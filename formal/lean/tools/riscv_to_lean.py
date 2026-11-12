#!/usr/bin/env python3
"""Translate a function of a shipped RV64 object into a Lean program for Hashtree.Asm.Riscv.

    riscv_to_lean.py <object.o> <symbol> <LeanNamespace> > Program.lean

The instruction stream is the object's own disassembly
(`riscv64-linux-gnu-objdump -d -r -M no-aliases`), restricted to the symbol's extent
[value, value + size) from the symbol table (so alignment padding before the function and after
its end -- e.g. the zero halfword objdump shows as `c.unimp` -- is not part of the program).
Every disassembled instruction becomes exactly one `Instr`; compressed (`c.*`) forms become their
base-instruction expansion and their indices are listed in `compressed`.

Relocations (from `readelf -rW`, which gives the symbol values):
* `R_RISCV_PCREL_HI20` / `R_RISCV_GOT_HI20` / `R_RISCV_CALL_PLT` on an `auipc` give its link-time
  target: `.rodata + off`, a GOT slot (whose content is listed in `got`), or a named symbol.  The
  `%pcrel_lo` partner (`R_RISCV_PCREL_LO12_I/S` naming the auipc's label; for CALL_PLT the next
  `jalr`) must use the auipc's register as base with immediate 0, and the auipc's result must be
  dead after the partner (checked on the straight-line code) -- then `auipc = target`, `lo = 0`
  is exactly what the linked code computes.
* `R_RISCV_JAL` / `BRANCH` / `RVC_*` to labels inside the function -> instruction indices.
* `R_RISCV_RELAX` / `R_RISCV_ALIGN` do not change semantics and are ignored.
Anything else is rejected (the script exits with an error): unsupported forms are never guessed.
The translator only parses syntax; every semantic decision lives in Riscv.lean.
"""
import re
import subprocess
import sys

OBJDUMP = 'riscv64-linux-gnu-objdump'
READELF = 'riscv64-linux-gnu-readelf'

ABI = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1'] + ['a%d' % i for i in range(8)] + \
      ['s%d' % i for i in range(2, 12)] + ['t3', 't4', 't5', 't6']


class Fail(Exception):
    pass


def reg(name):
    if name == 'fp':
        return 8
    if name in ABI:
        return ABI.index(name)
    m = re.fullmatch(r'x(\d+)', name)
    if m and int(m.group(1)) < 32:
        return int(m.group(1))
    raise Fail('not a register: ' + name)


def num(s):
    return int(s, 0)


def memop(s):
    m = re.fullmatch(r'(-?(?:0x[0-9a-f]+|\d+))\((\w+)\)', s)
    if not m:
        raise Fail('memory operand ' + s)
    return num(m.group(1)), reg(m.group(2))


def run(args):
    return subprocess.run(args, capture_output=True, text=True, check=True).stdout


def section_bytes(obj, name):
    out = subprocess.run([OBJDUMP, '-s', '-j', name, obj], capture_output=True, text=True).stdout
    data = bytearray()
    for ln in out.splitlines():
        m = re.match(r'^ ([0-9a-f]+) ((?:[0-9a-f]{2,8} ?)+)', ln)
        if m:
            data += bytes.fromhex(m.group(2).replace(' ', ''))
    return bytes(data)


def sections(obj):
    secs = {}
    for ln in run([READELF, '-SW', obj]).splitlines():
        m = re.match(r'^\s*\[\s*(\d+)\]\s+(\S+)\s+\S+\s+[0-9a-f]+\s+[0-9a-f]+\s+([0-9a-f]+)', ln)
        if m:
            secs[int(m.group(1))] = (m.group(2), int(m.group(3), 16))
    return secs


def symbols(obj, secs):
    """name -> (value, size, section name or None, bind); local `.L0` labels are not unique."""
    syms = {}
    for ln in run([READELF, '-sW', obj]).splitlines():
        m = re.match(r'^\s*\d+:\s+([0-9a-f]+)\s+(\d+)\s+(\w+)\s+(\w+)\s+\w+\s+(\w+)\s*(\S*)$', ln.rstrip())
        if not m or not m.group(6):
            continue
        ndx = m.group(5)
        sec = secs[int(ndx)][0] if ndx.isdigit() else None
        syms.setdefault(m.group(6), (int(m.group(1), 16), int(m.group(2)), sec, m.group(4)))
    return syms


def relocs(obj, secname):
    """offset -> list of (type, symvalue, symname, addend) for section `secname`."""
    out = run([READELF, '-rW', obj])
    rel = {}
    cur = None
    for ln in out.splitlines():
        m = re.match(r"^Relocation section '\.rela(\S+)'", ln)
        if m:
            cur = m.group(1)
            continue
        f = ln.split()
        if cur != secname or len(f) < 3 or not f[2].startswith('R_RISCV_') or not re.fullmatch(r'[0-9a-f]+', f[0]):
            continue
        val, name, add = 0, '', 0
        if len(f) >= 7 and f[5] in '+-':
            val, name, add = int(f[3], 16), f[4], int(f[6], 16) * (1 if f[5] == '+' else -1)
        rel.setdefault(int(f[0], 16), []).append((f[2], val, name, add))
    return rel


# --- operand roles for the dead-register check -------------------------------------------------

STORES = {'sw', 'sd', 'sb', 'sh', 'c.sw', 'c.sd', 'c.swsp', 'c.sdsp'}
BRANCHES = {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'c.beqz', 'c.bnez'}
JUMPS = {'jal', 'jalr', 'c.j', 'c.jr', 'c.jalr'}
TWO_ADDR = {'c.add', 'c.addw', 'c.and', 'c.or', 'c.xor', 'c.sub', 'c.subw', 'c.slli', 'c.srli', 'c.srai',
            'c.andi', 'c.addi', 'c.addiw', 'c.addi16sp'}


def regs_of(ops):
    rs = []
    for o in ops:
        m = re.fullmatch(r'-?(?:0x[0-9a-f]+|\d+)\((\w+)\)', o)
        if m:
            rs.append(reg(m.group(1)))
            continue
        try:
            rs.append(reg(o))
        except Fail:
            pass
    return rs


def reads_writes(mn, ops):
    rs = regs_of(ops)
    if mn in STORES or mn in BRANCHES or mn == 'c.jr':
        return set(rs), set()
    if not rs:
        return set(), set()
    if mn in TWO_ADDR:
        return set(rs), {rs[0]}
    return set(rs[1:]), {rs[0]}


# --- instruction translation ------------------------------------------------------------------

BOPS = {'and': 'and', 'or': 'or', 'xor': 'xor'}
WOPS = {'slliw', 'srliw', 'sraiw', 'roriw'}
SHA = {'sha256sum0': 'sum0', 'sha256sum1': 'sum1', 'sha256sig0': 'sig0', 'sha256sig1': 'sig1'}


def target_lean(t):
    kind = t[0]
    if kind == 'ro':
        return '(.ro (%d))' % t[1]
    if kind == 'got':
        return '(.got %d)' % t[1]
    return '(.sym "%s" (%d))' % (t[1], t[2])


def translate(mn, ops, ctx):
    """One instruction -> Lean term. `ctx`: branch target index / auipc target, if any."""
    i = lambda k: reg(ops[k])
    if mn == 'addi':
        if ops == ['zero', 'zero', '0']:
            return '.nop'
        return '.addi %d %d (%d)' % (i(0), i(1), num(ops[2]))
    if mn == 'c.addi':
        if ops == ['zero', '0']:
            return '.nop'
        return '.addi %d %d (%d)' % (i(0), i(0), num(ops[1]))
    if mn == 'c.addi16sp':
        assert ops[0] == 'sp'
        return '.addi 2 2 (%d)' % num(ops[1])
    if mn == 'c.addi4spn':
        assert ops[1] == 'sp'
        return '.addi %d 2 (%d)' % (i(0), num(ops[2]))
    if mn == 'c.li':
        return '.addi %d 0 (%d)' % (i(0), num(ops[1]))
    if mn == 'c.mv':
        return '.add %d 0 %d' % (i(0), i(1))
    if mn == 'add':
        return '.add %d %d %d' % (i(0), i(1), i(2))
    if mn == 'c.add':
        return '.add %d %d %d' % (i(0), i(0), i(1))
    if mn in ('lui', 'c.lui'):
        return '.lui %d %d' % (i(0), num(ops[1]) % (1 << 20))
    if mn in BOPS:
        return '.bop .%s %d %d %d' % (BOPS[mn], i(0), i(1), i(2))
    if mn in ('c.and', 'c.or', 'c.xor'):
        return '.bop .%s %d %d %d' % (mn[2:], i(0), i(0), i(1))
    if mn in ('andi', 'ori', 'xori'):
        return '.bopi .%s %d %d (%d)' % (mn[:-1], i(0), i(1), num(ops[2]))
    if mn == 'c.andi':
        return '.bopi .and %d %d (%d)' % (i(0), i(0), num(ops[1]))
    if mn == 'slli':
        return '.slli %d %d %d' % (i(0), i(1), num(ops[2]))
    if mn == 'c.slli':
        return '.slli %d %d %d' % (i(0), i(0), num(ops[1]))
    if mn == 'srai':
        return '.srai %d %d %d' % (i(0), i(1), num(ops[2]))
    if mn == 'c.srai':
        return '.srai %d %d %d' % (i(0), i(0), num(ops[1]))
    if mn in WOPS:
        return '.wop .%s %d %d %d' % (mn, i(0), i(1), num(ops[2]))
    if mn == 'addw':
        return '.addw %d %d %d' % (i(0), i(1), i(2))
    if mn == 'c.addw':
        return '.addw %d %d %d' % (i(0), i(0), i(1))
    if mn == 'rev8':
        return '.rev8 %d %d' % (i(0), i(1))
    if mn in SHA:
        return '.sha .%s %d %d' % (SHA[mn], i(0), i(1))
    if mn in ('lwu', 'ld', 'c.ld', 'c.ldsp'):
        off, b = memop(ops[1])
        return '.%s %d %d (%d)' % ('lwu' if mn == 'lwu' else 'ld', i(0), b, off)
    if mn in ('sw', 'c.sw', 'c.swsp', 'sd', 'c.sd', 'c.sdsp'):
        off, b = memop(ops[1])
        return '.%s %d %d (%d)' % ('sw' if 'sw' in mn else 'sd', i(0), b, off)
    if mn in ('beq', 'bne'):
        return '.br .%s %d %d %d' % ('eq' if mn == 'beq' else 'ne', i(0), i(1), ctx)
    if mn in ('c.beqz', 'c.bnez'):
        return '.br .%s %d 0 %d' % ('eq' if mn == 'c.beqz' else 'ne', i(0), ctx)
    if mn == 'jal':
        return '.jal %d %d' % (i(0), ctx)
    if mn == 'c.j':
        return '.jal 0 %d' % ctx
    if mn == 'jalr':
        off, b = memop(ops[1])
        return '.jalr %d %d (%d)' % (i(0), b, off)
    if mn == 'c.jr':
        return '.jalr 0 %d 0' % i(0)
    if mn == 'c.jalr':
        return '.jalr 1 %d 0' % i(0)
    if mn == 'auipc':
        if ctx is None:
            raise Fail('auipc without relocation')
        return '.auipc %d %s' % (i(0), target_lean(ctx))
    if mn == 'c.unimp':
        return '.unimp'
    raise Fail('unsupported: %s %s' % (mn, ','.join(ops)))


def main():
    obj, sym, ns = sys.argv[1], sys.argv[2], sys.argv[3]
    secs = sections(obj)
    syms = symbols(obj, secs)
    if sym not in syms or syms[sym][2] != '.text':
        raise SystemExit('symbol %s not in .text' % sym)
    start, size = syms[sym][0], syms[sym][1]
    end = start + size
    rel = relocs(obj, '.text')
    dis = run([OBJDUMP, '-d', '-M', 'no-aliases', '--no-show-raw-insn', '-j', '.text', obj])
    raw = run([OBJDUMP, '-d', '-M', 'no-aliases', '-j', '.text', obj])
    enc_len = {}
    for ln in raw.splitlines():
        m = re.match(r'^\s+([0-9a-f]+):\t([0-9a-f]+)\s', ln)
        if m:
            enc_len[int(m.group(1), 16)] = len(m.group(2)) // 2
    insns = []   # (addr, mnemonic, ops, text)
    for ln in dis.splitlines():
        m = re.match(r'^\s+([0-9a-f]+):\t(\S+)\s*(.*)$', ln)
        if not m:
            continue
        a = int(m.group(1), 16)
        if not (start <= a < end):
            continue
        mn = m.group(2)
        opstr = m.group(3).split('#')[0].strip()
        if mn in BRANCHES or mn in ('jal', 'c.j'):
            opstr = re.sub(r'\s*<[^>]*>', '', opstr)
        ops = [o.strip() for o in opstr.split(',')] if opstr else []
        insns.append((a, mn, ops, (mn + ' ' + m.group(3)).strip()))
    if not insns:
        raise SystemExit('no instructions in %s' % sym)
    # the function must be exactly covered
    pos = start
    for a, mn, _, _ in insns:
        if a != pos:
            raise SystemExit('gap in disassembly at %x' % pos)
        pos += enc_len[a]
    if pos != end:
        raise SystemExit('disassembly ends at %x, symbol at %x' % (pos, end))
    index = {a: k for k, (a, _, _, _) in enumerate(insns)}

    got_slots = []    # list of targets (tuples)

    def sym_target(name, value, add):
        info = syms.get(name)
        sec = info[2] if info else None
        if sec == '.rodata':
            return ('ro', value + add)
        if info and info[3] == 'LOCAL' and sec is not None and sec != '.text':
            # a local data label: the section is the object
            return ('sym', sec, value + add)
        if info and info[3] == 'LOCAL' and sec == '.text':
            return ('sym', name, add)   # a local function (named by its symbol)
        return ('sym', name, add)

    ctxs = [None] * len(insns)
    partner = {}     # partner index -> auipc index
    for k, (a, mn, ops, text) in enumerate(insns):
        rs = rel.get(a, [])
        kinds = [r[0] for r in rs if r[0] not in ('R_RISCV_RELAX', 'R_RISCV_ALIGN')]
        if mn in BRANCHES or mn in ('jal', 'c.j'):
            t = num('0x' + ops[-1]) if not ops[-1].startswith('0x') else num(ops[-1])
            for r in rs:
                if r[0] in ('R_RISCV_JAL', 'R_RISCV_BRANCH', 'R_RISCV_RVC_BRANCH', 'R_RISCV_RVC_JUMP'):
                    info = syms.get(r[2])
                    if info is None and not r[2].startswith('.L'):
                        raise SystemExit('%x: jump to external %s' % (a, r[2]))
                    t = r[1] + r[3]
            if t not in index:
                raise SystemExit('%x: branch target %x outside %s' % (a, t, sym))
            ctxs[k] = index[t]
            continue
        if mn == 'auipc':
            hi = [r for r in rs if r[0] in ('R_RISCV_PCREL_HI20', 'R_RISCV_GOT_HI20', 'R_RISCV_CALL_PLT', 'R_RISCV_CALL')]
            if len(hi) != 1:
                raise SystemExit('%x: auipc relocation %s' % (a, kinds))
            kind, value, name, add = hi[0]
            if num(ops[1]) != 0:
                raise SystemExit('%x: auipc immediate not 0' % a)
            if kind == 'R_RISCV_GOT_HI20':
                t = sym_target(name, value, add)
                if t not in got_slots:
                    got_slots.append(t)
                ctxs[k] = ('got', got_slots.index(t))
            else:
                ctxs[k] = sym_target(name, value, add)
            rd = reg(ops[0])
            # find the partner
            if kind in ('R_RISCV_CALL_PLT', 'R_RISCV_CALL'):
                p = k + 1
                if p >= len(insns) or insns[p][1] != 'jalr' or memop(insns[p][2][1]) != (0, rd):
                    raise SystemExit('%x: call without jalr partner' % a)
            else:
                cands = [q for q, (b, _, _, _) in enumerate(insns)
                         if any(r[0] in ('R_RISCV_PCREL_LO12_I', 'R_RISCV_PCREL_LO12_S') and r[1] == a
                                for r in rel.get(b, []))]
                if len(cands) != 1:
                    raise SystemExit('%x: auipc has %d lo12 partners' % (a, len(cands)))
                p = cands[0]
                pmn, pops = insns[p][1], insns[p][2]
                if pmn in ('ld', 'lwu', 'sd', 'sw'):
                    off, b = memop(pops[1])
                elif pmn == 'addi':
                    off, b = num(pops[2]), reg(pops[1])
                else:
                    raise SystemExit('%x: lo12 partner %s' % (a, pmn))
                if off != 0 or b != rd:
                    raise SystemExit('%x: lo12 partner operands' % a)
            # straight line auipc .. partner .. redefinition of rd: rd read only by the partner
            if p < k:
                raise SystemExit('%x: partner before auipc' % a)
            ok = False
            for q in range(k + 1, len(insns)):
                qmn, qops = insns[q][1], insns[q][2]
                r_, w_ = reads_writes(qmn, qops)
                if rd in r_ and q != p:
                    raise SystemExit('%x: auipc result used outside its partner at %x' % (a, insns[q][0]))
                if q > p and rd in w_:
                    ok = True
                    break
                if q == p and rd in w_:
                    ok = True
                    break
                if qmn in BRANCHES or qmn in JUMPS:
                    break
            if not ok:
                raise SystemExit('%x: cannot show auipc result dead after its partner' % a)
            partner[p] = k
            continue
        for r in rs:
            if r[0] in ('R_RISCV_PCREL_LO12_I', 'R_RISCV_PCREL_LO12_S'):
                if r[1] not in index or insns[index[r[1]]][1] != 'auipc':
                    raise SystemExit('%x: lo12 without auipc' % a)
            elif r[0] not in ('R_RISCV_RELAX', 'R_RISCV_ALIGN'):
                raise SystemExit('%x: unsupported relocation %s' % (a, r[0]))
    out = []
    for k, (a, mn, ops, text) in enumerate(insns):
        try:
            out.append((a, text, translate(mn, ops, ctxs[k])))
        except (Fail, IndexError, AssertionError) as e:
            raise SystemExit('%x: %s: %s' % (a, text, e))
    compressed = [k for k, (a, _, _, _) in enumerate(insns) if enc_len[a] == 2]
    rodata = section_bytes(obj, '.rodata') if any(s[0] == '.rodata' for s in secs.values()) else b''
    # pointer-valued words of writable data sections (R_RISCV_64 relocations)
    datarel = []
    for sname in ('.data.rel.local', '.data.rel', '.data'):
        for off, rs in sorted(relocs(obj, sname).items()):
            for r in rs:
                if r[0] != 'R_RISCV_64':
                    raise SystemExit('%s+%x: relocation %s' % (sname, off, r[0]))
                datarel.append((sname, off, sym_target(r[2], r[1], r[3])))
    print('import Hashtree.Asm.Riscv\n')
    print('/-! Generated by tools/riscv_to_lean.py from the shipped object (symbol `%s`). -/\n' % sym)
    print('namespace %s' % ns)
    print('open Hashtree.Asm Hashtree.Asm.Riscv\n')
    print('set_option maxRecDepth 100000 in')
    print('/-- The instructions of `%s`, in address order. -/' % sym)
    print('def prog : Array Instr := #[')
    for k, (addr, text, term) in enumerate(out):
        sep = ',' if k + 1 < len(out) else ''
        print('  %s%s  -- %d @%x: %s' % (term, sep, k, addr, text))
    print(']\n')
    print('set_option maxRecDepth 100000 in')
    print('/-- Indices of the instructions with a 16-bit (C extension) encoding. -/')
    print('def compressed : List Nat := [%s]\n' % ', '.join(str(c) for c in compressed))
    print('/-- Contents of the GOT slots the program uses (each an 8-byte pointer). -/')
    print('def got : List Target := [%s]\n' % ', '.join(target_lean(t) for t in got_slots))
    print('/-- Pointer words of the object\'s writable data sections: (section, offset, target). -/')
    print('def datarel : List (String × Int × Target) := [%s]\n' %
          ', '.join('("%s", %d, %s)' % (s, o, target_lean(t)) for s, o, t in datarel))
    print('set_option maxRecDepth 100000 in')
    print('/-- `.rodata` bytes. -/')
    print('def rodata : List Nat := [%s]\n' % ', '.join(str(b) for b in rodata))
    print('end %s' % ns)


if __name__ == '__main__':
    main()
