#!/usr/bin/env python3
"""Translate a shipped AArch64 kernel object into a Lean program for Hashtree.Asm.Arm.

    arm_to_lean.py [--llvm] <kernel.o> <symbol> <LeanNamespace> > Program.lean

The instruction stream is the object's own disassembly, so the assembler's macro expansion is
what is verified, not a re-implementation:

* Linux ELF objects: `aarch64-linux-gnu-objdump -d -r --no-show-raw-insn` (GNU syntax; `--llvm`
  uses `llvm-objdump --triple=aarch64-linux-gnu` instead, as a cross-check of the parser);
* macOS Mach-O objects: `llvm-objdump --triple=aarch64-linux-gnu -d -r` (the triple selects the
  generic assembler syntax instead of Apple's `ld1.4s { v0, v1 }` variant).

The function is the address range from its global symbol to the next global symbol (Mach-O
local labels such as `.Lshani_loop` do not split it).  `adrp`/`add` pairs relocated against the
read-only section (ELF `R_AARCH64_ADR_PREL_PG_HI21` / `R_AARCH64_ADD_ABS_LO12_NC` against
`.rodata+k`; Mach-O `ARM64_RELOC_PAGE21` / `ARM64_RELOC_PAGEOFF12` against a local symbol of
`__const`) become `.adrp d k` / `.addLo12 d n k` with `k` the offset into that section (whose
bytes are emitted as `rodata`); branches inside the function become instruction indices; a
branch relocated against another symbol (`R_AARCH64_JUMP26`, `ARM64_RELOC_BRANCH26`) becomes a
tail call.  The translator only parses syntax; every semantic decision lives in Arm.lean.  Any
form it does not know is a hard error.
"""
import re
import subprocess
import sys


class Fail(Exception):
    pass


def num(s):
    s = s.strip()
    if s.startswith('#'):
        s = s[1:]
    return int(s, 0)


def gpr(tok):
    """x0..x30 / w0..w30 / sp -> (index, width).  Index 31 = SP; the zero register is refused."""
    tok = tok.strip()
    if tok == 'sp':
        return 31, 64
    if tok == 'wsp':
        return 31, 32
    m = re.fullmatch(r'([xw])(\d+)', tok)
    if m and int(m.group(2)) <= 30:
        return int(m.group(2)), 64 if m.group(1) == 'x' else 32
    if tok in ('xzr', 'wzr'):
        raise Fail('zero register not modelled')
    return None


def xreg(tok):
    g = gpr(tok)
    if not g or g[1] != 64:
        raise Fail('expected x register: ' + tok)
    return g[0]


def xreg_nosp(tok):
    r = xreg(tok)
    if r == 31:
        raise Fail('sp not allowed here: ' + tok)
    return r


def wreg(tok):
    g = gpr(tok)
    if not g or g[1] != 32 or g[0] == 31:
        raise Fail('expected w register: ' + tok)
    return g[0]


def vreg(tok, arr):
    """`v3.4s` with the given arrangement -> 3."""
    m = re.fullmatch(r'v(\d+)\.(\w+)', tok.strip())
    if not m or m.group(2) != arr:
        raise Fail('expected v.%s: %s' % (arr, tok))
    return int(m.group(1))


def fpreg(tok):
    """q3 / d3 / s3 -> (kind, 3)."""
    m = re.fullmatch(r'([qdsbh])(\d+)', tok.strip())
    if not m:
        return None
    return m.group(1), int(m.group(2))


def reglist(tok):
    """`{v0.4s-v3.4s}` or `{ v0.4s, v1.4s, v2.4s, v3.4s }` (optionally `[i]`) ->
    (first, count, arrangement, index)."""
    m = re.fullmatch(r'\{([^}]*)\}(?:\[(\d+)\])?', tok.strip())
    if not m:
        raise Fail('register list ' + tok)
    inner = m.group(1).strip()
    idx = int(m.group(2)) if m.group(2) is not None else None
    regs = []
    if '-' in inner:
        a, b = inner.split('-')
        ma = re.fullmatch(r'v(\d+)\.(\w+)', a.strip())
        mb = re.fullmatch(r'v(\d+)\.(\w+)', b.strip())
        if not ma or not mb or ma.group(2) != mb.group(2):
            raise Fail('register list ' + tok)
        first, last = int(ma.group(1)), int(mb.group(1))
        cnt = (last - first) % 32 + 1
        return first, cnt, ma.group(2), idx
    for r in inner.split(','):
        mr = re.fullmatch(r'v(\d+)\.(\w+)', r.strip())
        if not mr:
            raise Fail('register list ' + tok)
        regs.append((int(mr.group(1)), mr.group(2)))
    first = regs[0][0]
    for k, (r, a) in enumerate(regs):
        if r != (first + k) % 32 or a != regs[0][1]:
            raise Fail('register list not consecutive ' + tok)
    return first, len(regs), regs[0][1], idx


def addressing(ops):
    """Memory operand (+ optional post-index operand) -> (base, Lean Idx)."""
    m = re.fullmatch(r'\[([^\],]+)(?:,\s*(#?-?(?:0x[0-9a-f]+|\d+)))?\](!?)', ops[0].strip())
    if not m:
        raise Fail('memory operand ' + ops[0])
    base = xreg(m.group(1))
    off = num(m.group(2)) if m.group(2) else 0
    pre = m.group(3) == '!'
    rest = ops[1:]
    if pre:
        if rest:
            raise Fail('pre-index with post operand')
        return base, '(.pre (%d))' % off
    if rest:
        if len(rest) != 1 or m.group(2):
            raise Fail('addressing ' + ', '.join(ops))
        p = rest[0].strip()
        if p.startswith('#') or re.fullmatch(r'-?(0x[0-9a-f]+|\d+)', p):
            return base, '(.post (%d))' % num(p)
        return base, '(.postR %d)' % xreg_nosp(p)
    return base, '(.off (%d))' % off


SIZES = {'w': '.w', 'x': '.x', 'd': '.d', 'q': '.q'}


def ldst_reg(tok):
    """Transfer register of ldr/str/ldp/stp -> (Lean size, index)."""
    g = gpr(tok)
    if g:
        if g[0] == 31:
            raise Fail('sp as transfer register')
        return ('.x' if g[1] == 64 else '.w'), g[0]
    f = fpreg(tok)
    if f and f[0] in ('d', 'q'):
        return SIZES[f[0]], f[1]
    raise Fail('transfer register ' + tok)


CCS = {'eq': 'eq', 'ne': 'ne', 'hs': 'hs', 'cs': 'hs', 'lo': 'lo', 'cc': 'lo', 'hi': 'hi', 'ls': 'ls',
       'ge': 'ge', 'lt': 'lt', 'gt': 'gt', 'le': 'le'}
LOGIC16 = {'eor': 'eor', 'orr': 'orr', 'and': 'and', 'bic': 'bic'}
WOPS = {'add': 'add', 'eor': 'eor', 'and': 'and', 'orr': 'orr', 'bic': 'bic'}


def is_imm(tok):
    return re.fullmatch(r'#-?(0x[0-9a-f]+|\d+)', tok.strip()) is not None


def translate(mn, ops, rel, target_index, ext_target):
    """One instruction -> Lean term.  `rel`: ('page'|'lo12', offset) or None."""
    if mn == 'nop':
        return '.nop'
    # ---- branches
    if mn.startswith('b.'):
        cc = CCS.get(mn[2:])
        if cc is None:
            raise Fail('condition ' + mn)
        if ext_target:
            raise Fail('conditional branch to another symbol')
        return '.bcc .%s %d' % (cc, target_index)
    if mn == 'b':
        if ext_target:
            return '.bTail "%s"' % ext_target
        return '.b %d' % target_index
    if mn == 'ret':
        if ops and ops[0] != 'x30':
            raise Fail('ret to a register other than x30')
        return '.ret'
    # ---- relocated address formation
    if mn == 'adrp':
        if not rel or rel[0] != 'page':
            raise Fail('adrp without page relocation')
        return '.adrp %d (%d)' % (xreg_nosp(ops[0]), rel[1])
    if rel:
        if mn == 'add' and rel[0] == 'lo12' and len(ops) == 3 and num(ops[2]) == 0:
            return '.addLo12 %d %d (%d)' % (xreg(ops[0]), xreg(ops[1]), rel[1])
        raise Fail('relocation on %s' % mn)
    # ---- SHA-256
    if mn in ('sha256h', 'sha256h2'):
        fd, fn = fpreg(ops[0]), fpreg(ops[1])
        if not fd or not fn or fd[0] != 'q' or fn[0] != 'q':
            raise Fail('sha256h operands')
        return '.%s %d %d %d' % (mn, fd[1], fn[1], vreg(ops[2], '4s'))
    if mn == 'sha256su0':
        return '.sha256su0 %d %d' % (vreg(ops[0], '4s'), vreg(ops[1], '4s'))
    if mn == 'sha256su1':
        return '.sha256su1 %d %d %d' % (vreg(ops[0], '4s'), vreg(ops[1], '4s'), vreg(ops[2], '4s'))
    # ---- vector data processing
    if ops and ops[0].startswith('v'):
        if mn == 'add':
            return '.vop .add %d %d %d' % (vreg(ops[0], '4s'), vreg(ops[1], '4s'), vreg(ops[2], '4s'))
        if mn in LOGIC16:
            return '.vop .%s %d %d %d' % (LOGIC16[mn], vreg(ops[0], '16b'), vreg(ops[1], '16b'), vreg(ops[2], '16b'))
        if mn == 'mov' and len(ops) == 2:
            d, n = vreg(ops[0], '16b'), vreg(ops[1], '16b')
            return '.vop .orr %d %d %d' % (d, n, n)          # MOV (vector) = ORR Vd, Vn, Vn
        if mn == 'movi':
            d = vreg(ops[0], '4s')
            imm = num(ops[1])
            sh = 0
            if len(ops) == 3:
                ms = re.fullmatch(r'lsl\s+#(\d+)', ops[2].strip())
                if not ms:
                    raise Fail('movi shift')
                sh = int(ms.group(1))
            if not (0 <= imm < 256 and sh in (0, 8, 16, 24)) or len(ops) > 3:
                raise Fail('movi form')
            return '.movi %d %d' % (d, imm << sh)
        if mn in ('shl', 'ushr'):
            for arr, esz in (('4s', 32), ('2d', 64)):
                if ops[0].endswith('.' + arr):
                    k = num(ops[2])
                    if mn == 'shl' and not 0 <= k < esz or mn == 'ushr' and not 1 <= k <= esz:
                        raise Fail('shift amount')
                    return '.%s %d %d %d %d' % (mn, esz, vreg(ops[0], arr), vreg(ops[1], arr), k)
            raise Fail('shift arrangement')
        if mn == 'ext':
            imm = num(ops[3])
            if not 0 <= imm < 16:
                raise Fail('ext index')
            return '.ext %d %d %d %d' % (vreg(ops[0], '16b'), vreg(ops[1], '16b'), vreg(ops[2], '16b'), imm)
        if mn in ('zip1', 'zip2', 'uzp1'):
            return '.%s %d %d %d' % (mn, vreg(ops[0], '4s'), vreg(ops[1], '4s'), vreg(ops[2], '4s'))
        if mn == 'xtn':
            return '.xtn %d %d' % (vreg(ops[0], '2s'), vreg(ops[1], '2d'))
        if mn == 'rev32':
            return '.rev32 %d %d' % (vreg(ops[0], '16b'), vreg(ops[1], '16b'))
        raise Fail('vector form')
    # ---- structure loads / stores
    if mn in ('ld1', 'st1', 'ld4', 'st4'):
        first, cnt, arr, idx = reglist(ops[0])
        base, mode = addressing(ops[1:])
        if mn in ('ld1', 'st1'):
            if arr != '4s' or idx is not None or not 1 <= cnt <= 4:
                raise Fail('ld1/st1 form')
            if mode.startswith('(.post ') and num(mode[7:-1].strip('()')) != 16 * cnt:
                raise Fail('ld1/st1 post-index immediate')
            return '.%s %d %d %d %s' % (mn, first, cnt, base, mode)
        if arr != 's' or idx is None or cnt != 4 or not 0 <= idx < 4:
            raise Fail('ld4/st4 form (only single structure .s[i])')
        if mode.startswith('(.post ') and num(mode[7:-1].strip('()')) != 16:
            raise Fail('ld4/st4 post-index immediate')
        if mode.startswith('(.pre ') or mode.startswith('(.off (') and mode != '(.off (0))':
            raise Fail('ld4/st4 addressing')
        return '.%ss %d %d %d %s' % (mn, first, idx, base, mode)
    if mn in ('ldr', 'str'):
        sz, t = ldst_reg(ops[0])
        base, mode = addressing(ops[1:])
        return '.%s %s %d %d %s' % (mn, sz, t, base, mode)
    if mn in ('ldp', 'stp'):
        sz1, t1 = ldst_reg(ops[0])
        sz2, t2 = ldst_reg(ops[1])
        if sz1 != sz2:
            raise Fail('ldp/stp sizes')
        base, mode = addressing(ops[2:])
        return '.%s %s %d %d %d %s' % (mn, sz1, t1, t2, base, mode)
    # ---- general registers
    if mn == 'mov':
        if len(ops) == 2 and is_imm(ops[1]):
            v = num(ops[1])
            if not -(1 << 63) <= v < (1 << 64):
                raise Fail('mov immediate')
            if v >= 1 << 63:      # GNU prints MOVN results unsigned: the 64-bit value, as signed
                v -= 1 << 64
            return '.movz %d (%d)' % (xreg_nosp(ops[0]), v)
        raise Fail('mov form')
    if mn in ('add', 'sub') and len(ops) == 3 and is_imm(ops[2]):
        d, n = xreg(ops[0]), xreg(ops[1])
        imm = num(ops[2])
        if not 0 <= imm < 4096:
            raise Fail('add/sub immediate')
        return '.%si %d %d %d' % (mn, d, n, imm)
    if mn in WOPS and len(ops) in (3, 4):
        g = gpr(ops[0])
        if g and g[1] == 64:
            if mn != 'add':
                raise Fail('64-bit data operation')
            d, n, m = xreg_nosp(ops[0]), xreg_nosp(ops[1]), xreg_nosp(ops[2])
            sh = 0
            if len(ops) == 4:
                ms = re.fullmatch(r'lsl\s+#(\d+)', ops[3].strip())
                if not ms:
                    raise Fail('add shift')
                sh = int(ms.group(1))
            return '.addr %d %d %d %d' % (d, n, m, sh)
        if len(ops) != 3:
            raise Fail('shifted w operation')
        return '.wop .%s %d %d %d' % (WOPS[mn], wreg(ops[0]), wreg(ops[1]), wreg(ops[2]))
    if mn == 'ror' and len(ops) == 3 and is_imm(ops[2]):
        k = num(ops[2])
        if not 0 <= k < 32:
            raise Fail('ror amount')
        return '.rorw %d %d %d' % (wreg(ops[0]), wreg(ops[1]), k)
    if mn == 'rev32':
        return '.rev32x %d %d' % (xreg_nosp(ops[0]), xreg_nosp(ops[1]))
    if mn == 'cmp':
        if is_imm(ops[1]):
            imm = num(ops[1])
            if len(ops) != 2 or not 0 <= imm < 4096:
                raise Fail('cmp immediate')
            return '.cmpi %d %d' % (xreg(ops[0]), imm)
        if len(ops) != 2:
            raise Fail('cmp form')
        return '.cmpr %d %d' % (xreg_nosp(ops[0]), xreg_nosp(ops[1]))
    raise Fail('unsupported: %s %s' % (mn, ', '.join(ops)))


def split_ops(s):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch in '[{':
            depth += 1
        if ch in ']}':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur.strip())
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def parse_insn(text):
    text = text.split('//')[0].strip()
    parts = text.split(None, 1)
    mn = parts[0]
    ops = split_ops(parts[1]) if len(parts) > 1 else []
    return mn, ops


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout


def sections(obj):
    """name -> (vma, size) via llvm-objdump -h."""
    out = {}
    for ln in run(['llvm-objdump', '-h', obj]).splitlines():
        m = re.match(r'^\s*\d+\s+(\S+)\s+([0-9a-f]+)\s+([0-9a-f]+)', ln)
        if m:
            out[m.group(1)] = (int(m.group(3), 16), int(m.group(2), 16))
    return out


def symbols(obj):
    """[(value, flags, section, name)] via llvm-objdump -t."""
    out = []
    for ln in run(['llvm-objdump', '-t', obj]).splitlines():
        m = re.match(r'^([0-9a-f]{16}) (.{7}) (\S+)\s+(?:[0-9a-f]{16}\s+)?(\S+)$', ln)
        if m:
            out.append((int(m.group(1), 16), m.group(2), m.group(3), m.group(4)))
    return out


def section_bytes(obj, name, vma):
    data = bytearray()
    for ln in run(['llvm-objdump', '-s', '--section=' + name, obj]).splitlines():
        m = re.match(r'^ ([0-9a-f]+) ((?:[0-9a-f]{2,8} ?)+)', ln)
        if m:
            addr = int(m.group(1), 16) - vma
            if addr != len(data):
                raise SystemExit('gap in section dump')
            data += bytes.fromhex(m.group(2).replace(' ', ''))
    return bytes(data)


def main():
    args = sys.argv[1:]
    use_llvm = False
    if args and args[0] == '--llvm':
        use_llvm = True
        args = args[1:]
    obj, sym, ns = args
    macho = open(obj, 'rb').read(4) == b'\xcf\xfa\xed\xfe'
    secs = sections(obj)
    text_name, ro_name = ('__text', '__const') if macho else ('.text', '.rodata')
    text_vma, text_size = secs[text_name]
    ro_vma, ro_size = secs.get(ro_name, (0, 0))
    for nm, (_, size) in secs.items():
        if nm in ('.data', '.bss', '__data', '__bss') and size:
            raise SystemExit('unexpected non-empty %s' % nm)
    syms = symbols(obj)
    text_sec = '__TEXT,__text' if macho else '.text'
    ro_sec = '__TEXT,__const' if macho else '.rodata'
    globs = sorted(v for (v, fl, sec, nm) in syms if sec == text_sec and fl[0] == 'g')
    start = [v for (v, fl, sec, nm) in syms if nm == sym and sec == text_sec]
    if len(start) != 1:
        raise SystemExit('symbol %s not found' % sym)
    start = start[0]
    end = min([g for g in globs if g > start] + [text_vma + text_size])
    # data in code (ELF mapping symbols) is refused
    for (v, fl, sec, nm) in syms:
        if sec == text_sec and nm.startswith('$d') and start <= v < end:
            raise SystemExit('data in code at %x' % v)
    ro_syms = {nm: v - ro_vma for (v, fl, sec, nm) in syms if sec == ro_sec}

    def ro_offset(target):
        m = re.fullmatch(r'([^+-]+)(?:([+-])(0x[0-9a-f]+|\d+))?', target)
        name, add = m.group(1), 0
        if m.group(3):
            add = int(m.group(3), 0) * (-1 if m.group(2) == '-' else 1)
        if name == ro_name:
            return add
        if name in ro_syms:
            return ro_syms[name] + add
        return None

    if macho or use_llvm:
        dis = run(['llvm-objdump', '--triple=aarch64-linux-gnu', '-d', '-r', '--no-show-raw-insn', obj])
    else:
        dis = run(['aarch64-linux-gnu-objdump', '-d', '-r', '--no-show-raw-insn', obj])
    insns = []     # [addr, text]
    relocs = {}    # addr -> (kind, target)
    for ln in dis.splitlines():
        m = re.match(r'^\s+([0-9a-f]+):\s+(R_AARCH64_\w+|ARM64_RELOC_\w+)\s+(\S+)\s*$', ln)
        if m:
            a = int(m.group(1), 16)
            if a in relocs:
                raise SystemExit('two relocations at %x' % a)
            relocs[a] = (m.group(2), m.group(3))
            continue
        m = re.match(r'^\s*([0-9a-f]+):\s+(\S.*)$', ln)
        if m:
            a = int(m.group(1), 16)
            if start <= a < end:
                insns.append([a, m.group(2).strip()])
    if not insns:
        raise SystemExit('no instructions for %s' % sym)
    for k, (a, _) in enumerate(insns):
        if a != start + 4 * k:
            raise SystemExit('instruction stream not contiguous at %x' % a)
    if len(insns) * 4 != end - start:
        raise SystemExit('instruction count does not match the function size')
    addr_index = {a: i for i, (a, _) in enumerate(insns)}
    out = []
    for i, (addr, text) in enumerate(insns):
        mn, ops = parse_insn(text)
        rel, ext, tgt = None, None, None
        if addr in relocs:
            kind, target = relocs.pop(addr)
            if kind in ('R_AARCH64_ADR_PREL_PG_HI21', 'ARM64_RELOC_PAGE21'):
                off = ro_offset(target)
                if off is None or not 0 <= off < ro_size:
                    raise SystemExit('%x: page relocation outside read-only data: %s' % (addr, target))
                rel = ('page', off)
            elif kind in ('R_AARCH64_ADD_ABS_LO12_NC', 'ARM64_RELOC_PAGEOFF12'):
                off = ro_offset(target)
                if off is None or not 0 <= off < ro_size:
                    raise SystemExit('%x: lo12 relocation outside read-only data: %s' % (addr, target))
                rel = ('lo12', off)
            elif kind in ('R_AARCH64_JUMP26', 'ARM64_RELOC_BRANCH26'):
                if mn != 'b':
                    raise SystemExit('%x: branch relocation on %s' % (addr, mn))
                ext = target
            else:
                raise SystemExit('%x: unsupported relocation %s' % (addr, kind))
        if mn == 'b' or mn.startswith('b.'):
            if not ext:
                t = int(ops[0].split()[0], 16)
                tgt = addr_index.get(t)
                if tgt is None:
                    raise SystemExit('%x: branch target %x outside %s' % (addr, t, sym))
        try:
            out.append((addr, text, translate(mn, ops, rel, tgt, ext)))
        except Fail as e:
            raise SystemExit('%x: %s: %s' % (addr, text, e))
    left = [a for a in relocs if start <= a < end]
    if left:
        raise SystemExit('unused relocations at %s' % left)
    rodata = section_bytes(obj, ro_name, ro_vma) if ro_size else b''
    if len(rodata) != ro_size:
        raise SystemExit('read-only section size mismatch')
    tool = 'llvm-objdump --triple=aarch64-linux-gnu' if (macho or use_llvm) else 'aarch64-linux-gnu-objdump'
    print('import Hashtree.Asm.Arm\n')
    print('/-! Generated by tools/arm_to_lean.py from the shipped object (symbol `%s`, %s, disassembled\n'
          'with `%s`). -/\n' % (sym, 'Mach-O' if macho else 'ELF', tool))
    print('namespace %s' % ns)
    print('open Hashtree.Asm Hashtree.Asm.Arm\n')
    print('set_option maxRecDepth 100000 in')
    print('/-- The instructions of `%s`, in address order. -/' % sym)
    print('def prog : Array Instr := #[')
    for k, (addr, text, term) in enumerate(out):
        sep = ',' if k + 1 < len(out) else ''
        print('  %s%s  -- %d @%x: %s' % (term, sep, k, addr, re.sub(r'\s+', ' ', text)))
    print(']\n')
    print('set_option maxRecDepth 100000 in')
    print('/-- `%s` bytes. -/' % ro_name)
    print('def rodata : List Nat := [%s]\n' % ', '.join(str(b) for b in rodata))
    print('end %s' % ns)


if __name__ == '__main__':
    main()
