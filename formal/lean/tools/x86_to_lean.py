#!/usr/bin/env python3
"""Translate a shipped x86-64 kernel object into a Lean program for Hashtree.Asm.X86.

    x86_to_lean.py <kernel.o> <symbol> <LeanNamespace> > Program.lean

The instruction stream is the object's own disassembly (`objdump -d -r -M intel`), so the
assembler's macro expansion is what is verified, not a re-implementation.  rip-relative operands
are resolved through their relocation records to offsets into `.rodata` (whose bytes are emitted
too); branches inside the function become instruction indices; jumps to other symbols become
tail calls.  Windows COFF objects are converted to ELF first (objcopy) — the code bytes are
unchanged.  The translator only parses syntax; every semantic decision lives in X86.lean.
"""
import re
import subprocess
import sys

GPR64 = ['rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi'] + ['r%d' % i for i in range(8, 16)]
GPR32 = ['eax', 'ecx', 'edx', 'ebx', 'esp', 'ebp', 'esi', 'edi'] + ['r%dd' % i for i in range(8, 16)]


def gpr(name):
    if name in GPR64:
        return GPR64.index(name), 64
    if name in GPR32:
        return GPR32.index(name), 32
    return None


def vreg(name):
    m = re.fullmatch(r'([xyz])mm(\d+)', name)
    if not m:
        return None
    return int(m.group(2)), {'x': 4, 'y': 8, 'z': 16}[m.group(1)]


def num(s):
    return int(s, 0)


class Fail(Exception):
    pass


def objdump(args, obj):
    return subprocess.run(['objdump'] + args + [obj], capture_output=True, text=True, check=True).stdout


def section_bytes(obj, name):
    out = subprocess.run(['objdump', '-s', '-j', name, obj], capture_output=True, text=True).stdout
    data = bytearray()
    for ln in out.splitlines():
        m = re.match(r'^ ([0-9a-f]+) ((?:[0-9a-f]{2,8} ?)+)', ln)
        if m:
            data += bytes.fromhex(m.group(2).replace(' ', ''))
    return bytes(data)


def parse_mem(txt, reloc_target):
    """`DWORD PTR [rcx+0x10]` etc. -> Lean MemRef literal."""
    m = re.search(r'\[(.*)\]', txt)
    if not m:
        raise Fail('mem ' + txt)
    inner = m.group(1).replace(' ', '')
    fields = {}
    if inner.startswith('rip'):
        if reloc_target is None:
            raise Fail('rip operand without relocation: ' + txt)
        return '{ ro := some %d }' % reloc_target
    parts = re.findall(r'[+-]?[^+-]+', inner)
    disp = 0
    for p in parts:
        sign = -1 if p.startswith('-') else 1
        p = p.lstrip('+-')
        if '*' in p:
            r, sc = p.split('*')
            fields['index'] = 'some %d' % gpr(r)[0]
            fields['scale'] = str(int(sc, 0))
        elif gpr(p):
            if 'base' in fields:
                fields['index'] = 'some %d' % gpr(p)[0]
                fields['scale'] = '1'
            else:
                fields['base'] = 'some %d' % gpr(p)[0]
        else:
            disp += sign * num(p)
    if disp:
        fields['disp'] = '(%d)' % disp
    return '{ ' + ', '.join('%s := %s' % kv for kv in fields.items()) + ' }' if fields else '{}'


def width_of_mem(txt):
    for k, w in [('ZMMWORD', 16), ('YMMWORD', 8), ('XMMWORD', 4), ('QWORD', 64), ('DWORD', 32)]:
        if k in txt:
            return w
    return None


def vsrc(op, rt):
    v = vreg(op)
    if v:
        return '(.reg %d)' % v[0]
    return '(.mem %s)' % parse_mem(op, rt)


def gsrc(op, rt):
    g = gpr(op)
    if g:
        return '(.reg %d)' % g[0]
    if re.fullmatch(r'-?0x[0-9a-f]+|-?\d+', op):
        v = num(op)
        if v >= 1 << 63:
            v -= 1 << 64
        return '(.imm (%d))' % v
    return '(.mem %s)' % parse_mem(op, rt)


VOPS = {'paddd': 'add', 'pxor': 'xor', 'pand': 'and', 'por': 'or'}
SHIFTS = {'pslld': 'shl', 'psrld': 'shr', 'psrad': 'sar'}
VMOVS = {'movdqa', 'movdqu', 'vmovdqa', 'vmovdqu', 'vmovups', 'vmovdqa32', 'vmovdqu32', 'vmovdqa64', 'movups'}
CCS = {'je': 'e', 'jne': 'ne', 'jl': 'l', 'jge': 'ge', 'jle': 'le', 'jg': 'g', 'jb': 'b', 'jae': 'ae',
       'jbe': 'be', 'ja': 'a'}


def translate(mn, ops, rt, target_index, ext_target):
    """One instruction -> Lean term."""
    if mn in ('nop', 'endbr64') or mn.startswith('data16') or mn.startswith('cs'):
        return '.nop'
    if mn == 'xchg' and len(ops) == 2 and ops[0] == ops[1]:
        return '.nop'   # `66 90` (xchg ax, ax): two-byte nop padding
    vex = mn.startswith('v')
    base = mn[1:] if vex and mn[1:] in VOPS or vex and mn[1:] in SHIFTS else mn
    if base in VOPS:
        if vex:
            d, w = vreg(ops[0]); s1 = vreg(ops[1])[0]
            return '.vop .%s true %d %d %d %s' % (VOPS[base], w, d, s1, vsrc(ops[2], rt))
        d, w = vreg(ops[0])
        return '.vop .%s false %d %d %d %s' % (VOPS[base], w, d, d, vsrc(ops[1], rt))
    if base in SHIFTS:
        if vex:
            d, w = vreg(ops[0])
            return '.vshift .%s true %d %d %d %d' % (SHIFTS[base], w, d, vreg(ops[1])[0], num(ops[2]))
        d, w = vreg(ops[0])
        return '.vshift .%s false %d %d %d %d' % (SHIFTS[base], w, d, d, num(ops[1]))
    if mn in ('psrlq', 'vpsrlq'):
        if vex:
            d, w = vreg(ops[0])
            return '.vshiftq true %d %d %d %d' % (w, d, vreg(ops[1])[0], num(ops[2]))
        d, w = vreg(ops[0])
        return '.vshiftq false %d %d %d %d' % (w, d, d, num(ops[1]))
    if mn == 'vprord':
        d, w = vreg(ops[0])
        return '.vror %d %d %d %d' % (w, d, vreg(ops[1])[0], num(ops[2]))
    if mn == 'vpternlogd':
        d, w = vreg(ops[0])
        return '.vtern %d %d %d %d %d' % (w, d, vreg(ops[1])[0], vreg(ops[2])[0], num(ops[3]))
    if mn in VMOVS:
        dv = vreg(ops[0])
        if dv:
            return '.vload %s %d %d %s' % ('true' if vex else 'false', dv[1], dv[0], vsrc(ops[1], rt))
        sv = vreg(ops[1])
        return '.vstore %d %s %d' % (sv[1], parse_mem(ops[0], rt), sv[0])
    if mn in ('pshufd', 'vpshufd'):
        if vex:
            return '.pshufd true %d %d %d' % (vreg(ops[0])[0], vreg(ops[1])[0], num(ops[2]))
        return '.pshufd false %d %d %d' % (vreg(ops[0])[0], vreg(ops[1])[0], num(ops[2]))
    if mn in ('pshufb', 'vpshufb'):
        d, w = vreg(ops[0])
        if vex:
            return '.pshufb true %d %d %d %d' % (w, d, vreg(ops[1])[0], vreg(ops[2])[0])
        return '.pshufb false %d %d %d %d' % (w, d, d, vreg(ops[1])[0])
    if mn in ('palignr', 'vpalignr'):
        if vex:
            return '.palignr true %d %d %d %d' % (vreg(ops[0])[0], vreg(ops[1])[0], vreg(ops[2])[0], num(ops[3]))
        d = vreg(ops[0])[0]
        return '.palignr false %d %d %d %d' % (d, d, vreg(ops[1])[0], num(ops[2]))
    if mn == 'pblendw':
        return '.pblendw %d %d %d' % (vreg(ops[0])[0], vreg(ops[1])[0], num(ops[2]))
    if mn == 'vshufps':
        d, w = vreg(ops[0])
        return '.shufps %d %d %d %d %d' % (w, d, vreg(ops[1])[0], vreg(ops[2])[0], num(ops[3]))
    if mn == 'vperm2f128':
        return '.perm2f128 %d %d %d %d' % (vreg(ops[0])[0], vreg(ops[1])[0], vreg(ops[2])[0], num(ops[3]))
    if mn == 'vinserti128':
        return '.inserti128 %d %d %s %d' % (vreg(ops[0])[0], vreg(ops[1])[0], parse_mem(ops[2], rt), num(ops[3]))
    if mn == 'vinserti64x4':
        return '.inserti64x4 %d %d %s %d' % (vreg(ops[0])[0], vreg(ops[1])[0], parse_mem(ops[2], rt), num(ops[3]))
    if mn in ('vpermi2d', 'vpermi2q'):
        return '.%s %d %d %d' % (mn[1:], vreg(ops[0])[0], vreg(ops[1])[0], vreg(ops[2])[0])
    if mn in ('sha256rnds2',):
        assert ops[2] == 'xmm0'
        return '.sha256rnds2 %d %d' % (vreg(ops[0])[0], vreg(ops[1])[0])
    if mn in ('sha256msg1', 'sha256msg2'):
        return '.%s %d %d' % (mn, vreg(ops[0])[0], vreg(ops[1])[0])
    # general registers
    if mn == 'mov':
        g = gpr(ops[0])
        if g:
            w = g[1]
            if w == 64 and ('DWORD' in ops[1]):
                raise Fail('mov r64, dword')
            return '.mov %d %d %s' % (w, g[0], gsrc(ops[1], rt))
        s = gpr(ops[1])
        return '.movst %d %s %d' % (s[1], parse_mem(ops[0], rt), s[0])
    if mn in ('add', 'xor', 'and', 'or'):
        g = gpr(ops[0])
        return '.alu .%s %d %d %s' % (mn, g[1], g[0], gsrc(ops[1], rt))
    if mn == 'sub':
        g = gpr(ops[0])
        return '.sub %d %d %s' % (g[1], g[0], gsrc(ops[1], rt))
    if mn == 'lea':
        return '.lea %d %s' % (gpr(ops[0])[0], parse_mem(ops[1], rt))
    if mn == 'ror':
        g = gpr(ops[0])
        return '.ror %d %d %d' % (g[1], g[0], num(ops[1]))
    if mn == 'shld':
        g = gpr(ops[0])
        return '.shld %d %d %d %d' % (g[1], g[0], gpr(ops[1])[0], num(ops[2]))
    if mn == 'shl':
        g = gpr(ops[0])
        return '.shl %d %d %d' % (g[1], g[0], num(ops[1]))
    if mn == 'bswap':
        g = gpr(ops[0])
        return '.bswap %d %d' % (g[1], g[0])
    if mn in ('push', 'pop'):
        return '.%s %d' % (mn, gpr(ops[0])[0])
    if mn == 'cmp':
        g = gpr(ops[0])
        return '.cmp %d %d %s' % (g[1], g[0], gsrc(ops[1], rt))
    if mn == 'test':
        g = gpr(ops[0])
        return '.test %d %d %d' % (g[1], g[0], gpr(ops[1])[0])
    if mn in CCS:
        if ext_target:
            return '.jccTail .%s "%s"' % (CCS[mn], ext_target)
        return '.jcc .%s %d' % (CCS[mn], target_index)
    if mn == 'jmp':
        if ext_target:
            return '.jmpTail "%s"' % ext_target
        return '.jmp %d' % target_index
    if mn == 'ret':
        return '.ret'
    raise Fail('unsupported: %s %s' % (mn, ','.join(ops)))


def split_ops(s):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch == '[':
            depth += 1
        if ch == ']':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur.strip()); cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def main():
    obj, sym, ns = sys.argv[1], sys.argv[2], sys.argv[3]
    coff = 'COFF' in subprocess.run(['file', obj], capture_output=True, text=True).stdout
    if coff:
        elf = '/tmp/x86_to_lean_%d.o' % abs(hash(obj))
        subprocess.run(['x86_64-w64-mingw32-objcopy', '-O', 'elf64-x86-64', obj, elf], check=True)
        obj = elf
    dis = objdump(['-d', '-r', '--no-show-raw-insn', '-M', 'intel'], obj)
    rodata = section_bytes(obj, '.rodata')
    insns = []   # [addr, text, reloc]
    cur = None
    for ln in dis.splitlines():
        m = re.match(r'^([0-9a-f]+) <([^>]+)>:$', ln)
        if m:
            cur = m.group(2)
            continue
        m = re.match(r'^\s+([0-9a-f]+):\s+(R_X86_64_\w+)\s+(\S+)$', ln)
        if m and insns:
            insns[-1][2] = (int(m.group(1), 16), m.group(2), m.group(3))
            continue
        m = re.match(r'^\s+([0-9a-f]+):\t(.*)$', ln)
        if m and cur == sym:
            insns.append([int(m.group(1), 16), m.group(2).split('#')[0].strip(), None])
    if not insns:
        raise SystemExit('symbol %s not found' % sym)
    addr_index = {a: i for i, (a, _, _) in enumerate(insns)}
    out = []
    for i, (addr, text, rel) in enumerate(insns):
        nxt = insns[i + 1][0] if i + 1 < len(insns) else addr + 16
        parts = text.split(None, 1)
        mn = parts[0]
        ops = split_ops(parts[1]) if len(parts) > 1 else []
        rt, ext, tgt = None, None, None
        if rel:
            p, kind, symadd = rel
            m = re.match(r'([^+-]+)([+-]0x[0-9a-f]+)?$', symadd)
            s0, add = m.group(1), int(m.group(2) or '0', 16) if m.group(2) else 0
            if s0 == '.rodata':
                if coff:
                    # COFF REL32: the addend is the displacement field; target = S + A + nxt - (P + 4)
                    md = re.search(r'\[rip([+-]0x[0-9a-f]+)?\]', text)
                    disp = int(md.group(1), 16) if md and md.group(1) else 0
                    rt = disp + (nxt - p - 4)
                else:
                    rt = add + (nxt - p)
            else:
                ext = s0
        if mn in CCS or mn == 'jmp':
            if not ext:
                t = int(ops[0].split()[0], 16)
                tgt = addr_index.get(t)
                if tgt is None:
                    raise Fail('branch target %x outside %s' % (t, sym))
        try:
            out.append((addr, text, translate(mn, ops, rt, tgt, ext)))
        except Fail as e:
            raise SystemExit('%x: %s: %s' % (addr, text, e))
    print('import Hashtree.Asm.X86\n')
    print('/-! Generated by tools/x86_to_lean.py from the shipped object (symbol `%s`). -/\n' % sym)
    print('namespace %s' % ns)
    print('open Hashtree.Asm Hashtree.Asm.X86\n')
    print('set_option maxRecDepth 100000 in')
    print('def prog : Array Instr := #[')
    for k, (addr, text, term) in enumerate(out):
        sep = ',' if k + 1 < len(out) else ''
        print('  %s%s  -- %d @%x: %s' % (term, sep, k, addr, text))
    print(']\n')
    print('set_option maxRecDepth 100000 in')
    print('/-- `.rodata` bytes. -/')
    print('def rodata : List Nat := [%s]\n' % ', '.join(str(b) for b in rodata))
    print('end %s' % ns)


if __name__ == '__main__':
    main()
