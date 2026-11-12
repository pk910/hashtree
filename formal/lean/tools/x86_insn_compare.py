#!/usr/bin/env python3
"""Compare native (or SDE) and model outputs of the x86 per-instruction differential test.

    x86_insn_compare.py <tests.json> <native.txt> <model.txt> [--ymm] [--label L] [--summary out.json]
    x86_insn_compare.py --cross <tests.json> <native_ymm.txt> <sde_zmm.txt>   # SDE vs silicon

Lines: `<test> <trial> tok...` with tokens v<r>.<l>=, g<i>=, m<reg>.<off>=, err=, pc=, OOB:, cc=.
The condition codes are compared only when the model has flags (`cc=-` otherwise: the kernels
never branch on flags of a data operation, and the model clobbers them).  Every other token must
be identical: a location the model changes and the CPU does not (or vice versa) is a mismatch,
so untouched lanes / registers / bytes are checked too.  On a mismatch the initial values of the
registers of the instruction are regenerated (same splitmix64 as the harness) for a reproducer.
"""
import json
import re
import sys
from collections import defaultdict

M64 = (1 << 64) - 1
GPR64 = ['rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi'] + ['r%d' % i for i in range(8, 16)]
GPR32 = ['eax', 'ecx', 'edx', 'ebx', 'esp', 'ebp', 'esi', 'edi'] + ['r%dd' % i for i in range(8, 16)]
CCS = ['e', 'ne', 'l', 'ge', 'le', 'g', 'b', 'ae', 'be', 'a']


def splitmix(seed):
    x = seed & M64
    while True:
        x = (x + 0x9e3779b97f4a7c15) & M64
        z = x
        z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & M64
        z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & M64
        yield z ^ (z >> 31)


def init_state(t, k, test, bases):
    g = splitmix(t * 1000003 + k + 12345)
    v = [[next(g) & 0xffffffff for _ in range(16)] for _ in range(32)]
    raw = [next(g) for _ in range(16)]
    gpr = list(raw)
    gpr[4] = bases[3] + 2048
    for r, kd in test['kinds'].items():
        r = int(r)
        x, m = raw[r], raw[r] >> 2
        typ = kd[0]
        if typ == 'c':
            val = [m % 48, m % 4096, m % (1 << 32), m % (1 << 62)][x & 3]
        elif typ == 'cm':
            val = (x % kd[1]) * kd[2]
        elif typ == 'p':
            val = bases[kd[1]] + kd[2]
        elif typ == 'pr':
            val = bases[kd[1]] + (x % kd[2]) * kd[3]
        elif typ == 'cb':
            val = x | (1 << 63)
        else:
            val = x
        gpr[r] = val
    return v, gpr


def parse(path):
    d, bases = {}, None
    for ln in open(path):
        p = ln.split()
        if not p:
            continue
        if p[0] == 'bases':
            bases = {1: int(p[1]), 3: int(p[2]), 4: int(p[3])}
            continue
        if not p[0].isdigit():
            continue
        toks = p[2:]
        cc = [x for x in toks if x.startswith('cc=')]
        rest = frozenset(x for x in toks if not x.startswith('cc='))
        d[(int(p[0]), int(p[1]))] = (rest, cc[0][3:] if cc else None)
    return d, bases


def project_ymm(toks):
    out = set()
    for x in toks:
        m = re.match(r'v(\d+)\.(\d+)=', x)
        if m and (int(m.group(1)) >= 16 or int(m.group(2)) >= 8):
            continue
        out.add(x)
    return frozenset(out)


def regs_of(asm):
    vs = sorted({(m.group(1), int(m.group(2))) for m in re.finditer(r'\b([xyz])mm(\d+)\b', asm)}, key=lambda a: a[1])
    gs = sorted({GPR64.index(r) if r in GPR64 else GPR32.index(r)
                 for r in re.findall(r'\b[a-z][a-z0-9]*\b', asm) if r in GPR64 or r in GPR32})
    return vs, gs


def reproducer(t, k, test, bases, nat, mod):
    v, gpr = init_state(t, k, test, bases)
    lines = ['  test %d trial %d: `%s`  (seed %d)' % (t, k, test['asm'], t * 1000003 + k + 12345)]
    if test['kinds']:
        lines.append('    kinds: %s' % {GPR64[int(r)]: kd for r, kd in test['kinds'].items()})
    vs, gs = regs_of(test['asm'])
    if test['asm'].startswith('sha256rnds2'):
        vs = sorted(set(vs) | {('x', 0)}, key=lambda a: a[1])
    for w, r in vs:
        n = {'x': 4, 'y': 8, 'z': 16}[w]
        lines.append('    in  %smm%d = [%s]  (lanes 0..%d, low first)' % (w, r, ' '.join('%08x' % x for x in v[r][:n]), n - 1))
    for r in gs:
        lines.append('    in  %s = %016x' % (GPR64[r], gpr[r]))
    only_n = sorted(nat[0] - mod[0])
    only_m = sorted(mod[0] - nat[0])
    lines.append('    native only: %s' % ' '.join(only_n[:40]))
    lines.append('    model  only: %s' % ' '.join(only_m[:40]))
    if mod[1] not in (None, '-') and nat[1] != mod[1]:
        lines.append('    cc (%s): native %s model %s' % (' '.join(CCS), nat[1], mod[1]))
    return '\n'.join(lines)


def compare(tests, native, model, ymm, label, summary):
    nat, bases = parse(native)
    mod, _ = parse(model)
    per = defaultdict(lambda: [0, 0, None])
    missing = 0
    for key, nv in nat.items():
        t, k = key
        mv = mod.get(key)
        e = per[t]
        e[0] += 1
        if mv is None:
            missing += 1
            e[1] += 1
            continue
        ntoks = project_ymm(nv[0]) if ymm else nv[0]
        ok = ntoks == mv[0] and (mv[1] == '-' or mv[1] == nv[1])
        if not ok:
            e[1] += 1
            if e[2] is None:
                e[2] = reproducer(t, k, tests[t], bases, (ntoks, nv[1]), mv)
    extra = len(set(mod) - set(nat))
    groups = defaultdict(lambda: [0, 0, 0, 0])   # tests, vectors, failing tests, failing vectors
    flagged = defaultdict(int)
    for t, (n, f, _) in per.items():
        g = 'probe' if tests[t]['probe'] else tests[t]['group']
        groups[g][0] += 1
        groups[g][1] += n
        groups[g][2] += f > 0
        groups[g][3] += f
    for key, mv in mod.items():
        if key in nat and mv[1] not in (None, '-'):
            flagged[key[0]] += 1
    print('== %s: %d vectors over %d tests; model lines missing %d, extra %d' % (label, len(nat), len(per), missing, extra))
    for g in sorted(groups):
        a = groups[g]
        print('  %-8s tests %4d  vectors %7d  failing tests %3d  failing vectors %6d' % (g, a[0], a[1], a[2], a[3]))
    print('  vectors with condition codes compared: %d' % sum(flagged.values()))
    bad = [t for t, e in sorted(per.items()) if e[1]]
    for t in bad:
        n, f, rep = per[t]
        print('MISMATCH%s %d `%s`: %d/%d vectors' % (' (probe)' if tests[t]['probe'] else '', t, tests[t]['asm'], f, n))
        if rep:
            print(rep)
    if summary:
        json.dump({'label': label, 'vectors': len(nat), 'missing': missing, 'extra': extra,
                   'per_test': {t: {'asm': tests[t]['asm'], 'group': tests[t]['group'], 'probe': tests[t]['probe'],
                                    'vectors': e[0], 'fail': e[1], 'cc': flagged.get(t, 0)} for t, e in per.items()},
                   'groups': groups}, open(summary, 'w'), indent=0)
    nonprobe = [t for t in bad if not tests[t]['probe']]
    return 0 if not nonprobe and missing == 0 and extra == 0 else 1


def cross(tests, nfile, sfile):
    nat, nb = parse(nfile)
    sde, sb = parse(sfile)
    if nb != sb:
        print('buffer addresses differ (%s vs %s): pointer values not comparable' % (nb, sb))
        return 1
    n = bad = 0
    for key, nv in nat.items():
        sv = sde.get(key)
        if sv is None:
            continue
        n += 1
        if project_ymm(sv[0]) != nv[0] or sv[1] != nv[1]:
            bad += 1
            if bad <= 10:
                print('SDE/CPU differ: test %d trial %d `%s`' % (key[0], key[1], tests[key[0]]['asm']))
    print('== SDE vs Milan (ymm view, incl. all condition codes): %d common vectors, %d differ' % (n, bad))
    return 1 if bad else 0


def main():
    a = sys.argv[1:]
    if a[0] == '--cross':
        tests = json.load(open(a[1]))
        sys.exit(cross(tests, a[2], a[3]))
    tests = json.load(open(a[0]))
    ymm = '--ymm' in a
    label = a[a.index('--label') + 1] if '--label' in a else a[1]
    summary = a[a.index('--summary') + 1] if '--summary' in a else None
    sys.exit(compare(tests, a[1], a[2], ymm, label, summary))


if __name__ == '__main__':
    main()
