#!/usr/bin/env python3
"""Differential test: the Lean RV64 model (rvcheck --dump/--disp) vs the shipped objects under
qemu-riscv64 (rv_harness), vs hashlib.  Run on the VM from formal/lean:

    python3 tools/rv_diff.py <harness binary> [<harness binary> ...]
"""
import hashlib
import itertools
import os
import re
import subprocess
import sys

RVCHECK = '.lake/build/bin/rvcheck'
QEMU = 'qemu-riscv64-static'
FULL = 'rv64,zbb=true,zbkb=true,zknh=true'
KERNELS = ['hashtree_sha256_riscv_x1', 'hashtree_sha256_riscv_zbb_x1', 'hashtree_sha256_riscv_crypto']


def rand_input(seed, n):
    x = (seed * 6364136223846793005 + 1442695040888963407) % 2 ** 64
    a = bytearray()
    for _ in range(n):
        x = (x * 6364136223846793005 + 1442695040888963407) % 2 ** 64
        a.append((x >> 33) % 256)
    return bytes(a)


def expected(count, seed):
    b = rand_input(seed, 64 * count)
    return ''.join(hashlib.sha256(b[64 * i:64 * i + 64]).hexdigest() for i in range(count))


def sh(args, **kw):
    return subprocess.run(args, capture_output=True, text=True, **kw)


def main():
    harnesses = sys.argv[1:]
    fails = 0
    n = 0
    counts = [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 34]
    offs = [(0, 0), (1, 0), (0, 1), (2, 3), (3, 2), (5, 7), (4, 4), (7, 6), (13, 29), (63, 33)]
    for k, name in enumerate(KERNELS):
        for count, (io, oo) in itertools.product(counts, offs):
            seed = 1000 + 37 * count + io * 64 + oo
            exp = expected(count, seed)
            lean = sh([RVCHECK, '--dump', name, str(count), str(seed), str(io), str(oo)]).stdout.strip()
            for h in harnesses:
                q = sh([QEMU, '-cpu', FULL, h, 'k', str(k), str(count), str(seed), str(io), str(oo)])
                n += 1
                if not (q.returncode == 0 and q.stdout.strip() == lean == exp):
                    fails += 1
                    print('FAIL %s count=%d in+%d out+%d %s rc=%d' % (name, count, io, oo, h, q.returncode))
    # output inside the input buffer (in place / lagging)
    for k, name in enumerate(KERNELS):
        for count, (io, oo) in itertools.product([1, 2, 3, 7, 16], [(0, 0), (64, 0), (5, 5), (67, 1), (33, 2), (31, 30)]):
            seed = 3000 + count + io
            exp = expected(count, seed)
            lean = sh([RVCHECK, '--dumpa', name, str(count), str(seed), str(io), str(oo)]).stdout.strip()
            for h in harnesses:
                q = sh([QEMU, '-cpu', FULL, h, 'a', str(k), str(count), str(seed), str(io), str(oo)])
                n += 1
                if not (q.returncode == 0 and q.stdout.strip() == lean == exp):
                    fails += 1
                    print('FAIL alias %s count=%d in+%d out+%d %s rc=%d' % (name, count, io, oo, h, q.returncode))
    print('kernels: %d qemu runs compared with the model and hashlib' % n)
    # dispatcher: the probe answer of each qemu CPU, the kernel qemu executed, the model's choice
    cpus = ['rv64,zbb=false', 'rv64', 'rv64,zbb=false,zknh=true', 'rv64,zbb=false,zbkb=true',
            'rv64,zbb=false,zbkb=true,zknh=true', 'rv64,zbkb=true,zknh=true', FULL, 'max']
    h = harnesses[0]
    syms = {}
    for ln in sh(['riscv64-linux-gnu-nm', h]).stdout.splitlines():
        f = ln.split()
        if len(f) == 3:
            syms[f[2]] = int(f[0], 16)
    for cpu in cpus:
        pr = sh([QEMU, '-cpu', cpu, h, 'probe']).stdout.strip()
        count, seed, io, oo = 5, 77, 3, 1
        log = '/tmp/rv_diff_inasm.log'
        q = sh([QEMU, '-cpu', cpu, '-d', 'in_asm', '-D', log, h, 'k', '3', str(count), str(seed), str(io), str(oo)])
        text = open(log).read()
        ran = [nm for nm in KERNELS if re.search(r'0x0*%x:' % syms[nm], text)]
        os.unlink(log)
        dl = sh([RVCHECK, '--disp', pr if pr else 'fail', str(count), str(seed), str(io), str(oo)]).stdout.splitlines()
        m = re.match(r'path \[(.*)\] err (\S+) isaViolations (\d+)', dl[0])
        lean_k = m.group(1).split(', ')[-1]
        exp = expected(count, seed)
        ok = q.returncode == 0 and q.stdout.strip() == exp == dl[1].strip() and ran == [lean_k] \
            and m.group(2) == 'none' and m.group(3) == '0'
        print('dispatch cpu=%-38s hwprobe=%s qemu ran %s, model chose %s: %s' %
              (cpu, pr, ran, lean_k, 'ok' if ok else 'FAIL'))
        fails += 0 if ok else 1
    print('failures: %d' % fails)
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
