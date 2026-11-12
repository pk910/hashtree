#!/usr/bin/env python3
"""Per-instruction differential test of the x86-64 model (Hashtree/Asm/X86.lean) against the CPU.

    x86_insn_diff.py gen  <build>                 # test list -> asm harness + C table
    x86_insn_diff.py lean <build> <X86InsnCheck.lean>   # objects -> Lean table (in place)

Tests: (1) one or more tests per distinct instruction form of the shipped kernels plus the special
sweeps (palignr / vpalignr immediates 0..31, vpternlogd immediates 0..255, aliasing variants,
SHA-NI operand orders, flags after every flag-setting form), and (2) every distinct instruction
text that occurs in the generated kernel programs (Hashtree/Kernels/X86{,Win}/*.lean), with
rip-relative operands redirected to the harness's own rodata.

Each test is one instruction between the labels x_{y,z}insn_<n> / x_{y,z}insn_end_<n> of the
assembled harness x86_insn_tests.S (a ymm-state and a zmm-state copy, in one binary so that the
buffer addresses are the same natively and under SDE).  The Lean side is produced from the *disassembly of those
objects* by the same `x86_to_lean.translate` as the kernels, so the bytes that execute natively
are the bytes the model interprets.  Initial states (all vector registers, general registers,
three memory buffers) come from splitmix64 seeded by (test, trial), implemented identically in
the C harness, in X86InsnCheck.lean and in x86_insn_compare.py; both sides print the
locations whose value changed (vector lanes, 64-bit GPRs, memory bytes) and the ten condition
codes e ne l ge le g b ae be a.

General-register kinds (the model distinguishes data from pointers/counts):
  ('d',)            random 64-bit data (model: two lanes)
  ('c',)            random count: m%48 | m%4096 | m%2^32 | m%2^62 (m = raw>>2, by raw&3)
  ('cm', m, k)      count (raw % m) * k
  ('p', r, off)     pointer into buffer region r (1 data, 3 stack, 4 rodata) at off
  ('pr', r, m, k)   pointer into region r at (raw % m) * k
  ('cb',)           count with bit 63 set (out of the model's domain; probes only)
rsp is ('p', 3, 2048) unless overridden.
"""
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import x86_to_lean  # noqa: E402

GPR64 = x86_to_lean.GPR64
GPR32 = x86_to_lean.GPR32
NB1, NB3, NB4, SP0 = 4352, 4096, 256, 2048
CCS = ['e', 'ne', 'l', 'ge', 'le', 'g', 'b', 'ae', 'be', 'a']
KTYPE = {'d': 0, 'c': 1, 'cm': 2, 'p': 3, 'pr': 4, 'cb': 5}
EVEX_ONLY = {'vprord', 'vpternlogd', 'vpermi2d', 'vpermi2q', 'vmovdqa32', 'vmovdqa64', 'vmovdqu32',
             'vinserti64x4'}


def gi(name):
    """GPR index of a 64- or 32-bit register name."""
    return GPR64.index(name) if name in GPR64 else GPR32.index(name)


def T(asm, group, kinds=None, probe=False):
    return {'asm': asm, 'group': group, 'kinds': {gi(r): k for r, k in (kinds or {}).items()},
            'probe': probe}


P1 = ('p', 1, 0)


def form_tests():
    t = []
    # ---- lane-wise ALU (legacy 2-operand, VEX 3-operand, EVEX zmm)
    for op in ['paddd', 'pxor', 'por', 'pand']:
        t.append(T('%s xmm3, xmm7' % op, 'valu'))
        t.append(T('%s xmm5, xmm5' % op, 'valu'))
    t.append(T('paddd xmm0, XMMWORD PTR [rax]', 'valu', {'rax': P1}))
    t.append(T('paddd xmm1, XMMWORD PTR [rip+x_ro_l+0x40]', 'valu'))
    for op in ['vpaddd', 'vpxor', 'vpor', 'vpand']:
        for w in 'xy':
            t.append(T('%s %smm0, %smm4, %smm9' % (op, w, w, w), 'valu'))
            t.append(T('%s %smm7, %smm7, %smm14' % (op, w, w, w), 'valu'))
            t.append(T('%s %smm3, %smm5, %smm3' % (op, w, w, w), 'valu'))
            t.append(T('%s %smm6, %smm6, %smm6' % (op, w, w, w), 'valu'))
    t.append(T('vpaddd xmm9, xmm4, XMMWORD PTR [rcx+0x30]', 'valu', {'rcx': P1}))
    t.append(T('vpaddd xmm14, xmm14, XMMWORD PTR [rcx+r9*1]', 'valu', {'rcx': P1, 'r9': ('cm', 64, 16)}))
    t.append(T('vpaddd xmm2, xmm3, XMMWORD PTR [rax+r9*1+0x10]', 'valu', {'rax': P1, 'r9': ('cm', 64, 16)}))
    t.append(T('vpaddd ymm8, ymm8, YMMWORD PTR [rcx+0x60]', 'valu', {'rcx': P1}))
    t.append(T('vpaddd zmm8, zmm7, zmm12', 'valu'))
    t.append(T('vpaddd zmm25, zmm30, zmm16', 'valu'))
    t.append(T('vpaddd zmm3, zmm3, zmm3', 'valu'))
    t.append(T('vpaddd zmm0, zmm0, ZMMWORD PTR [r11+0x40]', 'valu', {'r11': P1}))
    # ---- shifts (kernel immediates, plus 0/1/31/32/33 boundary values)
    kim = {
        ('pslld', 'x'): [0x19, 0xe], ('psrld', 'x'): [0x12, 3, 7, 0xa], ('psrlq', 'x'): [0x11, 0x13],
        ('vpslld', 'x'): [0x15, 0x19, 0x1a, 0x1b, 0x1e, 7, 0xa, 0xe, 0xf],
        ('vpslld', 'y'): [0x15, 0x19, 0x1a, 0x1b, 0x1e, 7, 0xa, 0xf],
        ('vpsrld', 'x'): [0x11, 0x12, 0x16, 0x19, 2, 3, 5, 6, 7, 0xa, 0xb],
        ('vpsrld', 'y'): [0x11, 0x16, 0x19, 2, 3, 5, 6, 7, 0xa, 0xb],
        ('vpsrld', 'z'): [3, 0xa], ('vpsrlq', 'x'): [0x11, 0x13],
        ('vprord', 'z'): [0x11, 0x12, 0x13, 0x16, 0x19, 2, 6, 7, 0xb, 0xd],
    }
    extra = {'pslld': [0, 1, 31, 32, 33], 'psrld': [0, 1, 31, 32], 'psrlq': [0, 1, 31, 32, 33, 63, 64],
             'vpslld': [0, 31, 32], 'vpsrld': [0, 31, 32], 'vpsrlq': [0, 32, 33, 63, 64], 'vprord': [0, 1, 31]}
    for (op, w), ims in kim.items():
        for n in ims + [n for n in extra[op] if n not in ims and w != 'y']:
            if op.startswith('v'):
                t.append(T('%s %smm2, %smm1, 0x%x' % (op, w, w, n), 'vshift'))
            else:
                t.append(T('%s %smm2, 0x%x' % (op, w, n), 'vshift'))
    t.append(T('vpsrld xmm9, xmm9, 0x11', 'vshift'))
    t.append(T('vpslld ymm15, ymm15, 0x7', 'vshift'))
    t.append(T('vpsrld zmm15, zmm17, 0x3', 'vshift'))
    t.append(T('vprord zmm13, zmm30, 0x11', 'vshift'))
    t.append(T('vprord zmm4, zmm4, 0x19', 'vshift'))
    # ---- vpternlogd: all immediates; aliasing for the kernel immediates
    for imm in range(256):
        t.append(T('vpternlogd zmm10, zmm11, zmm12, 0x%x' % imm, 'vtern'))
    for imm in (0x96, 0xca, 0xe8):
        t.append(T('vpternlogd zmm9, zmm9, zmm20, 0x%x' % imm, 'vtern'))
        t.append(T('vpternlogd zmm9, zmm5, zmm9, 0x%x' % imm, 'vtern'))
        t.append(T('vpternlogd zmm9, zmm9, zmm9, 0x%x' % imm, 'vtern'))
        t.append(T('vpternlogd zmm27, zmm1, zmm1, 0x%x' % imm, 'vtern'))
    # ---- moves, loads, stores
    S = {'rsp': ('p', 3, SP0)}
    mv = [
        ('movdqa XMMWORD PTR [rsp], xmm1', {}), ('movdqa XMMWORD PTR [rsp+0x4a0], xmm9', {}),
        ('movdqa xmm0, XMMWORD PTR [rcx]', {'rcx': P1}), ('movdqa xmm6, XMMWORD PTR [rsp+0x60]', {}),
        ('movdqa xmm8, XMMWORD PTR [rip+x_ro_l+0x80]', {}), ('movdqa xmm3, xmm0', {}),
        ('movdqa xmm3, xmm3', {}),
        ('movdqu XMMWORD PTR [rdi+0x24], xmm1', {'rdi': P1}), ('movdqu xmm0, XMMWORD PTR [rsi+0x13]', {'rsi': P1}),
        ('vmovdqa XMMWORD PTR [rsp], xmm9', {}), ('vmovdqa YMMWORD PTR [rsp+0x300], ymm6', {}),
        ('vmovdqa xmm0, XMMWORD PTR [rcx+0x10]', {'rcx': P1}),
        ('vmovdqa xmm4, XMMWORD PTR [rcx+r9*1]', {'rcx': P1, 'r9': ('cm', 64, 16)}),
        ('vmovdqa xmm5, XMMWORD PTR [rax+r9*1]', {'rax': P1, 'r9': ('cm', 64, 16)}),
        ('vmovdqa xmm13, XMMWORD PTR [rip+x_ro_l+0x10]', {}), ('vmovdqa xmm4, xmm6', {}),
        ('vmovdqa ymm0, YMMWORD PTR [rcx+0x20]', {'rcx': P1}), ('vmovdqa ymm7, YMMWORD PTR [rip+x_ro_l+0x20]', {}),
        ('vmovdqa ymm12, ymm8', {}), ('vmovdqa ymm6, YMMWORD PTR [rsp+0x4c0]', {}),
        ('vmovdqu XMMWORD PTR [rdi+0x7], xmm14', {'rdi': P1}), ('vmovdqu YMMWORD PTR [rdi+0x41], ymm0', {'rdi': P1}),
        ('vmovdqu xmm4, XMMWORD PTR [rsi+0x5]', {'rsi': P1}),
        ('vmovups xmm12, XMMWORD PTR [rsi+0x3]', {'rsi': P1}), ('vmovups ymm8, YMMWORD PTR [rsi+0x1c1]', {'rsi': P1}),
        ('vmovups ymm16, YMMWORD PTR [rsi+0x2]', {'rsi': P1}), ('vmovups ymm25, YMMWORD PTR [rsi+0x60]', {'rsi': P1}),
        ('vmovdqa32 zmm0, ZMMWORD PTR [r11+0x40]', {'r11': P1}),
        ('vmovdqa32 zmm11, ZMMWORD PTR [rip+x_ro_l+0x40]', {}),
        ('vmovdqa32 zmm9, zmm4', {}), ('vmovdqa32 zmm20, zmm31', {}),
        ('vmovdqa64 zmm13, ZMMWORD PTR [rip+x_ro_l+0x80]', {}),
        ('vmovdqu32 ZMMWORD PTR [rdi+0x3], zmm0', {'rdi': P1}), ('vmovdqu32 ZMMWORD PTR [rdi+0x100], zmm29', {'rdi': P1}),
        ('vmovdqu32 zmm10, zmm13', {}),
    ]
    for a, k in mv:
        t.append(T(a, 'vmov', k))
    # ---- shuffles
    for imm in (0x1b, 0x50, 0xb1, 0xe, 0xfa, 0x00, 0xff, 0xe4):
        t.append(T('pshufd xmm2, xmm7, 0x%x' % imm, 'shuf'))
        t.append(T('pshufd xmm1, xmm1, 0x%x' % imm, 'shuf'))
    for imm in (0x50, 0xfa, 0x1b, 0x93):
        t.append(T('vpshufd xmm2, xmm0, 0x%x' % imm, 'shuf'))
        t.append(T('vpshufd xmm3, xmm3, 0x%x' % imm, 'shuf'))
    t += [T('pshufb xmm0, xmm8', 'pshufb'), T('pshufb xmm1, xmm1', 'pshufb'), T('pshufb xmm5, xmm2', 'pshufb'),
          T('vpshufb xmm4, xmm4, xmm13', 'pshufb'), T('vpshufb xmm4, xmm5, xmm13', 'pshufb'),
          T('vpshufb xmm6, xmm7, xmm6', 'pshufb'), T('vpshufb xmm2, xmm2, xmm2', 'pshufb'),
          T('vpshufb ymm8, ymm8, ymm7', 'pshufb'), T('vpshufb ymm1, ymm9, ymm3', 'pshufb'),
          T('vpshufb zmm16, zmm16, zmm11', 'pshufb'), T('vpshufb zmm3, zmm20, zmm7', 'pshufb'),
          T('vpshufb zmm5, zmm6, zmm5', 'pshufb')]
    for imm in list(range(32)) + [32, 40, 128, 255]:
        t.append(T('palignr xmm7, xmm5, 0x%x' % imm, 'palignr'))
        t.append(T('vpalignr xmm0, xmm7, xmm6, 0x%x' % imm, 'palignr'))
    t += [T('palignr xmm2, xmm2, 0x4', 'palignr'), T('palignr xmm2, xmm2, 0x8', 'palignr'),
          T('vpalignr xmm3, xmm3, xmm6, 0x4', 'palignr'), T('vpalignr xmm3, xmm6, xmm3, 0x4', 'palignr'),
          T('vpalignr xmm1, xmm1, xmm1, 0x5', 'palignr')]
    for imm in (0xf0, 0x0f, 0x00, 0xff, 0x33, 0xcc, 0xa5, 0x5a, 0x01, 0x80):
        t.append(T('pblendw xmm1, xmm2, 0x%x' % imm, 'blend'))
    t.append(T('pblendw xmm9, xmm9, 0xf0', 'blend'))
    for w in 'xyz':
        for imm in (0x44, 0x88, 0xdd, 0xee, 0x1b, 0xe4):
            t.append(T('vshufps %smm14, %smm12, %smm13, 0x%x' % (w, w, w, imm), 'shuf'))
        t.append(T('vshufps %smm12, %smm12, %smm10, 0x88' % (w, w, w), 'shuf'))
        t.append(T('vshufps %smm13, %smm9, %smm13, 0xdd' % (w, w, w), 'shuf'))
    t.append(T('vshufps zmm17, zmm16, zmm18, 0x88', 'shuf'))
    for imm in (0x13, 0x02, 0x20, 0x31, 0x00, 0x11, 0x22, 0x33, 0x08, 0x80, 0x88, 0x28, 0x83, 0xff):
        t.append(T('vperm2f128 ymm6, ymm5, ymm1, 0x%x' % imm, 'perm'))
    t += [T('vperm2f128 ymm5, ymm5, ymm1, 0x13', 'perm'), T('vperm2f128 ymm1, ymm5, ymm1, 0x02', 'perm')]
    for imm in (1, 0):
        t.append(T('vinserti128 ymm8, ymm8, XMMWORD PTR [rsi+0x100], 0x%x' % imm, 'perm', {'rsi': P1}))
        t.append(T('vinserti128 ymm3, ymm9, XMMWORD PTR [rdx+0x1b0], 0x%x' % imm, 'perm', {'rdx': P1}))
        t.append(T('vinserti64x4 zmm16, zmm16, YMMWORD PTR [rsi+0x200], 0x%x' % imm, 'perm', {'rsi': P1}))
        t.append(T('vinserti64x4 zmm2, zmm7, YMMWORD PTR [rsi+0x24], 0x%x' % imm, 'perm', {'rsi': P1}))
    t.append(T('vinserti128 ymm4, ymm4, XMMWORD PTR [rsi+0x3], 0x3', 'perm', {'rsi': P1}))
    t += [T('vpermi2d zmm9, zmm0, zmm4', 'permi2'), T('vpermi2d zmm30, zmm22, zmm17', 'permi2'),
          T('vpermi2d zmm9, zmm9, zmm4', 'permi2'), T('vpermi2d zmm9, zmm4, zmm9', 'permi2'),
          T('vpermi2d zmm9, zmm4, zmm4', 'permi2'),
          T('vpermi2q zmm10, zmm25, zmm29', 'permi2'), T('vpermi2q zmm1, zmm2, zmm3', 'permi2'),
          T('vpermi2q zmm10, zmm10, zmm29', 'permi2'), T('vpermi2q zmm10, zmm25, zmm10', 'permi2')]
    # ---- SHA-NI (implicit xmm0 in sha256rnds2; aliasing incl. xmm0 as destination/source)
    t += [T('sha256rnds2 xmm2, xmm1, xmm0', 'sha'), T('sha256rnds2 xmm1, xmm2, xmm0', 'sha'),
          T('sha256rnds2 xmm10, xmm9, xmm0', 'sha'), T('sha256rnds2 xmm3, xmm3, xmm0', 'sha'),
          T('sha256rnds2 xmm0, xmm5, xmm0', 'sha'), T('sha256rnds2 xmm5, xmm0, xmm0', 'sha'),
          T('sha256rnds2 xmm0, xmm0, xmm0', 'sha'),
          T('sha256msg1 xmm3, xmm4', 'sha'), T('sha256msg1 xmm14, xmm11', 'sha'), T('sha256msg1 xmm6, xmm6', 'sha'),
          T('sha256msg1 xmm0, xmm1', 'sha'),
          T('sha256msg2 xmm3, xmm6', 'sha'), T('sha256msg2 xmm12, xmm11', 'sha'), T('sha256msg2 xmm5, xmm5', 'sha'),
          T('sha256msg2 xmm0, xmm2', 'sha')]
    # ---- general registers: 32-bit data
    for op in ('add', 'xor', 'and', 'or'):
        t.append(T('%s r15d, r13d' % op, 'gpr32'))
        t.append(T('%s eax, ebx' % op, 'gpr32'))
        t.append(T('%s r9d, r9d' % op, 'gpr32'))
    t += [T('add r15d, DWORD PTR [rsp]', 'gpr32'), T('add r12d, DWORD PTR [rsp+0x24]', 'gpr32'),
          T('add eax, DWORD PTR [rcx+0x3]', 'gpr32', {'rcx': P1}),
          T('mov DWORD PTR [rsp+0x20], eax', 'gpr32'), T('mov DWORD PTR [rdi+0x5], r14d', 'gpr32', {'rdi': P1}),
          T('mov eax, DWORD PTR [rcx]', 'gpr32', {'rcx': P1}), T('mov r8d, DWORD PTR [rcx+0x3c]', 'gpr32', {'rcx': P1}),
          T('mov r13d, r9d', 'gpr32'), T('mov ecx, ecx', 'gpr32'), T('mov edx, r10d', 'gpr32'),
          T('bswap eax', 'gpr32'), T('bswap r12d', 'gpr32'), T('bswap edi', 'gpr32')]
    for n in (2, 5, 6, 9, 0xb, 0xe, 0, 1, 31):
        t.append(T('ror r14d, 0x%x' % n, 'gpr32'))
    t.append(T('ror eax, 0x6', 'gpr32'))
    for n in (0x12, 0x15, 0x17, 0x1a, 0x1b, 0x1e, 0, 1, 31):
        t.append(T('shld r13d, r13d, 0x%x' % n, 'gpr32'))
        t.append(T('shld r13d, r10d, 0x%x' % n, 'gpr32'))
    # ---- general registers: 64-bit pointers/counts, stack
    C, PR = ('c',), ('pr', 1, 64, 64)
    t += [T('mov r12, QWORD PTR [rsp+0x380]', 'gpr64'), T('mov QWORD PTR [rsp+0x398], r12', 'gpr64'),
          T('mov QWORD PTR [rsp+0x8], rbx', 'gpr64', {'rbx': PR}), T('mov rbx, QWORD PTR [rsp+0x8]', 'gpr64'),
          T('mov rbp, rsp', 'gpr64'), T('mov rax, rdx', 'gpr64', {'rdx': C}), T('mov rax, rdx', 'gpr64'),
          T('mov rsi, rcx', 'gpr64', {'rcx': PR}),
          T('push rbp', 'gpr64'), T('push r12', 'gpr64'), T('push rsi', 'gpr64', {'rsi': PR}),
          T('push rdi', 'gpr64', {'rdi': C}),
          T('pop rbp', 'gpr64'), T('pop r15', 'gpr64'), T('pop r8', 'gpr64'),
          T('xor r9, r9', 'gpr64'), T('xor r9, r9', 'gpr64', {'r9': C}),
          T('lea rcx, [rip+x_ro_l+0x0]', 'gpr64'), T('lea r11, [rip+x_ro_l+0x40]', 'gpr64'),
          T('and rsp, 0xffffffffffffffe0', 'gpr64', {'rsp': ('pr', 3, 64, 8)}),
          T('and rsp, 0xffffffffffffffc0', 'gpr64', {'rsp': ('pr', 3, 64, 8)}),
          T('shl rdx, 0x5', 'gpr64', {'rdx': ('cm', 1 << 40, 1)}), T('shl rdx, 0x6', 'gpr64', {'rdx': ('cm', 1 << 40, 1)})]
    # flag-setting forms: compare all ten condition codes
    for imm in (0x10, 0x100, 0x198, 0x20, 0x200, 0x238, 0x40, 0x400, 0x58, 0x80, 0xc0, 0xf8):
        t.append(T('add r9, 0x%x' % imm, 'flags', {'r9': C}))
    t += [T('add rdi, 0x100', 'flags', {'rdi': PR}), T('add rsi, 0x400', 'flags', {'rsi': PR}),
          T('add rsp, 0x198', 'flags'), T('add rsp, 0x238', 'flags'),
          T('add rdx, rdi', 'flags', {'rdx': C, 'rdi': PR}), T('add rdx, rdi', 'flags', {'rdx': C, 'rdi': C})]
    for imm in (0x10, 0x2, 0x4, 0x8, 0x198, 0x238, 0x3a0, 0x4e0, 0x58, 0xc0, 0xf8):
        t.append(T('sub rdx, 0x%x' % imm, 'flags', {'rdx': C}))
        t.append(T('sub rdx, 0x%x' % imm, 'flags', {'rdx': ('cm', 32, 1)}))
    for imm in (0x198, 0x238, 0x3a0, 0x4e0, 0x58, 0xc0, 0xf8):
        t.append(T('sub rsp, 0x%x' % imm, 'flags'))
    for imm in (0x0, 0x10, 0x2, 0x4, 0x400, 0x8):
        t.append(T('cmp rdx, 0x%x' % imm, 'flags', {'rdx': C}))
        t.append(T('cmp rdx, 0x%x' % imm, 'flags', {'rdx': ('cm', 2 * max(imm, 4), 1)}))
    t += [T('cmp r9, 0x400', 'flags', {'r9': ('cm', 128, 16)}),
          T('cmp rdi, rdx', 'flags', {'rdi': ('pr', 1, 4, 32), 'rdx': ('pr', 1, 4, 32)}),
          T('cmp rdi, rdx', 'flags', {'rdi': C, 'rdx': C}),
          T('cmp rdi, rdx', 'flags', {'rdi': ('cm', 4, 1), 'rdx': ('cm', 4, 1)}),
          T('test rdx, rdx', 'flags', {'rdx': C}), T('test rdx, rdx', 'flags', {'rdx': ('cm', 3, 1)})]
    # probes outside the model's domain (expected to differ; never used this way by the kernels)
    t += [T('cmp rcx, 0x10', 'probe', {'rcx': PR}, probe=True),
          T('sub rcx, 0x40', 'probe', {'rcx': PR}, probe=True),
          T('cmp rdx, 0x4', 'probe', {'rdx': ('cb',)}, probe=True),
          T('test rdx, rdx', 'probe', {'rdx': ('cb',)}, probe=True)]
    return t


# ---- every distinct kernel instruction text

SKIP = re.compile(r'^(j[a-z]+|ret)\b')   # control flow: covered by the kernel runs (x86check)


def kernel_texts():
    d = os.path.join(HERE, '..', 'Hashtree', 'Kernels')
    seen = {}
    for sub in ('X86', 'X86Win'):
        for f in sorted(os.listdir(os.path.join(d, sub))):
            for ln in open(os.path.join(d, sub, f)):
                m = re.search(r'-- \d+ @[0-9a-f]+: (.*)$', ln)
                if m:
                    txt = m.group(1).strip()
                    if not SKIP.match(txt):
                        seen.setdefault(txt, '%s/%s' % (sub, f))
    return seen


def sweep_test(txt):
    parts = txt.split(None, 1)
    mn = parts[0]
    ops = x86_to_lean.split_ops(parts[1]) if len(parts) > 1 else []
    asm = re.sub(r'\[rip(?:[+-]0x[0-9a-f]+)?\]', '[rip+x_ro_l+0x40]', txt)
    if asm.startswith('data16 '):   # gas rejects a second operand-size prefix in this spelling
        asm = '.byte 0x66; ' + asm[len('data16 '):]
    kinds = {}
    for o in ops:
        m = re.search(r'\[(.*)\]', o)
        if not m or 'rip' in m.group(1):
            continue
        for p in re.findall(r'[a-z][a-z0-9]*', m.group(1)):
            if p in GPR64 and p != 'rsp':
                star = re.search(re.escape(p) + r'\*', m.group(1))
                plus = re.search(r'\+' + re.escape(p) + r'\b', m.group(1))
                kinds[gi(p)] = ('cm', 64, 16) if (star or plus) else ('p', 1, 0)
    if mn in ('add', 'sub', 'cmp', 'test', 'shl') and ops and ops[0] in GPR64:
        for o in ops:
            if o in GPR64 and o != 'rsp':
                kinds[gi(o)] = ('cm', 1 << 40, 1) if mn == 'shl' else ('c',)
    return {'asm': asm, 'group': 'kernel', 'kinds': kinds, 'probe': False, 'orig': txt}


def needs512(asm):
    mn = asm.split()[0]
    return bool(mn in EVEX_ONLY or re.search(r'\bzmm\d+|\b[xy]mm(1[6-9]|2\d|3[01])\b', asm))


def all_tests():
    t = form_tests()
    for txt in kernel_texts():
        t.append(sweep_test(txt))
    for x in t:
        x['avx512'] = needs512(x['asm'])
    return t


# ---- harness generation

def asm_file(tests):
    """One object with two functions per test: x_y<n> (ymm0-15 state, for CPUs without AVX-512)
    and x_z<n> (zmm0-31 state); test instruction between x_{y,z}insn_<n> and x_{y,z}insn_end_<n>."""
    o = ['\t.intel_syntax noprefix', '\t.section .rodata', '\t.p2align 12', 'x_ro_l:', '\t.globl x_ro', 'x_ro:',
         '\t.zero %d' % NB4, '\t.text']
    for z in 'yz':
        nv = 32 if z == 'z' else 16
        mv = 'vmovdqu32' if z == 'z' else 'vmovdqu'
        o += ['\t.p2align 4', 'x_%sloadv:' % z]
        o += ['\t%s %smm%d, %sMMWORD PTR [rip+x_in_v+%d]' % (mv, z, r, z.upper(), 64 * r) for r in range(nv)]
        o += ['\tret', 'x_%sstorev:' % z]
        o += ['\t%s %sMMWORD PTR [rip+x_out_v+%d], %smm%d' % (mv, z.upper(), 64 * r, z, r) for r in range(nv)]
        o.append('\tret')
    for n, x in enumerate(tests):
        for z in 'yz':
            o += ['\t.p2align 4', '\t.globl x_%s%d' % (z, n), 'x_%s%d:' % (z, n)]
            o += ['\tpush %s' % r for r in ('rbx', 'rbp', 'r12', 'r13', 'r14', 'r15')]
            o += ['\tmov QWORD PTR [rip+x_saved], rsp', '\tcall x_%sloadv' % z, '\tmov rsp, QWORD PTR [rip+x_in_g+32]']
            o += ['\tmov %s, QWORD PTR [rip+x_in_g+%d]' % (GPR64[i], 8 * i) for i in range(16) if i != 4]
            o += ['x_%sinsn_%d:' % (z, n), '\t' + x['asm'], 'x_%sinsn_end_%d:' % (z, n)]
            o += ['\tset%s BYTE PTR [rip+x_cc+%d]' % (c, i) for i, c in enumerate(CCS)]
            o += ['\tmov QWORD PTR [rip+x_out_g+%d], %s' % (8 * i, GPR64[i]) for i in range(16)]
            o += ['\tmov rsp, QWORD PTR [rip+x_saved]', '\tcall x_%sstorev' % z]
            o += ['\tpop %s' % r for r in ('r15', 'r14', 'r13', 'r12', 'rbp', 'rbx')]
            o.append('\tret')
    o.append('\t.section .note.GNU-stack,"",@progbits')
    return '\n'.join(o) + '\n'


def kind_c(k):
    a = list(k[1:]) + [0, 0, 0]
    return KTYPE[k[0]], a[0], a[1], a[2]


def tab_h(tests):
    o = ['/* generated by tools/x86_insn_diff.py */', '#define NTESTS %d' % len(tests),
         'struct kind { int reg, type; uint64_t a, b, c; };']
    for n, x in enumerate(tests):
        ks = ', '.join('{%d, %d, %dull, %dull, %dull}' % ((r,) + kind_c(k)) for r, k in sorted(x['kinds'].items()))
        o.append('static const struct kind K%d[] = {%s%s{-1, 0, 0, 0, 0}};' % (n, ks, ', ' if ks else ''))
        o.append('void x_y%d(void); void x_z%d(void);' % (n, n))
    o.append('static const struct kind *const KINDS[NTESTS] = {%s};' % ', '.join('K%d' % n for n in range(len(tests))))
    o.append('static void (*const FUNCS_Y[NTESTS])(void) = {%s};' % ', '.join('x_y%d' % n for n in range(len(tests))))
    o.append('static void (*const FUNCS_Z[NTESTS])(void) = {%s};' % ', '.join('x_z%d' % n for n in range(len(tests))))
    o.append('static const unsigned char AVX512[NTESTS] = {%s};' % ', '.join(str(int(x['avx512'])) for x in tests))
    return '\n'.join(o) + '\n'


def gen(build):
    os.makedirs(build, exist_ok=True)
    tests = all_tests()
    with open(os.path.join(build, 'x86_insn_tests.S'), 'w') as f:
        f.write(asm_file(tests))
    with open(os.path.join(build, 'x86_insn_tab.h'), 'w') as f:
        f.write(tab_h(tests))
    with open(os.path.join(build, 'tests.json'), 'w') as f:
        json.dump(tests, f, indent=0)
    print('%d tests (%d form tests, %d kernel texts, %d need AVX-512)' % (
        len(tests), sum(x['group'] != 'kernel' for x in tests), sum(x['group'] == 'kernel' for x in tests),
        sum(x['avx512'] for x in tests)))


# ---- translation of the assembled test instructions

def disasm_tests(obj, z):
    """{n: (text, translated term)} from the object's disassembly between x_<z>insn_n / x_<z>insn_end_n."""
    dis = subprocess.run(['objdump', '-d', '-r', '--no-show-raw-insn', '-M', 'intel', obj],
                         capture_output=True, text=True, check=True).stdout
    cur, insns = None, {}
    for ln in dis.splitlines():
        m = re.match(r'^([0-9a-f]+) <([^>]+)>:$', ln)
        if m:
            mm = re.fullmatch(r'x_%sinsn_(\d+)' % z, m.group(2))
            cur = int(mm.group(1)) if mm else None
            continue
        m = re.match(r'^\s+([0-9a-f]+):\s+(R_X86_64_\w+)\s+(\S+)$', ln)
        if m and cur is not None and insns.get(cur):
            insns[cur][-1][2] = (int(m.group(1), 16), m.group(2), m.group(3))
            continue
        m = re.match(r'^\s+([0-9a-f]+):\t(.*)$', ln)
        if m and cur is not None:
            insns.setdefault(cur, []).append([int(m.group(1), 16), m.group(2).split('#')[0].strip(), None])
            continue
    # the address of the next instruction (x_insn_end_n) for rip-relative relocations
    ends = {}
    for ln in dis.splitlines():
        m = re.match(r'^([0-9a-f]+) <x_%sinsn_end_(\d+)>:$' % z, ln)
        if m:
            ends[int(m.group(2))] = int(m.group(1), 16)
    out = {}
    for n, lst in insns.items():
        if len(lst) != 1:
            raise SystemExit('test %d: %d instructions between labels: %s' % (n, len(lst), lst))
        addr, text, rel = lst[0]
        parts = text.split(None, 1)
        mn = parts[0]
        ops = x86_to_lean.split_ops(parts[1]) if len(parts) > 1 else []
        rt = None
        if rel:
            p, kind, symadd = rel
            m = re.match(r'([^+-]+)([+-]0x[0-9a-f]+)?$', symadd)
            s0 = m.group(1)
            add = int(m.group(2), 16) if m.group(2) else 0
            if s0 != '.rodata':
                raise SystemExit('test %d: relocation against %s' % (n, s0))
            rt = add + (ends[n] - p)
        out[n] = (text, x86_to_lean.translate(mn, ops, rt, None, None))
    return out


def lean(build, leanfile):
    tests = json.load(open(os.path.join(build, 'tests.json')))
    a = disasm_tests(os.path.join(build, 'x86_insn_tests.o'), 'y')
    b = disasm_tests(os.path.join(build, 'x86_insn_tests.o'), 'z')
    if a != b:
        raise SystemExit('ymm/zmm objects translate differently')
    if sorted(a) != list(range(len(tests))):
        raise SystemExit('missing tests in object')
    # the sweep tests must interpret the kernel instruction exactly as the kernel program does
    # (rip-relative offsets aside: they point at the harness's rodata)
    kterms = {}
    d = os.path.join(HERE, '..', 'Hashtree', 'Kernels')
    for sub in ('X86', 'X86Win'):
        for f in sorted(os.listdir(os.path.join(d, sub))):
            for ln in open(os.path.join(d, sub, f)):
                m = re.match(r'^\s+(.*?),?\s+-- \d+ @[0-9a-f]+: (.*)$', ln)
                if m:
                    kterms.setdefault(m.group(2).strip(), set()).add(m.group(1))
    norm = lambda s: re.sub(r'ro := some -?\d+', 'ro := some _', s)
    nk = 0
    for n, x in enumerate(tests):
        if x['group'] == 'kernel':
            ks = {norm(k) for k in kterms[x['orig']]}
            if ks != {norm(a[n][1])}:
                raise SystemExit('test %d (%s): harness term %s vs kernel terms %s' % (n, x['orig'], a[n][1], ks))
            nk += 1
    print('%d kernel-text tests: harness translation == kernel program term' % nk)
    rows = []
    for n, x in enumerate(tests):
        text, term = a[n]
        ks = ', '.join('(%d, %s)' % (int(r), kind_lean(k)) for r, k in sorted(x['kinds'].items(), key=lambda kv: int(kv[0])))
        rows.append('  ⟨"%s", %s, [%s], %s⟩' % (text.replace('"', '\\"'), term, ks, 'true' if x['avx512'] else 'false'))
    body = ('-- BEGIN TABLE (generated by tools/x86_insn_diff.py from the assembled harness objects)\n'
            'set_option maxRecDepth 100000 in\n'
            'def tests : Array Test := #[\n' + ',\n'.join(rows)
            + ']\n-- END TABLE')
    src = open(leanfile).read()
    src2 = re.sub(r'-- BEGIN TABLE.*?-- END TABLE', lambda _: body, src, flags=re.S)
    if src2 == src and '-- BEGIN TABLE' not in src:
        raise SystemExit('no table markers in ' + leanfile)
    open(leanfile, 'w').write(src2)
    print('%d tests written to %s' % (len(rows), leanfile))


def kind_lean(k):
    k = list(k)
    if k[0] == 'd':
        return '.dat'
    if k[0] == 'c':
        return '.cnt'
    if k[0] == 'cb':
        return '.cbig'
    if k[0] == 'cm':
        return '(.cm %d %d)' % (k[1], k[2])
    if k[0] == 'p':
        return '(.ptr %d %d)' % (k[1], k[2])
    if k[0] == 'pr':
        return '(.pr %d %d %d)' % (k[1], k[2], k[3])
    raise ValueError(k)


if __name__ == '__main__':
    if sys.argv[1] == 'gen':
        gen(sys.argv[2])
    elif sys.argv[1] == 'lean':
        lean(sys.argv[2], sys.argv[3])
    else:
        raise SystemExit(__doc__)
