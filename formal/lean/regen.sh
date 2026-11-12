#!/usr/bin/env bash
# Regenerate Hashtree/Gen from the committed machine-code models.
#
# The generators use fixed seeds and read no external files, so the output is
# deterministic. This takes a long time (thousands of kernel-checked symbolic
# runs); CI runs it to verify that Gen.tar.zst is still what the generators
# produce.
set -euo pipefail
cd "$(dirname "$0")"

lake build x86loop x86loopw x86loop1 x86loop1w x86proof1 x86proofv armproof rvproof

rm -rf Hashtree/Gen
mkdir -p Hashtree/Gen

# linux/amd64: shani_x2 for every count (ShaniL) and from the wrapper's call
# state (ShaniW), sse_x1 and avx_x1 for every count, avx_x1 from the wrapper
# state, the fixed-count sse/avx pilots, and the multi-lane kernels.
for seg in head it t1 t0; do lake exe x86loop  Hashtree/Gen/ShaniL "$seg"; done
for seg in head it t1 t0; do lake exe x86loopw Hashtree/Gen/ShaniW "$seg"; done
lake exe x86loop1  sse Hashtree/Gen/SseX1L all
lake exe x86loop1  avx Hashtree/Gen/AvxX1L all
lake exe x86loop1w avx Hashtree/Gen/AvxX1LW all
lake exe x86proof1 sse Hashtree/Gen/SseX1P
lake exe x86proof1 avx Hashtree/Gen/AvxX1P
lake exe x86proofv x4  Hashtree/Gen/AvxX4P     --split
lake exe x86proofv x8  Hashtree/Gen/Avx2X8P    --split
lake exe x86proofv x16 Hashtree/Gen/Avx512X16P --split

# linux/arm64 (the macOS models are identical up to the tail symbol name)
lake exe armproof sha_x1  2 Hashtree/Gen/ArmShaX1P
lake exe armproof neon_x1 2 Hashtree/Gen/ArmNeonX1P
lake exe armproof neon_x4 4 Hashtree/Gen/ArmNeonX4P
lake exe armproof neon_x1 0 Hashtree/Gen/ArmNeonX1P0

# linux/riscv64
lake exe rvproof x1     Hashtree/Gen/RvX1P
lake exe rvproof zbb    Hashtree/Gen/RvZbbX1P
lake exe rvproof crypto Hashtree/Gen/RvCryptoP

echo "regenerated Hashtree/Gen"
