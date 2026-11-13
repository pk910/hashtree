#!/usr/bin/env bash
# Regenerate Hashtree/Gen from the committed machine-code models.
#
#   ./regen.sh                 # everything (long: thousands of kernel-checked
#                              # symbolic runs, tens of minutes to a few hours,
#                              # several GB of RAM)
#   ./regen.sh shani_x2        # one kernel: remove only its Gen trees,
#                              # regenerate them, then build its final theorem
#
# The generators use fixed seeds and read no external files, so the output is
# deterministic.  Partial regeneration assumes the rest of Hashtree/Gen is
# present (`make gen`); it rebuilds the affected proof module at the end, so a
# successful run is also the certificate check for that kernel.
set -euo pipefail
cd "$(dirname "$0")"

target=${1:-all}
case "$target" in
  all|shani_x2|sse_x1|avx_x1|avx_x4|avx2_x8|avx512_x16|\
  sha_x1|neon_x1|neon_x4|riscv_x1|riscv_zbb_x1|riscv_crypto|\
  wrapper_linux_amd64|go_generic|go_api) ;;
  *)
    echo "unknown target: $target" >&2
    echo "see the case list at the top of regen.sh" >&2
    exit 2 ;;
esac

want() { [ "$target" = all ] || [ "$target" = "$1" ]; }

# Build the generators once; they are small compared with the proofs.
lake build x86loop x86loopw x86loop1 x86loop1w x86proof1 x86proofv armproof rvproof armloop1

if [ "$target" = all ]; then
  rm -rf Hashtree/Gen
else
  case "$target" in
    shani_x2)           rm -rf Hashtree/Gen/ShaniL Hashtree/Gen/ShaniW ;;
    sse_x1)             rm -rf Hashtree/Gen/SseX1L Hashtree/Gen/SseX1P ;;
    avx_x1)             rm -rf Hashtree/Gen/AvxX1L Hashtree/Gen/AvxX1LW Hashtree/Gen/AvxX1P ;;
    avx_x4)             rm -rf Hashtree/Gen/AvxX4P ;;
    avx2_x8)            rm -rf Hashtree/Gen/Avx2X8P ;;
    avx512_x16)         rm -rf Hashtree/Gen/Avx512X16P ;;
    sha_x1)             rm -rf Hashtree/Gen/ArmShaX1P ;;
    neon_x1)            rm -rf Hashtree/Gen/ArmNeonX1P Hashtree/Gen/ArmNeonX1P0 ;;
    neon_x4)            rm -rf Hashtree/Gen/ArmNeonX4P ;;
    riscv_x1)           rm -rf Hashtree/Gen/RvX1P ;;
    riscv_zbb_x1)       rm -rf Hashtree/Gen/RvZbbX1P ;;
    riscv_crypto)       rm -rf Hashtree/Gen/RvCryptoP ;;
    *)                  : ;;
  esac
fi
mkdir -p Hashtree/Gen

# linux/amd64: shani_x2 for every count (ShaniL) and from the wrapper's call
# state (ShaniW), sse_x1 and avx_x1 for every count, avx_x1 from the wrapper
# state, the fixed-count pilots, and the multi-lane kernels.
if want shani_x2; then
  for seg in head it t1 t0; do lake exe x86loop  Hashtree/Gen/ShaniL "$seg"; done
  for seg in head it t1 t0; do lake exe x86loopw Hashtree/Gen/ShaniW "$seg"; done
fi
if want sse_x1; then
  lake exe x86loop1  sse Hashtree/Gen/SseX1L all
  lake exe x86proof1 sse Hashtree/Gen/SseX1P
fi
if want avx_x1; then
  lake exe x86loop1  avx Hashtree/Gen/AvxX1L all
  lake exe x86loop1w avx Hashtree/Gen/AvxX1LW all
  lake exe x86proof1 avx Hashtree/Gen/AvxX1P
fi
if want avx_x4;       then lake exe x86proofv x4  Hashtree/Gen/AvxX4P     --split; fi
if want avx2_x8;      then lake exe x86proofv x8  Hashtree/Gen/Avx2X8P    --split; fi
if want avx512_x16;   then lake exe x86proofv x16 Hashtree/Gen/Avx512X16P --split; fi

# linux/arm64 (the macOS models are identical up to the tail symbol name)
if want sha_x1;   then lake exe armproof sha_x1  2 Hashtree/Gen/ArmShaX1P; fi
if want neon_x1;  then lake exe armproof neon_x1 2 Hashtree/Gen/ArmNeonX1P
                       lake exe armproof neon_x1 0 Hashtree/Gen/ArmNeonX1P0; fi
if want neon_x4;  then lake exe armproof neon_x4 4 Hashtree/Gen/ArmNeonX4P; fi

# linux/riscv64
if want riscv_x1;       then lake exe rvproof x1     Hashtree/Gen/RvX1P; fi
if want riscv_zbb_x1;   then lake exe rvproof zbb    Hashtree/Gen/RvZbbX1P; fi
if want riscv_crypto;   then lake exe rvproof crypto Hashtree/Gen/RvCryptoP; fi

echo "regenerated Hashtree/Gen ($target)"

# Check the certificate that was just produced.  With target=all this builds
# the whole library; with one kernel it builds only its final theorem (plus the
# wrapper modules that depend on it for shani_x2/avx_x1).
case "$target" in
  all)                lake build Hashtree ;;
  shani_x2)           lake build Hashtree.Proofs.ShaniAll Hashtree.Proofs.ShaniW ;;
  sse_x1)             lake build Hashtree.Proofs.SseX1All ;;
  avx_x1)             lake build Hashtree.Proofs.AvxX1All Hashtree.Proofs.AvxX1W ;;
  avx_x4)             lake build Hashtree.Gen.AvxX4P.Final ;;
  avx2_x8)            lake build Hashtree.Gen.Avx2X8P.Final ;;
  avx512_x16)         lake build Hashtree.Gen.Avx512X16P.Final ;;
  sha_x1)             lake build Hashtree.Gen.ArmShaX1P.Final ;;
  neon_x1)            lake build Hashtree.Gen.ArmNeonX1P.Final Hashtree.Gen.ArmNeonX1P0.Final ;;
  neon_x4)            lake build Hashtree.Gen.ArmNeonX4P.Final ;;
  riscv_x1)           lake build Hashtree.Gen.RvX1P.Final ;;
  riscv_zbb_x1)       lake build Hashtree.Gen.RvZbbX1P.Final ;;
  riscv_crypto)       lake build Hashtree.Gen.RvCryptoP.Final ;;
  wrapper_linux_amd64) lake build Hashtree.Proofs.WrapperAmd64 ;;
  go_generic)         lake build Hashtree.GoProof ;;
  go_api)             lake build Hashtree.Glue ;;
esac
echo "checked $target"
