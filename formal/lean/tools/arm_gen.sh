#!/bin/bash
# Generate the AArch64 kernel programs from the shipped objects (run on the VM, from formal/lean):
#   tools/arm_gen.sh [objs-dir]      (default /root/ht/objs)
# Linux ELF objects -> Hashtree/Kernels/Arm, macOS Mach-O objects -> Hashtree/Kernels/ArmMac,
# and the ArmInsnTests table + C program of the per-instruction differential test.
# Cross-checks: each ELF object is also translated from llvm-objdump's disassembly, and the
# Mach-O translation is compared with the ELF one (the instruction terms must be identical).
set -e
OBJS=${1:-/root/ht/objs}
mkdir -p Hashtree/Kernels/Arm Hashtree/Kernels/ArmMac
TMP=$(mktemp -d)
gen() {  # object symbol leanname
  local o=$1 s=$2 n=$3
  python3 tools/arm_to_lean.py "$OBJS/linux_arm64/$o" "$s" "Hashtree.Kernels.Arm.$n" > "Hashtree/Kernels/Arm/$n.lean"
  python3 tools/arm_to_lean.py --llvm "$OBJS/linux_arm64/$o" "$s" "Hashtree.Kernels.Arm.$n" > "$TMP/$n.llvm.lean"
  python3 tools/arm_to_lean.py "$OBJS/darwin_arm64/$o" "_$s" "Hashtree.Kernels.ArmMac.$n" > "Hashtree/Kernels/ArmMac/$n.lean"
  terms() { grep -E '^  \.' "$1" | sed -E 's/  -- .*//; s/"_hashtree/"hashtree/'; }
  cmp <(terms "Hashtree/Kernels/Arm/$n.lean") <(terms "$TMP/$n.llvm.lean") || { echo "GNU/LLVM mismatch $n"; exit 1; }
  cmp <(terms "Hashtree/Kernels/Arm/$n.lean") <(terms "Hashtree/Kernels/ArmMac/$n.lean") || { echo "ELF/Mach-O mismatch $n"; exit 1; }
  cmp <(grep '^def rodata' "Hashtree/Kernels/Arm/$n.lean") <(grep '^def rodata' "Hashtree/Kernels/ArmMac/$n.lean") || { echo "rodata mismatch $n"; exit 1; }
  echo "$n: $(terms Hashtree/Kernels/Arm/$n.lean | wc -l) instructions"
}
gen sha256_armv8_crypto.o hashtree_sha256_sha_x1 ShaX1
gen sha256_armv8_neon_x4.o hashtree_sha256_neon_x4 NeonX4
gen sha256_armv8_neon_x1.o hashtree_sha256_neon_x1 NeonX1
python3 tools/arm_insn_diff.py Hashtree/Asm/ArmInsnTests.lean "$TMP/arm_insn.c"
mkdir -p /root/ht/ws-arm/run
cp "$TMP/arm_insn.c" /root/ht/ws-arm/run/arm_insn.c
rm -rf "$TMP"
