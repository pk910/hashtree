#!/bin/bash
# Differential validation of the AArch64 model against the real code under qemu (run on the VM
# from formal/lean after `lake build armcheck` and tools/arm_gen.sh):
#  1. the shipped kernel objects (ar x of the bindings' libhashtree.a) linked into
#     tools/arm_kernel_harness.c, run for counts 0..34 on the inputs armcheck uses, under
#     several qemu CPU models; outputs compared with `armcheck --dumpall linux|mac`;
#  2. per-instruction vectors (tools/arm_insn_diff.py's C program) recorded natively, checked
#     with `armcheck --insn`.
set -e
LIB=${LIB:-/root/ht/hashtree-bindings/lib/linux_arm64/libhashtree.a}
W=${W:-/root/ht/ws-arm/run}
CPUS=${CPUS:-"max cortex-a53 cortex-a72 neoverse-n1 a64fx"}
mkdir -p $W/objs
(cd $W/objs && ar x "$LIB")
aarch64-linux-gnu-gcc -O2 -static -nostdlib -ffreestanding -fno-builtin -I tools tools/arm_kernel_harness.c $W/objs/sha256_armv8_crypto.o \
  $W/objs/sha256_armv8_neon_x1.o $W/objs/sha256_armv8_neon_x4.o -o $W/arm_kernel_harness
.lake/build/bin/armcheck --dumpall linux > $W/model_linux.txt
.lake/build/bin/armcheck --dumpall mac | sed 's/^_//' > $W/model_mac.txt
cmp $W/model_linux.txt $W/model_mac.txt && echo "model: linux and mac objects give identical outputs"
for cpu in $CPUS; do
  if qemu-aarch64-static -cpu $cpu $W/arm_kernel_harness > $W/native_$cpu.txt 2> $W/native_$cpu.err; then
    if cmp -s $W/native_$cpu.txt $W/model_linux.txt; then echo "cpu $cpu: all kernels: $(wc -l < $W/native_$cpu.txt) runs identical to the model"
    else echo "cpu $cpu: MISMATCH"; diff $W/native_$cpu.txt $W/model_linux.txt | head -5; fi
  else
    echo "cpu $cpu: all kernels failed ($(head -c 200 $W/native_$cpu.err)); neon only:"
    qemu-aarch64-static -cpu $cpu $W/arm_kernel_harness hashtree_sha256_neon_x4 hashtree_sha256_neon_x1 > $W/native_${cpu}_neon.txt
    grep -v sha_x1 $W/model_linux.txt | cmp -s - $W/native_${cpu}_neon.txt && echo "  neon kernels identical to the model" || echo "  MISMATCH"
  fi
done
aarch64-linux-gnu-gcc -O1 -static -nostdlib -ffreestanding -fno-builtin -march=armv8-a+crypto -I tools $W/arm_insn.c -o $W/arm_insn
qemu-aarch64-static -cpu max $W/arm_insn ${TRIALS:-300} > $W/insn_vectors.txt
.lake/build/bin/armcheck --insn $W/insn_vectors.txt
