#!/bin/bash
# Regenerate the RV64 programs from the shipped objects (run on the VM, from formal/lean).
# Objects: lib/linux_riscv64/libhashtree.a of hashtree-bindings, extracted to $O.
set -e
O=${O:-/root/ht/objs/linux_riscv64}
D=Hashtree/Kernels/Riscv
mkdir -p $D
gen() { python3 tools/riscv_to_lean.py "$O/$1" "$2" "Hashtree.Kernels.Riscv.$3" > "$D/$3.lean"; }
gen sha256_riscv_x1.o hashtree_sha256_riscv_x1 X1
gen sha256_riscv_zbb_x1.o hashtree_sha256_riscv_zbb_x1 ZbbX1
gen sha256_riscv_crypto.o hashtree_sha256_riscv_crypto Crypto
gen hashtree.o hashtree_hash DispHash
gen hashtree.o init_and_hash DispInitAndHash
gen hashtree.o hashtree_init DispInit
sha256sum "$O"/*.o
