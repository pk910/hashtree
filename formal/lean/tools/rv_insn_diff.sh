#!/bin/bash
# Per-instruction differential test (VM, from formal/lean): qemu executes every modelled data
# instruction form on edge-case/random operands; rvcheck --insn recomputes them with the model.
set -e
W=${W:-/tmp/rv_insn}
mkdir -p $W
python3 tools/rv_insn_gen.py > $W/rv_insn.c
riscv64-linux-gnu-gcc -march=rv64gc_zbb_zk -mabi=lp64d -O1 -ffreestanding -fno-stack-protector -nostdlib -static -no-pie \
  $W/rv_insn.c -o $W/rv_insn
qemu-riscv64-static -cpu rv64,zbb=true,zbkb=true,zknh=true $W/rv_insn > $W/qemu.txt
cut -d' ' -f1-4 $W/qemu.txt | .lake/build/bin/rvcheck --insn > $W/model.txt
echo "$(wc -l < $W/qemu.txt) qemu results, $(wc -l < $W/model.txt) model results"
if cmp -s $W/qemu.txt $W/model.txt; then echo "per-instruction differential: all equal"; else
  diff $W/qemu.txt $W/model.txt | head -20; echo "per-instruction differential: MISMATCH"; exit 1; fi
cut -d' ' -f1 $W/qemu.txt | sort | uniq -c | tr '\n' ' '; echo
