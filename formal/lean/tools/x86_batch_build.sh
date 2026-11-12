#!/bin/bash
# x86b_batch.sh <GenDir> <nslices> <batch>: build split-mode slices B at a time, then Final
d=$1; C=$2; B=$3
cd /root/ht/ws-x86b/formal/lean
export PATH=$HOME/.elan/bin:$PATH
start=$(date +%s)
c=0
while [ $c -lt $C ]; do
  t=""; for i in $(seq $c $((c+B-1))); do [ $i -lt $C ] && t="$t Hashtree.Gen.$d.P$i"; done
  taskset -c 9-17 /usr/bin/time -f "batch $c %e s %M KB" lake build $t 2>&1 | grep -vE "^trace|^⣿"
  c=$((c+B))
done
taskset -c 9-17 /usr/bin/time -f "Final %e s %M KB" lake build Hashtree.Gen.$d.Final 2>&1 | grep -vE "^trace|^⣿"
echo "all $(( $(date +%s) - start )) s"
