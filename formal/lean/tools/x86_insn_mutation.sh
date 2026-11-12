#!/bin/bash
# Mutation sanity check of the x86 per-instruction differential test (run on the VM, after
# x86_insn_run.sh has produced <build>/zmm.native.txt).  Applies one deliberate bug to the
# workspace's Hashtree/Asm/X86.lean, rebuilds x86insncheck, reruns the model (zmm view, all
# tests), compares with the recorded SDE vectors, then restores X86.lean and rebuilds.
#
#   x86_insn_mutation.sh <formal/lean dir> <build dir> <mutation> [form trials] [kernel trials] [jobs]
#
# mutations:
#   palignr   palignrL, dword-aligned case: `j < 8` -> `j < 7` (drops the top dword of hi)
#   palignr1  palignrL, byte case: shift one byte too far (`4 * i + imm` -> `4 * i + 1 + imm`)
#   rnds2     rnds2: the two WK words swapped (wk0 <-> wk1)
#   legacy    pblendw writes as VEX (zeroes lanes 4..15 instead of keeping them)
set -e
LEAN=$(realpath "$1"); B=$(realpath "$2"); MUT=$3; T1=${4:-500}; T2=${5:-300}; J=${6:-6}
F=$LEAN/Hashtree/Asm/X86.lean
python3 "$LEAN/tools/x86_insn_diff.py" lean "$B" "$LEAN/X86InsnCheck.lean" > /dev/null
grep -q x86insncheck "$LEAN/lakefile.toml" || printf '\n[[lean_exe]]\nname = "x86insncheck"\nroot = "X86InsnCheck"\n' >> "$LEAN/lakefile.toml"
cp "$F" "$B/X86.lean.orig"
restore() { cp "$B/X86.lean.orig" "$F"; (cd "$LEAN" && lake build x86insncheck 2>&1 | tail -1); }
trap restore EXIT
python3 - "$F" "$MUT" <<'EOF'
import sys
f, mut = sys.argv[1], sys.argv[2]
s = open(f).read()
rep = {
  'palignr': ('else if j < 8 then hi.getD (j - 4)', 'else if j < 7 then hi.getD (j - 4)'),
  'palignr1': ('ofBytes (catByte hi lo (4 * i + imm))', 'ofBytes (catByte hi lo (4 * i + 1 + imm))'),
  'rnds2': ('let wk0 := g k 0; let wk1 := g k 1', 'let wk0 := g k 1; let wk1 := g k 0'),
  'legacy': ('pure (setVec s false 4 d (pblendwL', 'pure (setVec s true 4 d (pblendwL'),
}[mut]
assert s.count(rep[0]) == 1, rep[0]
open(f, 'w').write(s.replace(rep[0], rep[1]))
print('mutation %s: %r -> %r' % (mut, rep[0], rep[1]))
EOF
(cd "$LEAN" && lake build x86insncheck 2>&1 | tail -1)
X=$LEAN/.lake/build/bin/x86insncheck
cd "$B"
N=$(python3 -c "import json;print(len(json.load(open('tests.json'))))")
NF=$(python3 -c "import json;print(sum(x['group']!='kernel' for x in json.load(open('tests.json'))))")
read _ B1 B3 B4 < zmm.native.txt
pids=(); i=0
step=$(( (NF + J - 1) / J )); for ((a=0; a<NF; a+=step)); do
  "$X" "$T1" "$B1" "$B3" "$B4" "$a" "$((a+step-1 < NF-1 ? a+step-1 : NF-1))" > "mut.$i" & pids+=($!); i=$((i+1)); done
for p in "${pids[@]}"; do wait "$p"; done; pids=()
step=$(( (N - NF + J - 1) / J )); for ((a=NF; a<N; a+=step)); do
  "$X" "$T2" "$B1" "$B3" "$B4" "$a" "$((a+step-1 < N-1 ? a+step-1 : N-1))" > "mut.$i" & pids+=($!); i=$((i+1)); done
for p in "${pids[@]}"; do wait "$p"; done
cat $(for ((k=0; k<i; k++)); do echo "mut.$k"; done) > "mut.$MUT.model.txt"; rm -f mut.[0-9]*
set +e
python3 "$LEAN/tools/x86_insn_compare.py" tests.json zmm.native.txt "mut.$MUT.model.txt" --label "mutation $MUT vs SDE" > "mut.$MUT.report.txt"
echo "compare exit $? (1 = mutation detected)"
grep -v '^    ' "mut.$MUT.report.txt" | grep -v '(probe)' | head -40
