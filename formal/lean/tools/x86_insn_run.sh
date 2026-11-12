#!/bin/bash
# Per-instruction differential test of the x86 model, end to end (run on the x86 VM).
#
#   x86_insn_run.sh <formal/lean dir> <build dir> <sde64> [form trials] [kernel-text trials] [jobs]
#
# 1. generate the harness (x86_insn_diff.py gen), assemble and link it (one binary, ymm and zmm modes);
# 2. translate the assembled test instructions into X86InsnCheck.lean, build `x86insncheck`
#    (the lakefile of this workspace gets the exe target if it lacks it);
# 3. run natively on this CPU (ymm view, AVX-512 tests skipped) and under Intel SDE -spr (zmm view,
#    all tests); run the model for both views with the matching buffer addresses;
# 4. compare (x86_insn_compare.py), and compare SDE with the CPU on the common view.
set -e
LEAN=$(realpath "$1"); B=$(realpath -m "$2"); SDE=$(realpath "$3")
T1=${4:-500}; T2=${5:-300}; J=${6:-6}
TOOLS=$LEAN/tools
mkdir -p "$B"; cd "$B"
python3 "$TOOLS/x86_insn_diff.py" gen "$B"
gcc -c x86_insn_tests.S -o x86_insn_tests.o
gcc -O1 -static -no-pie -I"$B" "$TOOLS/x86_insn_harness.c" x86_insn_tests.o -o x86_insn
python3 "$TOOLS/x86_insn_diff.py" lean "$B" "$LEAN/X86InsnCheck.lean"
grep -q x86insncheck "$LEAN/lakefile.toml" || printf '\n[[lean_exe]]\nname = "x86insncheck"\nroot = "X86InsnCheck"\n' >> "$LEAN/lakefile.toml"
(cd "$LEAN" && lake build x86insncheck 2>&1 | tail -2)
X=$LEAN/.lake/build/bin/x86insncheck
N=$(python3 -c "import json;print(len(json.load(open('tests.json'))))")
NF=$(python3 -c "import json;print(sum(x['group']!='kernel' for x in json.load(open('tests.json'))))")
echo "tests: $N (form tests 0..$((NF-1)) x $T1 trials, kernel texts $NF..$((N-1)) x $T2 trials)"

# chunks: (first last trials)
CH=()
step=$(( (NF + J - 1) / J )); for ((a=0; a<NF; a+=step)); do CH+=("$a $((a+step-1 < NF-1 ? a+step-1 : NF-1)) $T1"); done
step=$(( (N - NF + J - 1) / J )); for ((a=NF; a<N; a+=step)); do CH+=("$a $((a+step-1 < N-1 ? a+step-1 : N-1)) $T2"); done

run_view() {  # view: ymm | zmm
  local view=$1 i=0 pids=()
  rm -f "$view".native.* "$view".model.*
  for c in "${CH[@]}"; do
    set -- $c
    if [ "$view" = ymm ]; then ./x86_insn ymm "$3" "$1" "$2" > "$view.native.$i" &
    else "$SDE" -spr -- ./x86_insn zmm "$3" "$1" "$2" > "$view.native.$i" & fi
    pids+=($!); i=$((i+1))
  done
  for p in "${pids[@]}"; do wait "$p"; done
  read _ B1 B3 B4 < "$view.native.0"
  i=0; pids=()
  for c in "${CH[@]}"; do
    set -- $c
    if [ "$view" = ymm ]; then "$X" "$3" "$B1" "$B3" "$B4" --ymm "$1" "$2" > "$view.model.$i" &
    else "$X" "$3" "$B1" "$B3" "$B4" "$1" "$2" > "$view.model.$i" & fi
    pids+=($!); i=$((i+1))
    if (( ${#pids[@]} >= J )); then wait "${pids[0]}"; pids=("${pids[@]:1}"); fi
  done
  for p in "${pids[@]}"; do wait "$p"; done
  for ((k=0; k<i; k++)); do read _ a b c < "$view.native.$k"; [ "$a $b $c" = "$B1 $B3 $B4" ] || { echo "bases differ"; exit 1; }; done
  cat $(for ((k=0; k<i; k++)); do echo "$view.native.$k"; done) | awk 'NR==1 || $1!="bases"' > "$view.native.txt"
  cat $(for ((k=0; k<i; k++)); do echo "$view.model.$k"; done) > "$view.model.txt"
  rm -f "$view".native.[0-9]* "$view".model.[0-9]*
}
time run_view ymm
time run_view zmm
set +e
python3 "$TOOLS/x86_insn_compare.py" tests.json ymm.native.txt ymm.model.txt --ymm --label "native AMD EPYC Milan (ymm0-15)" --summary ymm.summary.json > ymm.report.txt; r1=$?
python3 "$TOOLS/x86_insn_compare.py" tests.json zmm.native.txt zmm.model.txt --label "Intel SDE -spr (zmm0-31)" --summary zmm.summary.json > zmm.report.txt; r2=$?
python3 "$TOOLS/x86_insn_compare.py" --cross tests.json ymm.native.txt zmm.native.txt > cross.report.txt; r3=$?
cat ymm.report.txt zmm.report.txt cross.report.txt | grep -v '^    ' | head -80
echo "exit: milan=$r1 sde=$r2 cross=$r3"
