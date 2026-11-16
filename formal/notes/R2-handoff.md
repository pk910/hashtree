# R2 handoff (linux/amd64, VM1) — updated 2026-11-16

Written so a successor can continue without the controller transcript.  VM1 is
`root@46.101.165.150`; repo `/root/ht/hashtree`, branch `research/formal-r2-amd64`; scratch
`/root/r2w/`.  Lean commands run from `/root/ht/hashtree/formal/lean` with
`export PATH=/root/.elan/bin:$PATH`; this `lake` has no `-j` flag and ignores CPU affinity
for its job count (cap it with a `systemd-run` cgroup: `MemoryMax`, `CPUQuota`).

Publishing: the VM has no GitHub credentials.  From the control machine:
`git --git-dir=relay-vm1.git fetch root@VM:/root/ht/hashtree research/formal-r2-amd64:research/formal-r2-amd64`
then `git --git-dir=relay-vm1.git push https://github.com/pk910/hashtree research/formal-r2-amd64`
(the control machine has `gh` auth).  Same with `relay-vm1-x8x16.git` for the R2b clone.
Never amend or force-push `research/formal-r2-amd64` (R5 merges it); signature changes to
`x4_runW`/`K201W`/`upd15`/`sIt` must be announced before pushing.

Shell gotcha that cost two cycles: `pkill -f`/`pgrep -f` with a pattern that also occurs in the
ssh command line kills the ssh shell itself; anchor patterns (`^/bin/bash /root/r2w/...`,
`^/root/.elan/toolchains/[^ ]*/bin/lake build ...`).  Do not put Lean text in an unquoted
heredoc inside a single-quoted ssh command (backticks, `σ'`); scp a file instead.

Memory: a global OOM on 2026-11-15 00:46 (a 50 GB single lean compile from another clone)
took the box offline for two hours; a memcg OOM at 11.7 GB killed one pass-1 part under a
too-small `MemoryMax`.  Oleans written without lake's `.trace` files get rebuilt, so keep the
builds under `lake build`, not `lake env lean -o`.

## Landed

* `9a2d747` — `AvxX4X1WAgree.lean`: the `c >= 4` x4 -> x1 edge at the W-mode exit cut behind
  the log (`x4_x1_W`).  R2.md checkpoint (6).
* `3cc8e61` — `Avx2X8Align.lean`: the x8 `and rsp,-32` at `entryW`, residue parameterised
  (`align_hom8`, `run1_align`, `x8A r`), the small path `0 < c < 8` at all 32 residues
  (`smOk_all`), `x8_small_run`, `x8Sm_resume`, `x8Sm_outLogW`, `residue_abi`.
* `9910d41` — `AvxX4Agree.lean`: x4 dead-register analysis from `{rcx, flags}` (`Dsx4`,
  `hsound`, `run_agree4`); `X86Agree.readsOf` no longer lists the flags as read by `cmp`/`test`.
* `f6636f5`, `207b233`, `59b86cb`, `8dcb714` and the loop commit — the x8 W-mode loop:
  `Avx2X8WShift` (rebased pilot cuts per residue, `BODYLEN := 6035`, `KT r`, `KTE r`, `exitGpr`,
  kernel facts for r = 0 and 16), `tools/avx_x8w.py`, the pass-1 parts `Avx2X8WBodyR{0,16}P1..4`
  and compositions `Avx2X8WBodyR{0,16}`, `Avx2X8WStripDefs` (`pushC r`, `m8P r`, `stripK8`,
  `KTs r`/`KHs r`/`KTEs r`, `stripOk r`), `Avx2X8WStrip{0,16}` (one `decide +kernel` each,
  ~4.5 min), the pass-2 parts `Avx2X8WBodyR{0,16}S1..4` and compositions `Avx2X8WBodyR{0,16}S`,
  `Avx2X8WLoop` (residue-generic loop over `CutsW r`/`BodyW r`), `Avx2X8WAll`
  (`x8_runW_last_abi`, `x8_runW_abi`, residue selected by `σ 9 % 16 = 8`).  R2.md section
  "x8 W-mode loop, all counts".  Gate exit 0, audit exit 0, standard axioms plus
  `loadLane_hom._native.bv_decide.ax_1_6`.
* R2b clone (`/root/ht/hashtree-x8x16`, `research/formal-r2b-x8x16`): `45d55df` frames the x16
  loop with the output-only log `OutLogO` (drops `24 ≤ σ 9` from the x16 loop theorems);
  `x8Pre` uses `OutLogO M`; `outLogO_outLog : OutLogO M → OutLog M`.  `AxiomsR2b.lean`: 38
  prints, no sorryAx.  (The x16 `OutOk` lemma is R2c's workstream, VM2.)

* x8 -> x4 hand-off (this commit): `Avx2X8ExitShape` (32x16 vector file at `KTE r`/`KTEs r`),
  `Avx2X8WAt` (`x8_runW_at`/`x8_runW_last_at`: the x8 W-mode runs with the x8 table at a fresh
  region `r8`, by `run_swap_chain`), `AvxX4Agree` (the dead set now also holds `rax`:
  `Dsx4 0 = [0,1,16]`, `raxFree`), `Avx2X8X4WAgree`: the resumed x8 exit cut agrees with the x4
  entry state up to `{rax, rcx}` (`x4cut_agree`, `cutEnv8`), and `x8_x4_W_last/_small/_zero`
  (`c = 8 (j+1) + s`, `s` in [12,16) / [9,12) / 8) and `x8_x4_W1_*` (`8 <= c < 16`): the x8 run to
  its exit cut, then the x4 link to `K201W` (behind the x8 log), its small path (`KSm`), or its
  count-0 return.  Trap found and removed: `x8_runW_at` states its log as `(KTEs r).mem.map …`,
  the goals as `(mapState … (KTEs r)).mem`; passing it unchanged made Lean unfold the cut (each
  theorem > 90 min); `mapState_mem_eq` (generic `rfl`) + `rw` first: the module checks in 23 s.
* Next on amd64: `x8 -> x4 -> x1` (compose with `AvxX4X1WAgree.x4_x1_W` and the x1 small path).

## In flight

* Windows x4 port, clone `/root/ht/hashtree-r5win`, branch `research/formal-r2-winx4` (off
  R5's `ee0bb0c`; R5's pilot sources are read-only for R2).  `d91b49b`:
  `Hashtree/Proofs/WinAvxX4WShift.lean` (`m0W`, `wRegW`, `shiftKW`, `K1W`, `sliceE`/`sliceE1`,
  `KT` 25 steps, `KTE` 37 steps with the avx_x1 tail, `exitGprW`, `tailOk`; 3m07s) and
  `tools/winx4w.py` (emits `WinAvxX4WBodyP1..4` for slices 2..202 with orcs `[1715]` at
  slices 51/83, and `WinAvxX4WBody`).  Facts: 203 pilot slices `K1..K204`, cut pcs K1=9,
  K2=17, K203=4128, K204=4162; the kernel never writes rbx/rbp/rsi/rdi/r10-15; xmm6..15 are
  saved at `[rsp+384..543]` (160 `.dat` cells in every cut's log -- the x8 "spilled cells"
  situation again, so the loop needs the stripped pass-2 cuts: strip the 160 cells plus the
  memory-keyed push list, `wfix` at K2/K3).  Scheduler `/root/r2w/sched8.sh`
  (`r2sched8`, logs `/root/r2w/winbody_P*.log`, `/root/r2w/sched8.log`) builds the four parts
  then the composition.
* Next on amd64: the x8 -> x4 hand-off (`run_agree4` at `KTE r`/`KTEs r`; `cutEnv` for the
  vector lanes as in `AvxX4X1WAgree`), then `x8 -> x4 -> x1`.

## Other

* `/root/ht/hashtree-r2b-int`: source-only worktree of `ebe04b6` (no `.lake`; never hard-link
  `.lake` dirs, lake rewrites oleans in place).
* Untracked in `/root/ht/hashtree`: `Avx512X16Entry.lean` (R2b draft, leave), `lake-manifest.json`.
* Probes: `/root/r2w/WStripProbe.lean` (all 21 strip facts true at both residues, 15 s),
  `/root/r2w/WinX4ShiftProbe*.lean`.
* R5 builds in `/root/hashtree-win`; leave its processes alone.
