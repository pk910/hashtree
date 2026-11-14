# R2 handoff (linux/amd64, VM1) — updated 2026-11-14

Written so a successor can continue without the controller transcript.  VM1 is
`root@46.101.165.150`; repo `/root/ht/hashtree`, branch `research/formal-r2-amd64`; scratch
`/root/r2w/`.  Lean commands run from `/root/ht/hashtree/formal/lean` with
`export PATH=/root/.elan/bin:$PATH`; this `lake` has no `-j` flag.

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

## Landed

* `9a2d747` — `Hashtree/Proofs/AvxX4X1WAgree.lean`: the `c >= 4` x4 -> x1 edge at the W-mode
  exit cut behind the log (`x4_x1_W`).  R2.md checkpoint (6).  Lessons: never `rfl` a field
  goal of a computed cut (`K201W`); the file's `wAllSteps` had the wrong step count.
* `3cc8e61` — `Hashtree/Proofs/Avx2X8Align.lean`: the x8 `and rsp,-32` at `entryW`, residue
  parameterised (`align_hom8`, `run1_align`, `x8A r`), the small path `0 < c < 8` at all 32
  residues (`smOk_all`, 2 min in the kernel), `x8_small_run`, `x8Sm_resume`, `x8Sm_outLogW`,
  `residue_abi`.  R2.md section "x8 alignment".  Both: gate exit 0, audit exit 0, standard
  axioms + generated `*_native.bv_decide.ax_*` only.
* R2b clone (`/root/ht/hashtree-x8x16`, `research/formal-r2b-x8x16`): `45d55df` frames the x16
  loop with the output-only log `OutLogO` (WTurn/WLoop), dropping `24 ≤ σ 9` from
  `iter_step`, `exit_step`, `loop`, `x16_loop`, `x16_all`, `x16_chain_head`, `x16_all_region`;
  `x8Pre` uses `OutLogO M`; `outLogO_outLog : OutLogO M → OutLog M`.  Names and the `steps`
  arithmetic unchanged.  `AxiomsR2b.lean` audit: 38 prints, no sorryAx.

## In flight: the x8 W-mode loop (R2-owned files, repo `Hashtree/Proofs/`)

Files in the repo (uncommitted until the pipeline is green): `Avx2X8WShift.lean`
(rebasing `shiftK8 r`, `A0`/`asmge`, `tau8`, `BODYLEN := 6035`, `KT r`, `KH r`, `KH3 r`,
`KTE r`, `AT`/`AX`, `exitGpr`, 15 kernel facts per residue for r = 0 and 16),
`tools/avx_x8w.py` (generator), the generated `Avx2X8WBodyR{0,16}P{1..4}.lean` (208 body
slices per residue at the rebased cuts) and `Avx2X8WBodyR{0,16}.lean` (`body_runW`,
`body_memW`, `bodyV_runW`, `bodyV_memW`).  Scratch: `/root/r2w/Avx2X8WLoop.lean` (the
residue-generic loop over bundles `CutsW r`/`BodyW r`), `/root/r2w/WShiftProbe.lean`.

Pipeline `/root/r2w/x8chain2.sh` (running; logs `/root/r2w/wshift_build.log`,
`/root/r2w/x8body_build.log`, done marker `/root/r2w/x8chain.log`): `lake build
Hashtree.Proofs.Avx2X8WShift`, then the ten body modules (lake runs the eight slice files in
parallel; ~25 s per slice check, 416 checks).

Probe result (`/root/r2w/wshift_probe.log`): every fact true at both residues except
`KT_shape : {KT r with mem := [], assume := []} = (KH r).substL tau8`, which is FALSE and was
removed from the shift file.  Cause (a design point, not a typo): x8 pushes `rbp` and spills
`r12..r15`, so the body head `K2` carries those 40 pointer-byte cells in its own log, while
`mapState_reached`-style framing (x4's `KHL2_shape`, x16's `KT_shape`) needs an empty-log
head.  Decided design for the loop (not yet written):

* pass 1 (entry -> `K2` -> ... -> `K210`) keeps the pilot cuts as they are (the cells are in
  the cuts' logs); the pass-1 slice checks being built are correct for it;
* passes >= 2 use cuts with the 40 cells stripped from the log (`K.mem.take (len - 40)`; the
  cells are the oldest entries) and the symbolic memory `mem0qW 4 roC (pushC r)` whose `push`
  list places the 40 cells at `sAt (-8 + i)` (pushed rbp, `pb ⟨rStack, sym 6⟩ i`) and
  `sAt (-40 - r + 8 j + i)` (saved `r12..r15`, `pb` of the `wReg8` pointers); the head is
  `KH r` stripped, and `KT_shape` holds there.  This costs a second set of 208 slice checks per
  residue (BodyV-style) plus `WfMemW rodata (pushC r)` for the viewed memory after pass 1 —
  derivable because the entry slice writes exactly those cells and every later write is an
  output cell or a frame cell below `sAt (-40 - r)` (refine `OutLogW` with that bound);
* alternatively, prove the generic "`fr C` splits a cut whose log ends in `C`" lemma
  (`mapState_split`) and a `view` commutation for disjoint logs; judged more proof work.

Loop draft `/root/r2w/Avx2X8WLoop.lean` assumes `KT_shape` in `CutsW`; adjust it to the
stripped head.  It already frames with R2's `OutLogW σ` (no `24 ≤ σ 9`).

After the loop: the x8 -> x4 hand-off needs x4's dead-register contract (`rcx` and the flags
differ at `KTE r`; everything else is `entryWx` with rsi/rdi/rdx advanced = `exitGpr`), i.e. an
`AvxX1Agree`-style `Dsx` table for the x4 program, plus a `cutEnv` for the vector lanes as in
`AvxX4X1WAgree`.

## Other

* `/root/ht/hashtree-r2b-int`: source-only worktree of `ebe04b6` (no `.lake`; never hard-link
  `.lake` dirs, lake rewrites oleans in place).
* Untracked in `/root/ht/hashtree`: `Avx512X16Entry.lean` (R2b draft, leave), `lake-manifest.json`.
* R5 builds in `/root/hashtree-win`; leave its processes alone.
