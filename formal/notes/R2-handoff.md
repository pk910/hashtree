# R2 handoff (linux/amd64, VM1) — 2026-11-13

Written so a successor can continue without the controller transcript.  Everything below is
on VM1 (`root@46.101.165.150`), repo `/root/ht/hashtree`, branch `research/formal-r2-amd64`.
Scratch (not in the repo): `/root/r2w/`.  Lean commands run from `/root/ht/hashtree/formal/lean`
with `export PATH=/root/.elan/bin:$PATH`.  `lake` here has no `-j` flag (it uses all cores).

## Branch state

* Head before this note: `779901f` (= `origin/research/formal-r2-amd64` = control relay
  `relay-vm1.git`).  Tree clean except the untracked files below.
* `formal/proofs.json` is identical to HEAD and to `/root/proofs.json.bak`; the earlier
  "uncommitted theorem-ID fix" was another agent's edit, saved to `/tmp/proofs.json.dirty.diff`
  (copied off the VM) and reverted; nothing to preserve.
* `/root/ht/hashtree-x8x16` (R2b, `research/formal-r2b-x8x16`) is at `ebe04b6`, clean, pushed
  to origin and to `relay-vm1-x8x16.git`; its W-mode x16 build (`WBodyV`/`WTurn`/`WLoop`) is
  green (oleans 09:36 postdate the sources).  Nothing left to commit there.
  `/root/ht/hashtree-r2b-int` is a detached worktree of `ebe04b6` (source only; its `.lake`
  was removed — do not hard-link `.lake` dirs between clones, lake may rewrite shared inodes).
* Untracked in `/root/ht/hashtree`:
  - `formal/lean/Hashtree/Proofs/AvxX4X1WAgree.lean` (657 lines, from the crashed session) —
    the framed x4 -> x1 edge at the W-mode exit cut; see "Critical path" below.
  - `formal/lean/Hashtree/Proofs/Avx512X16Entry.lean` — an R2b draft stranded in this clone
    (R2.md already records it); not part of this branch, leave it.
  - `formal/lean/lake-manifest.json` — lake-generated.

## Critical path: `AvxX4X1WAgree.lean` (x4 -> x1 at the W-mode cut, framed route)

Content (all stated, no sorry): `agreeOn_fr` (AgreeOn survives `fr L` on both sides),
`mem_view_eq`/`view_in`/`wfAt_view`/`wfAt_cut` (an `OutLogW` log never shadows the table, the
return marker `σ 9 + k`, or the input: `WfMemAtW` holds at `view L mem0c`), `cutEnv` (memory keys
read the framed memory through the renaming, so `EnvMem` is `rfl`; numbered vars `≥ 100` are
the cut's own vector lanes), `K201L`/`E201L` register lists, `cut_gpr_pointwise`, `x1cut_agree`
(`AgreeOn [0,1,9] (cutBare e' σ') (refCut (swap 4 r) e' σ' mem0c M')`), `resume_cut_fr`/
`run_cut_fr` (`run_fr` at the resumed cut), `x1cut_bridge`/`x1cut_framed` (log-framed
InRange/OutOk/RegsOk post via `AvxX1Agree.correctWAt_agree`), and `x4_x1_W` (the all-count
x4 run `x4_runW` composed with the x1 edge for `c = 4(j+1)+s`).

Shadowing check (the "stop and report" item): `OutLogW` writes are at `rOut` or at `rStack`
strictly below `σ 9`; the x1 kernel reads region `r` (≠ rOut, rStack), `rIn`, and
`rStack, σ 9 + k` with `0 ≤ k < 8`.  No write in L hits a cell the kernel reads — no finding.

Check history:
* The crashed session's check (`lake env lean Hashtree/Proofs/AvxX4X1WAgree.lean`, PID
  428174, log `/tmp/wagree.log`) ran 40 min with no output and died at its `timeout 2400`
  (EXIT=124).
* Bisection (prefix copies `/root/r2w/WA_p1..p4.lean`, logs `WA_p*.log`): lines 1-310 check
  in 34 s, 1-384 and 1-427 in 75 s (EXIT 0).  Lines 1-478 (through `x1cut_agree`) do not
  finish.  Bullet variants (`WA_vA..vF.lean`, each bullet of `x1cut_agree` except the kept
  ones replaced by `sorry` — scratch only): vB (vr), vC (assume+flags), vD (glen), vE (gpr)
  finish in 90-110 s; vF (gpr16) fails only because `omega` does not know `flg = 16`
  (`WA_vF.lean:451:64`, `:452:64`); vA (the five `rfl` bullets pc/halted/tail/err/mem) does
  not finish — `rfl` on `(cutBare e' σ').pc = (refCut …).pc` makes `isDefEq` unify the two
  states first, which unfolds `mapState e' σ' K201W` and evaluates the symbolic exit run
  (`K201W := abstract (run … 27 K200W)`) in the elaborator.
* Fix (scratch `/root/r2w/x1cut_fix.lean`, spliced into the full file as
  `/root/r2w/WA_fix.lean` = repo lines 1-427 + fix + repo lines 478-657): projection lemmas
  `cutBare_{pc,halted,tail,err,mem,assume,vr,gpr}` and `refCut_{…,flags}` stated against
  literals/plain `map`s (each `rfl`, which only reduces the projection), the bullets rewritten
  with them, and `have hf : flg = 16 := rfl` for the gpr16 bullet.  Running:
  `(time timeout 2400 lake env lean /root/r2w/WA_fix.lean) > /root/r2w/WA_fix.log`, EXIT line
  appended at the end.  `WA_vA` is also still running (log `/root/r2w/WA_vA.log`).

On outcome:
* `WA_fix` EXIT 0: copy `/root/r2w/WA_fix.lean` over
  `formal/lean/Hashtree/Proofs/AvxX4X1WAgree.lean`, `lake build Hashtree.Proofs.AvxX4X1WAgree`,
  add `import Hashtree.Proofs.AvxX4X1WAgree` and
  `#print axioms Hashtree.Proofs.AvxX4X1WAgree.x4_x1_W` to `formal/lean/Axioms.lean`
  (R2 block, after the `x4_runW` line), `make gate`, `make audit` (both from `formal/lean`),
  commit ("formal: the x4 -> x1 edge at the W-mode cut behind the log"), push, update R2.md.
* `WA_fix` errors: fix them in `/root/r2w/WA_fix.lean` and re-run; the only unverified parts
  are the new projection lemmas and `x1cut_agree`'s bullets (everything else checked in p4
  and in the full-file tail, which is unchanged).
* If `WA_vA` ever finishes, it only confirms the diagnosis; no action.

## Second thread: the x8 alignment gap (new files, R2-owned)

Problem: `avx2_x8` does `push rbp; mov rbp,rsp; and rsp,-32; sub rsp,928`; at `entryW` the
`and` on `sAt (-8)` throws `"and on symbolic pointer"` (`X86.lean:449`, R2b's
`x8_align_blocked`).  No semantics change is needed.

Design (the R5/`align_hom` treatment ported):
* The alignment is executed *concretely*: `exec` of `and rsp,-32` at `mapState env σ x8P`
  (rsp = integer `σ 9 - 8`) equals `mapState env σ (x8A r)` with
  `x8A r := {x8P with rsp := sAt (-8 - r), flags := none, pc := 7}` and the residue
  `r = (σ 9 - 8) % 32` (`align_hom8`, `run1_align`).  A second stack symbol is impossible:
  `AddrEq Lin` decides addresses by the difference of offsets, so any lookup walking past the
  pushed `rbp` cells with a different stack symbol errors `"may alias"` (the epilogue's
  `pop rbp` would).  Hence one stack symbol and a residue *parameter*, with the post-alignment
  segments checked for every residue (32 for the small path; the loop body for the two the
  wrapper ABI allows, `σ 9 ≡ 8 (mod 16)` ⇒ `r ∈ {0, 16}`, `residue_abi`; the linux wrapper
  itself gives `r = 16`).
* Pilot cuts rebased per residue (`shiftK8 r`, in `Avx2X8WShift.lean`): pilot stack offset
  `k ≥ 16` (pushed rbp, marker) ↦ `sAt (k - 24)`, `k < 16` (frame) ↦ `sAt (k - 8 - r)`;
  `rax`/`rbx`/`r12..r15` ↦ the wrapper's values (`wReg8`, rax on `entryWx`'s symbol 15);
  saved-register cells (pilot `[-32,0)`) and the pushed rbp (`[16,24)`) ↦ pointer bytes.
  Scan facts (`/root/r2w/X8Scan.lean`): the body (pc 17..6069) never writes rax, rbx, r8-r11,
  r12-r15 (written only by the restores 6074-6077, read only by the saves 8-11) and never
  reads rbp; every ymm is loaded before read from pc 15 (`ymm0,1` at 15-16, `ymm2..7` at
  17-22, `ymm8..15` at 24-31).  So the loop head is the rebased `K2` (pc 17) with `ymm2..15`
  fixed to the turn's end values (`KH r`), `K3` (pc 25) with `ymm9..15` fixed (`KH3 r`), and
  the pass-1 cuts from `K4` on — only two slices need a second-pass re-check.
* Validated in the kernel (`/root/r2w/X8Probe.lean`, EXIT 0, 3m20s): the prologue cut,
  the entry slice `x8A r -> shiftK8 r K2` (10 instrs) at r = 0 and 16, body slices 2 and
  100 at r = 0 and 16, and the 14-instruction small path at r = 0 and 5 with
  `gpr = entryWx.gpr`, `vr = entryWx.vr`, a 40-cell log, `tail = some "hashtree_sha256_avx_x4"`.

Files (scratch copies in `/root/r2w/`, to be moved into `formal/lean/Hashtree/Proofs/` and
`formal/lean/tools/` once they elaborate):
1. `Avx2X8Align.lean` — `m8` (chunked wrapper memory, `m8_eq`, `m8_keyed`), `x8P` + facts,
   `alignI8`, `prog_6`, `x8A r`, `align_hom8`, `run1_align`, `orcSm`, `x8Sm r`, `A1Sm`/`asmSm`,
   `smOk r` (slice check + tail/err/halted/pc/gpr/vr/assume/log-shape as one Bool),
   `smOk_all : (List.range 32).all smOk = true` (decide +kernel), `x8Sm_facts`, `residue_lt`,
   `x8_small_run` (from `fr M (mapState env0 σ entryW)`, `0 < c < 8`, 20 instructions reach
   `fr M (mapState e' (upd15 σ) (x8Sm r))`), `x8Sm_resume` (the resumed cut is
   `{mapState e σ entryWx with flags := …}` behind the small path's log), `x8Sm_outLogW`,
   `residue_abi`.  Under check: `(time timeout 1500 lake env lean /root/r2w/Avx2X8Align.lean)
   > /root/r2w/Align.log` (EXIT appended); the suspected slow part is `smOk_all` (32 symbolic
   14-instruction runs, each evaluated several times).  If it times out, split `smOk` into the
   slice check and the facts, or check residues in two halves.
2. `Avx2X8WShift.lean` — the rebasing defs, `A0`/`asmge`, `orcB`/`orcEx`, `tau8`, `KT r`
   (27-instr tail to pc 17), `vfixAt`/`wfixS`, `KH r`, `KH3 r`, `KTE r` (31-instr exit),
   `AT`/`AX`/`asmT`/`asmX`, `exitGpr` (a guess of the exit register file — verify), and 17
   `decide +kernel` facts per residue for r = 0 and 16 (`sliceE_r`, `sliceV2_r`, `sliceV3_r`,
   `sliceT_r`, `sliceX_r`, `KT_shape_r`, `KT_pc_r`, `KT_assume_r`, `KT_logB_r`, `KH_nOnly_r`,
   `KTE_{tail,err,halted,pc,assume,logB,gpr}_r`).  Not yet run; needs `Avx2X8Align` built
   first.  `/root/r2w/WShiftProbe.lean` is the same file with `#eval`s of each fact (fast
   feedback on which conjunct fails); run it first.  Also needs `def BODYLEN : Nat := 6035`
   added (the loop file uses it; the generator states the body runs with it).
3. `avx_x8w.py` (→ `formal/lean/tools/`) — emits `Hashtree/Proofs/Avx2X8WBodyR{r}P1..P4.lean`
   (slices 2..209 at the rebased cuts, four files for parallel `lake build`) and
   `Avx2X8WBodyR{r}.lean` (env chains `G2..G210`, `GV2..GV210`, `body_runW`, `body_memW`,
   `bodyV_runW`, `bodyV_memW`).  Usage `python3 tools/avx_x8w.py 0` and `… 16`.  Its proofs
   use `BODYLEN` unfolded by `rw [show BODYLEN = <nested sum> from rfl]` — add that line
   (or state with the nested sum) before generating.  Slice table in `/root/r2w/x8slices.json`.
   Expected cost ~25 s per slice check, 416 checks, 8 files in parallel.
4. `Avx2X8WLoop.lean` (draft, residue-generic over bundles `CutsW r` / `BodyW r`):
   `tau8_*`, `sIt8`, `outLogW_of_logB`, `TURNLEN := BODYLEN + 27`, `entry_runW` (16 instrs),
   `turn_stepW`, `turn_runW`, `iter_stepW`, `loopW`, `final_runW`, `first_exitW`,
   `first_turnW`, `x8_runW_last` (`8 ≤ c < 16`), `x8_runW` (`c = 8(j+1)+s`).  Untested; the
   per-residue instantiation files (`cutsW_0 : CutsW 0 := ⟨sliceE_0, …⟩`, `bodyW_0`) are
   still to be written.
5. After the loop: the x8 -> x4 hand-off needs x4's dead-register contract (`rcx` and the
   flags differ at `KTE r`; everything else is `entryWx` with rsi/rdi/rdx advanced —
   `exitGpr`), i.e. an `AvxX1Agree`-style `Dsx` table for the x4 program, and the vector lanes
   handled by a `cutEnv` as in `AvxX4X1WAgree`.

## Other running/background items

* `make audit` log `/root/r2w/audit_bg.log` (exit 0, no sorryAx); warm `lake build` of the
  R2 modules (`/root/r2w/warm_bg.log`) — the first attempts used a non-existent target name
  (`AvxX4Small` is a namespace in `AvxX4Entry.lean`); relaunched with `AvxX4Entry`.
* R5's SseX1L build in `/root/hashtree-win` is what drives the load (~30-45); leave it.
