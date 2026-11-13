# R5 windows/amd64 handoff (refreshed at each commit)

Branch `research/formal-r5-windows`, VM1 clone `/root/hashtree-win` (R2 drives `/root/ht/hashtree`;
do not touch).  Pushes go through the control-machine relay (`relay-vm1-win.git`: fetch from the VM
over ssh, push to GitHub); the VM has no GitHub credentials.  Logs: `results/r5-windows-log.md`
(control machine, commit-by-commit) and `formal/notes/R5.md` (sections 17-18 are the current work).

## Proved (head of this file's commit)

* `Asm/RunAgree` (25399bc): `Agree R s1 s2`, `exec_agree` (all 46 `Instr`), `run_agree` with the
  per-pc certificate `Cert prog L`, `certB`/`Cert_of_certB`, `live` (R5.md §18).  Axioms standard.
* `Asm/BodyReads` completed scan (`test/shl/bswap/push/pop/ret`, index registers) — same commit.
* `WinShaniSeedAlign` §Live (21944b5): `shani_linux_cert`, `shani_windows_cert`,
  `shani_linux_live_entry_eq : linuxLive.getD 1 [] = [2,6,4,7]`, `shani_windows_live_entry_eq :
  winLive.getD 11 [] = [8,2,4,1]`, inclusions `shani_linux_live_entry`/`shani_windows_live_entry`.
* Entry live sets of all six windows kernels (= rbw tables): R5.md §18 table.
* ba279c6: linear certificate walk (`certAux`, reversed-list sweep; shani build 3m07s -> 20s);
  `Proofs/WinAvx512Live`, `Proofs/WinAvxX4Live` (`cert`, `live_entry` for [8,4,2,1] / [8,4,9,2,1]).
* `Asm/RunExit` (this commit): `exec_shape`, `run_err_none`, `run_exit` (`Body prog lo hi` →
  exit fuel `n ≤ N` with pc = hi unhalted, inside before), `run_preserve` (never-written register),
  `run_nowrite` (non-writing segment keeps the log).  These give `shani_call`'s `hcond`/`hpc`/`hnh`,
  `RegsOkW`'s callee-saved preservation, and the linux tail `add rsp,88; ret` leaving `mem` alone.

## Checkpoint (a): DONE — module `Proofs/WinShaniBridge.lean`

`shani_KSpecW : KSpecW winProg Kernels.X86Win.Shani.rodata stepsW 248` and `fitsW_shani : FitsW
.shani` (stepsW c = ShaniW.steps c + 22).  `call` instantiates `WinShaniCall.shani_call` (hv via
`loadLanes_ok` on rodata, hx, hvlen, hret via `loadVal_marker` on the return marker, hW/hmem from
`InRange` + the save-log bounds, hcond/hpc/hnh/hrsp from `exit`).  Axioms: standard + the
certificate's allowlisted bv_decide axioms (inherited from ShaniW.correctW / run_hom).

Next (thread 2): chain-aware `KSpecC` for avx512_x16 and avx_x4 via `X86Chain` with the same
recipe (their `Live` certificates exist); then avx2_x8 (push-saving, frame-slot design first).

## Checkpoint (a) history — module `Proofs/WinShaniBridge.lean`

Landed: `seed_agree` (Agree [2,6,4,7] between `s0` = seed without the save log and the
certificate's one-step state, via `run_hom` on the symbolic `E1`), `cert` (correctW at `view M m`
transferred to the seed run by `run_agree`), `exit` (`run_exit`/`run_preserve`/`run_tail` + the
two-step tail at 669/670 via `exec_shape`: the exit fuel `n ≤ N`, rsp and {8,3,12,13,14,15}
intact, `finS.mem = (run n s0).mem`).  Next: `shani_call` instantiation (hv/hx/hvlen/hret
helpers are in the file: `loadLanes_ok`, `loadVal_marker`, `entryWin_getV_len`), then
`KSpecW winProg rodata stepsW 248` with `stepsW c := ShaniW.steps c + 22` and `FitsW .shani`.

## The bridge recipe (as implemented)

Recipe fixed (see R5.md §18 follow-up when written): `s0 := {seedSt st a with mem := []}`,
`seedSt st a = fr M s0` with `M := saveLog st (a-248) 10 []`; `run_fr` moves `M` into `view M mem0c`;
certificate side `w1 := run linuxProg 4 (view M mem0c) orc 1 (mapState e σ' entryW)` computed by
`run_hom` (X86RunHom) from the symbolic 1-step state; `e` := env on `.n` keys, `cellX (view M
mem0c ⟨r, off.eval σ'⟩)` on `.m` keys (so `EnvMem` holds by construction; `ShaniW.wfW_view` gives
`WfMemW` under the view from `OutLogW (σ 9) M`); `run_agree shani_linux_cert` + `run_exit` with
`Body linuxProg 1 669` (decide) + `run_preserve` for rsp and {8,3,12,13,14,15} (decide: never
written in the body) + `run_nowrite` for pcs 669/670; then `WinShaniCall.shani_call` (not
`shani_call_mem`: its `NoStackVal` hypothesis fails at `entryWin`, rbx/rbp are stack pointers),
steps_w c := ShaniW.steps c + 22, extra fuel absorbed by `run_halted`.

With `st := mapState env σ WinWrapper.entryWin`, `a := ⟨rStack, σ 9⟩`, the linux body seed is
`WinShaniCall.seedSt st a` (linux numbering, pc 1, rsp = a-88, mem = windows save log
`saveLog st (a-248) 10` on top of `st.mem`).  The certificate side is
`run linuxProg 4 mem0c orc 1 (mapState e σ' X86SymW.entryW)` (pc 1 after `sub rsp, 88`).

1. `seed_agree_entryW`: for the relabelling `σ' 0 = σ 0, σ' 1 = σ 1, σ' 2 = σ 2, σ' 9 = σ 9` and
   `e` = `env` on the `vId` symbols (vector files are literally equal),
   `Agree [2, 6, 4, 7] {seedSt st a with mem := st.mem} (run linuxProg 4 mem0c orc 1 (mapState e σ' entryW))`
   — registers 2/6/4/7 by `seedSt_getG` + `mapState_getG` (as in `seed_gpr*`), the frame by
   unfolding; `st.mem` vs `[]`: `entryWin.mem = []`?  check; otherwise carry it as a log `M`.
2. The save log: `run prog ro mem0 n (fr M s0) = fr M (run prog ro (view M mem0) n s0)` via
   `X86Frame.run_fr` (read its exact hypotheses first) so that `run_agree` runs both states on the
   same memory; then `correctW` must be instantiated at `mem0c := view M mem0` — check that
   `WfMemW`/`EnvMem` are insensitive to the save-area cells `[σ9-248, σ9-88)`.
3. `run_agree shani_linux_cert` with `h : Agree (linuxLive.getD 1 []) ...` from (1) +
   `shani_linux_live_entry` (Agree.mono) gives agreement of the two runs on halted/err/tail/mem/pc
   for every fuel; `correctW` then transfers `OutOk`/`InRange`/halted/err/tail to the seed run.
4. Feed the seed-run facts to `WinShaniCall.shani_call_run` / `shani_call` (its hypotheses are the
   body-run facts), package as `KSpecW winProg rodata steps 248` (WinWrapper.KSpecW) and
   `FitsW .shani`.  Commit the bridge (1-3) before packaging (4).

## Thread 2 (parallel): avx512_x16 and avx_x4 (push-free)

`live`/`certB` modules per program (`Proofs/WinAvx512Live.lean`, `Proofs/WinAvxX4Live.lean`),
entry sets `[8,4,2,1]` and `[8,4,9,2,1]`; then chain-aware `KSpecC` (X86Chain) + `FitsW`.
Certificates landed (ba279c6); next is the chain-aware `KSpecC` per link (X86Chain) using the
same bridge recipe as shani, with the chain's `tail` handling.

## Deferred

sse_x1 / avx_x1 / avx2_x8: entry sets contain the push-saved callee-saved registers; the bridge
needs memory agreement outside the kernel frame plus a frame-slot liveness certificate (slots
keyed by rsp-relative offset; pushes/pops as slot writes/reads).  Design to be reported before
proving; if rsp-relative keying is awkward (rsp moves in the body) fall back to the fixed-rsp
bodies first.

## Running on VM1 (check `ps`; never pkill)

* certificate-module builds for the five non-shani bodies: PID 434086, `/tmp/build_certs.log`.
* x86check baseline at 66eb579: done, `/tmp/x86check_66eb579.log` (failures 0, 4m22s).
* `make audit` (full Axioms.lean) is blocked by missing oleans of unrelated linux modules
  (`WrapperAmd64`, ...); audit new names through a scratch import file.

## Thread 2 design (to be checked before proving)

### Chain links: statement shape (`Proofs/WinAvx512Bridge.lean`, definitions only)

`KSpecC512 s512 env σ m0 orcC c inp` (compiled, see the module): under the `KSpecW` memory
hypotheses, from `s = mapState env σ entryWin`, after `s512 c` steps: `err = none` and either
`c = 0 ∧ tail = none ∧ PostLink σ c inp 0 f` (the kernel returns at pc 3 without writing) or
`c ≠ 0 ∧ tail = some "hashtree_sha256_avx2_x8" ∧ PreLink env σ c (c - c%16) (c%16) inp L8
(resume f)`.  `KSpecC512_head` shows this is exactly the head clause of `X86Chain.KSpecC` for
`winSpecs` with `P512 := (· = mapState env σ entryWin)`, `Q512 := PostLink σ c inp 0`,
`P8 := PreLink env σ c (c - c%16) (c%16) inp L8`.

* `PostLink σ c inp D f := halted ∧ Foot (σ 9) D (σ 1) (32c) f.mem ∧ OutOk inp (σ 1) c f.mem ∧
  RegsOkW σ f` — the `KSpecW` conclusion, so a chain-aware `FitsW` is `∃ D, ChainPost ⊆ PostLink D`.
* `PreLink env σ c d r L s := ∃ e' M', SameG env e' ∧ Agree L {s with flags := none}
  (fr M' (mapState e' (shift σ d r) entryWin)) ∧ OutLogW (σ 9) M' ∧ Foot (σ 9) 0 (σ 1) (32c) M' ∧
  OutOk inp (σ 1) d M'`: on the next link's entry live set `L` the handed state is the wrapper call
  state with the symbols advanced (`shift`: input +64d, output +32d, count r), under a free vector
  environment (U6; `entryWin`'s lanes are distinct symbols so any vector file is an instance),
  over the output log so far.  Scratch registers (which may hold rodata pointers, not
  representable as `entryWin` numbers) are outside `L`, which is why the pre is an `Agree` and not
  an equality.  Flags: every kernel sets them before reading; implementation plan: a flags
  pseudo-register `FL` (16) in `srcs`/`dsts` (`jcc`/`jccTail` read it; `cmp`/`test`/`sub`/`alu`/
  `ror`/`shld`/`shl` write it) and `Agree L` compares flags iff `FL ∈ L` — a small, contained
  generalisation of `RunAgree`; then `{s with flags := none}` disappears from `PreLink`.
* Next-link entry: the avx2_x8 link's own bridge starts from `PreLink … L8` by `run_agree` on `L8`
  (= `WinAvx2X8Live.live_entry`), exactly as the shani bridge starts from `seed_agree`.

Dependency: the linux per-link certificate of the avx512 loop for an arbitrary count (the
loop composition of `Avx512X16Body.body_run` + the `jb` tail with the residual, + the `c = 0`
early `ret`) is R2's active work (`/root/ht/hashtree`: `Avx512X16Entry`, `AvxX4LoopWAll`,
`AvxX4ToX1`, `AvxX4X1WAgree`, head b7857ec).  The windows link proof is: `win_transfer`
(avx512 is a pure renaming, no prologue, no rsp) + `Agree` on `[2,4,6,7]`-renamed entry set
between the renamed wrapper state and the linux certificate start state (the 3-step `test/je`
prefix handled symbolically so that `rsp` leaves the live set), then `run_agree` + the linux
link certificate.  Not started until the linux link lands (or is merged from R2's branch).

### Frame-slot certificate (push-saving bodies: sse_x1, avx_x1, avx2_x8)

Problem: `push r` / `mov [rsp+k], r` of a callee-saved register makes its entry value flow into
a frame cell; with full-memory `Agree` that is a read, and the entry sets contain the callee-
saved registers.  The value flows only cell → matching `pop`/restore → the same register, and
the caller observes exactly "restored".

Design (decidable from the stream, checked by `decide +kernel`):

1. **Static rsp map.** For every pc, `rsp = base + δ(pc)` with `base ∈ {E, A}`: `E` the entry
   rsp, `A` the aligned base after `and rsp, -32` (avx2_x8 only).  Every rsp writer in the three
   streams is `push`/`pop`/`sub rsp, imm`/`add rsp, imm`/`mov rbp, rsp`/`mov rsp, rbp`/`and rsp,
   -32` (the scans `*_rsp_balanced`, `avx2x8_rsp_chain` already list them); the map is computed
   by a forward pass and *verified* per pc (predecessor consistency), so a non-static rsp motion
   is reported, not assumed.  Memory operands `[rsp + k]` at pc are the slot `(base, δ(pc) + k)`.
2. **Items** = general registers ∪ slots `(base, offset, 8 bytes)`.  `push r` reads `r`, writes
   slot `(E, δ-8)`; `pop r` reads the slot, writes `r`; `mov [rsp+k], r` / `mov r, [rsp+k]` and
   the vector saves/restores likewise (vector slots are 16/32 bytes and tagged by the vector
   register — they are outside `Agree` anyway and only need the "written before read" check).
3. **Tag flow** (copy propagation over the CFG): `tag(pc) : item → Option Reg` says which entry
   callee-saved register's value an item holds.  Entry: `tag r = r` for the callee-saved set;
   `push`/`pop`/save/restore copy tags; every other write clears; the fixpoint is computed like
   `live` and verified per pc like `certB`.  **Check**: no instruction reads a tagged item except
   as the source of a push/save/pop/restore (so tagged values never enter the computation), and
   at the `ret`/tail pc every callee-saved register is tagged with itself.
4. **Run relation**: two states equal except on tagged items (registers may differ, tagged
   slots may differ, everything else equal) stay so (`exec_agree` variant with the item set
   from the certificate), hence halted/err/tail/pc and all untagged memory agree; at exit the
   tags give `RegsOkW` (final `r` = entry `r`) and the memory differs only on frame slots below
   `E`, which `Foot` allows and `OutOk` never looks at.
5. **What the next link / wrapper needs**: for avx2_x8 the pushes `rbp`, `rsi` sit above the
   aligned frame (`avx2x8_frame_below`), the `r12`-`r15` saves at `[A + 896 + 8k]`; the
   certificate entry set drops `[3,5,6,7,12,13,14,15]` and becomes `[8,4,2,1]` plus the tagged
   set, matching avx512/avx_x4.

If the per-pc rsp map fails to verify for a stream (an rsp write not in the list above), fall
back to the fixed-rsp bodies first (shani done; avx512, avx_x4 next) — none of the three is
expected to fail given sections 5/11/12 of R5.md.
