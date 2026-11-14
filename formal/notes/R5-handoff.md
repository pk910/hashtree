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
  `Proofs/WinAvx512Live`, `Proofs/WinAvxX4Live` (`cert`, `live_entry` for [8,4,2,1] / [8,4,2,1] after the
  xor idiom; [8,4,9,2,1] before it).
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
entry sets `[8,4,2,1]` and `[8,4,2,1]` (x4 was `[8,4,9,2,1]` until the xor idiom); then chain-aware `KSpecC` (X86Chain) + `FitsW`.
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

## avx512_x16 link: DONE (`Proofs/WinAvx512Link.lean`, `KSpecC512_of_turnOut`)

Proved as planned below, with two deviations: the tail seed is `T8 := [8,4,2,1]` (the registers
the avx512 stream writes among avx2's entry set; the others `[5,6,12,13,14,15]` are never written
— `WinAvx512Live.unwritten` + `RunExit.run_preserve_all` — which also sidesteps the r12 region-tag
mismatch between `entryWin` and `entryW`), and `PreLink` quantifies the vector *file* (`∃ V`,
32 × 16 lanes) instead of a vector environment.  TRAP (cost 20 min): never `show`/`rfl`/`exact`
against a computed cut state (`KZ`/`KSm`/`KTE`, `sIt`-applied states) — the unifier re-runs the
symbolic execution; close projections with the generic `fr_*'`/`mapState_*'`/`renSt_*` lemmas
and rewrite syntactically.  Build 51 s.

## avx512_x16 link proof plan (as executed)

State of the tree: 49e49d5 (engine with flags bit + tail seed; `WinAvx512Bridge` has `KSpecC512`
with `24 ≤ σ 9`, `TurnOut`; R2b merged at 7669e84 and built: `Avx512X16W{Entry,Body,BodyV,Turn,
Loop}`, `Avx2X8WEntry`, `AvxX4Exit`, `AvxX4ToX1`, `AvxX1WAt`).

Theorem: `KSpecC512_of_turnOut (hT : TurnOut) env σ m0 orcC c inp : KSpecC512
Avx512X16WLoop.steps env σ m0 orcC c inp` (hypotheses of KSpecC512: WfMemW (windows rodata =
linux rodata? CHECK `decide` as for shani: `Kernels.X86Win.Avx512X16.rodata = Kernels.X86.
Avx512X16.rodata`; if they differ, use R2b's region machinery `x16_all_region`), EnvMem, σ 2 = c,
24 ≤ σ 9, input bytes; then ∀ s = mapState env σ entryWin).

Ingredients (all evaluated/checked this session):
* Renaming (`WinAvx512.F`/`G`, `win_transfer hprog n s hlen herr herr'`: `run winProg n (renSt F G
  s) = renSt F G (run linuxProg n s)`, `hprog := win_correspondence`): windows j holds linux
  `G j`; `G 1 = 7, G 2 = 6, G 6 = 9, G 7 = 10, G 8 = 2, G 9 = 1, G 10 = 8`, identity elsewhere.
* Linux certificate env `eL`: `eL (.n 18) := env (.n 12)`, `eL (.n 19) := env (.n 13)` (linux r9
  = `gId 9 _` = 18/19 must carry windows rsi = `gId 6 _` = 12/13; `gId g h = 2g+h`), `eL (.n k)
  := env (.n k)` otherwise, `eL (.m r off) := cellX (m0 ⟨r, off.eval σ'⟩)`; `σ' := fun i => if
  i = 10 then σ 1 else σ i` (x16_loop needs `σ 10 = σ 1`; entryW does not read symbol 10).
  `Mem0Rel eL σ' mW m0` from `mem0RelW_of_wf rodata [] eL σ' m0 (WfMemW …) (EnvMem by rfl)`.
* Entry agreement (windows side): `Agree L0 false (mapState env σ entryWin) (renSt F G (mapState
  eL σ' entryW))` with `L0 = WinAvx512Live.live_entry_eq = [8,4,5,6,12,13,14,15,2,1]`:
  entryW (linux, `X86SymW.entryW`): 0 ptr(rOut,s1), 1 ptr(rNum,s2), 2 ptr(rNum,s2), 3 ptr(rStack,s5),
  4 ptr(rStack,sAt 0), 5 ptr(rStack,s6), 6 ptr(rIn,s0), 7 ptr(rOut,s1), 8 num(16,17), 9 num(18,19),
  10 num(20,21), 11 num(22,23), 12 ptr(rStack,s7), 13 ptr(rNum,s11), 14 ptr(rG,s8), 15 ptr(rNum,s12).
  entryWin (windows): 1 ptr(rOut,s1), 2 ptr(rIn,s0), 8 ptr(rNum,s2), 4 ptr(rStack,sAt 0),
  3 ptr(rStack,s5), 5 ptr(rStack,s6), 12 ptr(rNum,s7) [NB: entryW has r12 = ptr(rStack,s7) —
  constructor differs! 12 ∈ L0: CHECK which is right; if the linux r12 is rStack-tagged and the
  windows one rNum-tagged, the entry Agree on 12 fails and r12 must leave L0: it is only in L0
  because avx2_x8 saves it (the push-saving link) — handle by proving the avx2 side reads r12 only
  into its save slot (frame-slot certificate) or by tagging both the same; report if blocked],
  13 ptr(rNum,s11), 14 ptr(rG,s8), 15 ptr(rNum,s12), 6/7/0/9/10/11 num(gId).
  Pairs for L0: 8↔2 ✓, 4↔4 ✓, 5↔5 ✓, 6↔9 (num 12/13 vs num 18/19 — fixed by eL) ✓, 12↔12 (see NB),
  13↔13 ✓, 14↔14 ✓, 15↔15 ✓, 2↔6 ✓, 1↔7 ✓; vr: same lanes (vId = 100+16i+l), eL = env on them;
  flags: fl = false; mem [] both; pc 0; len 16 (`renSt_gpr_len`).
* Then `run_agree WinAvx512Live.cert (steps c)` gives Agree at the final pc between W (windows run)
  and `renSt F G f` (f the linux run), on `L (final pc)` ⊇ `T8` at a tail pc (`Cert.tail`) and
  ∋ 4 at the ret pc 3 (ret reads rsp).
* Cases (`Avx512X16WLoop.steps c = if c = 0 then 4 else if c < 16 then 8 else 8 + turnSteps*(c/16)`):
  - c = 0: `x16_zero_run` → f = mapState e σ' KZ; KZ.pc = 3, halted, tail none, err none, mem [],
    `KZ.gpr[4]? = ptr(rStack, sAt 8)`. PostLink D = 0: Foot/OutOk vacuous (mem = []), RegsOkW:
    callee-saved via a never-written scan of p512 for [3,5,12,13,14,15] + `run_preserve_all`
    (to add to RunExit: no body range, halted steps are identity), rsp = σ9+8 via Agree(final pc ∋ 4).
  - 0 < c < 16: `x16_small_run` → f = mapState e σ' KSm, tail avx2; `KSm.gpr = entryW.gpr`,
    `KSm.vr = entryW.vr`, mem []. PreLink d = 0, r = c, M' = [], e' := env (vector file unchanged).
  - 16 ≤ c: `x16_loop` → f = fr M (mapState e (sIt (c/16-1) σ') KTE), OutLog M, `sIt_count`.
    KTE (evaluated): rax ptr(rOut,s10), rcx ptr(4,0), rdx ptr(rNum, s2-16), rbx ptr(rStack,s5),
    rsp ptr(rStack,sAt 0), rbp ptr(rStack,s6), rsi ptr(rIn, 1024+s0), rdi ptr(rOut, 512+s1),
    r8 ptr(4,4160), r9 num(18,19), r10 num(20,21), r11 ptr(4,8256), r12 ptr(rStack,s7),
    r13 ptr(rNum,s11), r14 ptr(rG,s8), r15 ptr(rNum,s12); KTE.mem = 512 rOut cells at s1+0..511;
    KTE.pc = 8, halted, tail avx2. `tau = [⟨1024,[1]⟩, ⟨512,[0,1]⟩, ⟨-16,[0,0,1]⟩]`, `sIt (j+1) σ
    = sIt j (sigmaOf tau σ)`, `sigmaOf tau σ i = (tau.getD i (Lin.sym i)).eval σ`: prove
    `sIt j σ 0 = σ 0 + 1024 j`, `sIt j σ 1 = σ 1 + 512 j`, `sIt j σ i = σ i` for i ∉ {0,1,2}
    (R2b has `sIt_count`, `sIt_9`). With j = c/16-1: rdi = σ1 + 32(c - c%16), rsi = σ0 + 64(c -
    c%16), rdx = c%16. PreLink d = c - c%16, r = c%16: M' := W.mem = KTE.mem-mapped ++ M;
    OutLogW (σ 9) M' from OutLog M (stack writes `off < 24 ≤ σ 9`) and KTE.mem all rOut; Foot and
    OutOk from `hT` (TurnOut); vector env `e' (.n n) := if ∃ i < 32, ∃ l < 16, n = vId i l then
    E.eval eL (KTE lane i l) else env (.n n)` (decidable bounded ∃; vId injective by omega), `e'`
    on `.m` keys irrelevant (entryWin has no memory symbols) — SameG env e' since vId ≥ 100 > gId.
* halted/err/tail of W from f via Agree + renSt (`renSt` keeps everything but gpr).

## avx_x4 link: certificate-independent parts DONE (`Proofs/WinAvxX4Link.lean`)

Landed (commit D): `rodata4_getD`/`wf_linux_of_win` (windows table = linux table + 48 zero bytes,
so the linux certificate's `WfMemW` follows from the windows one); the `c = 0` path as a
four-instruction symbolic run `KZ4 := run p4 4 (mem0sW 4 rodata []) _ 4 entryWin` transported by
`run_hom` (`x4_zero_run`; the recorded `jne` assumption `(.not (.eq ⟨0,[0,0,1]⟩ ⟨0,[]⟩), false)`
discharged from `σ 2 = 0`), `postLink_zero` (PostLink at depth 0: halted, no log, RegsOkW with
`rsp = σ 9 + 8`); the hand-off `preLink_of_exit` (PreLink for avx_x1 on `L1` from the exit facts:
r8/rcx/rdx/rsp values, callee-saved registers equal to the entry state, a 32x16 vector file, the
log facts); and the glue `KSpecC4_of_cert (X : X4WinCert)` giving `KSpecC4 (fun c => if c = 0
then 4 else X.steps c)`.  Axioms: standard + `loadLane_hom._native.bv_decide.ax_1_6` (run_hom).

`X4WinCert` is the interface a certificate OF THE WINDOWS STREAM must provide (route (b): R2's
W-mode tooling on `Kernels.X86Win.AvxX4.prog`, pack `Gen/WinAvxX4P`, count 4, Win64 entry
`X86Run.entry true cnt 24` — the generator needs a kernel-table entry and a Win64 S-mode start
state; not authorized in R5, see the integration note).  Its fields are exactly what
`preLink_of_exit` consumes: for `c ≠ 0`, after `steps c` instructions from `mapState env σ
entryWin`: err none, tail avx_x1, 16 gprs, r8 = ptr(rNum, c%4), rcx = ptr(rOut, σ1 + 32(c-c%4)),
rdx = ptr(rIn, σ0 + 64(c-c%4)), rsp = ptr(rStack, σ9), [3,5,6,7,12,13,14,15] unchanged, vr 32x16,
`OutLogW (σ 9)`, `Foot (σ 9) 568 (σ 1) (32c)`, `OutOk inp (σ 1) (c-c%4)` of the final log.
Route (a) (transfer from the linux certificate, below) would instead prove `X4WinCert.spec` from
`x4_runW` + `TurnOut4` through the piecewise pc map; it is NOT needed if the windows pack lands.

## avx_x4 link plan, route (a) (`KSpecC4_of_turnOut4` via transfer from the linux certificate)

Statement module `Proofs/WinAvxX4Bridge.lean` (KSpecC4, TurnOut4, x4RunSteps) is written; TurnOut4
sent to R2c.  Certificates merged: R2 9a2d747 (`AvxX4LoopWAll.x4_runW`, `x4_runW_last`, W-mode,
from `fr M (mapState env0 σ entryW)` at count `4(j+1)+s`, `s ∈ [4,8)`, to
`fr M' (mapState e' (sIt (j+1) (upd15 σ)) K201W)`), small counts: `AvxX4ToX1.x4_small_to_x1`
(x4 early exit, 8 instructions, tails to x1 — check its exact statement), zero: pc 1-3 `cmp r8,0;
jne; ret`.

Evaluated facts:
* Windows avx_x4 (`Kernels.X86Win.AvxX4`): pc 0 nop, 1 `cmp r8,0`, 2 `jne 4`, 3 `ret`, 4 `sub
  rsp,568`, 5-14 `vmovdqa [rsp+384+16k], xmm(6+k)`, 15 `cmp r8,4`, 16 `jl 4151`, 17 `xor r9,r9`,
  18 `lea rax,[rip+0x800]`, … body …, 4147 `add rdx,256`, 4148 `add rcx,128`, 4149 `sub r8,4`,
  4150 `jmp 15`, 4151-4160 restores, 4161 `add rsp,568`, 4162 `jmpTail avx_x1`.  Linux stream: the
  same without the saves/restores, pc map `w-10` below 705 / `w-9` from 705 (`WinAvxX4.bodyPc`,
  `bodyReg = {1->0, 2->8, 6->2, 7->1}`, section 11) — NOT a constant shift: the shani transfer
  engine `run_comb` needs a two-segment composition or a generalised pc map.
* `K201W` (R2, `AvxX4LoopWExit.K201W`, pc 4143, halted, tail avx_x1, 1280 log cells in rOut and
  rStack): rax ptr(rOut, s15) [upd15 pins s15 := s1], rcx ptr(4, 1024), rdx ptr(rNum, s2-4),
  rbx s5, rsp sAt 0, rbp s6, rsi ptr(rIn, 256+s0), rdi ptr(rOut, 128+s1), r8 num, r9 ptr(rNum,1024),
  r12 ptr(rStack,s7), r13 s11, r14 s8, r15 s12.  `tau` (x4) = [256+s0, 128+s1, s2-4, a, b] (a, b =
  the loop-head flags), `sIt j` iterates it; symbols ≥ 5 unchanged.
* Rodata: windows 2240 bytes = linux 2192 + 48 zero bytes (`getD` agrees everywhere): prove
  `WfMemW linuxRodata … ← WfMemW winRodata …` in the bridge (decide the prefix + zeros).
* Entry set `[8,4,2,1]` (commit C: `srcs` treats `xor r,r` as a zeroing idiom with no sources,
  `exec_agree` alu case split on it; before that 9 was spuriously live via `xor r9,r9`).  avx_x1's entry set `L1 = [4,3,8,6,7,5,12,13,14,15,1,2]`
  (push-saving); avx_x4 never writes `[3,5,6,7,12,13,14,15]` (`avx_x4_callee_gpr_untouched`,
  re-check with `unwrittenScan`), so PreLink's Agree on those is by preservation as for avx512.

Proof shape (shani-shaped, NOT avx512-shaped — the windows stream is not a renaming):
1. Windows prologue replay pc 0..14 from `mapState env σ entryWin` (c ≠ 0): symbolic 15-step run
   `P15 := abstract (run winProg 4 m0W? … 15 entryWin)` is NOT available (entryWin lives in
   WinWrapperPre with its own `m0W`) — either replay concretely (`run_succ` + `exec` evaluation per
   instruction, 15 steps: cmp/jne/sub/10 vstores/cmp/jl — the shani WinShaniFront did this for 11)
   or symbolically via `slice_sound` with a windows symbolic memory.  Result: rsp = σ9-568, flags
   of `cmp r8,4`, log = 10 xmm saves at [σ9-184, σ9-24) (the save log `M4`).
2. Seed: the linux state after its own prologue (`sub rsp,568`? CHECK the linux prologue pcs 0..4)
   from `fr M (mapState eL σ' entryW)` — compute the symbolic linux prefix state (decide), align
   with the windows post-prologue state on the linux body entry live set (compute `live
   linuxAvxX4Prog` at the body-entry pc; expect `[2,6,7,4,…]`) — Agree with the windows state
   *translated* by the register substitution bodyReg and the frame shift (windows frame 568 vs
   linux frame: CHECK `sub rsp` imm in Kernels.X86.AvxX4 pc 4).
3. Body transfer: windows body run (pcs 17..4150) = translated linux body run: needs
   `run_comb`-style theorem for the avx_x4 body with the piecewise pc map; R5 §11 has the static
   correspondence scans (`avx_x4_body_correspondence_lo/hi`) but no run-level transfer.  This is
   the main new piece (compare WinShaniTransfer: `run_comb renPerm δ W lo hi hi_le body_hmap
   body_hside`).  With `bodyPc` piecewise, split the body at windows pc 705 (linux 696) into two
   constant-shift segments and compose with the single inserted instruction at windows 705.
4. Exit: windows 4151-4162 replay (10 vloads from the save log, `add rsp`, `jmpTail`); PreLink
   for avx_x1 from K201W's registers (rcx = linux rdi → σ1 + 128(j+2) = σ1 + 32(c - c%4); rdx =
   linux rsi; r8 = linux rdx = c%4; rsp = σ9 after `add`; callee-saved by preservation), log =
   windows frame cells + outputs (TurnOut4 for the bytes/range), `D = 568`.
5. c = 0: 4-step concrete replay (nop, cmp, jne not taken, ret) — PostLink D = 0.
Estimated: the body transfer (3) is the long pole (shani's took WinShaniTransfer + WinFrameStack +
WinShaniFlags, ~2000 lines); consider asking whether R2 has a W-mode *windows-stream* avx_x4
certificate (`Kernels.X86Win.AvxX4` run directly) which would remove (3) entirely.
