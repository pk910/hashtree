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

## Next lemma (checkpoint (a), the positive shani bridge) — module `Proofs/WinShaniBridge.lean`

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
