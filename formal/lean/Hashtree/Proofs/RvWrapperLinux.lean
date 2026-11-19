import Hashtree.Kernels.Riscv.WrapperLinux
import Hashtree.Proofs.RvRegs
import Hashtree.Proofs.RvDispatch

/-!
# The linux/riscv64 `HashtreeHash` Go wrapper: run to the call, and back

`Hashtree/Kernels/Riscv/WrapperLinux.lean` models the go1.26 stream of
`hashtree-bindings/wrapper_linux_riscv64.s` (ABI0 `$0-24`): two `sd`'s of the incoming `ra`
below the entry `sp`, the three argument loads, `auipc`+`jalr` as the `CALL hashtree_hash`,
and `ld ra,0(sp)`/`addi sp,sp,8`/`jalr zero,0(ra)` as the `RET`.  This file proves:

* `wrapper_prefix` — from the ABI0 entry (`ra` = the return target, `sp = sp0`) on a frame whose
  words at `sp0+8`, `+16`, `+24` are the output pointer, input pointer and count, eight
  instructions reach the call boundary: `tail = some "call:hashtree_hash"`, the link
  `ra = ⟨rWcode, 8⟩`, the callee stack pointer `sp0 - 8`, and the three arguments in
  `a0`/`a1`/`a2`.
* `b7_entry`/`b7_callee`/`b7_concrete` — B7: `sp0 ≡ 8 (mod 16)` gives callee entry
  `sp0 - 8 ≡ 0 (mod 16)`, and conversely.
* `stub_run`/`stub_at_call` — the shipped `hashtree_hash` stub at that call boundary tail-calls
  `init_and_hash` (`RvDispatch.stub_correct` is the same statement for the all-location-variable
  entry; the wrapper's registers are concrete pointers, so the concrete-state form is proved
  here directly from the three instructions, with the `.data.rel.local` slot as a hypothesis).
* `wrapper_epilogue` — once the callee has returned to instruction 8, three instructions reload
  the caller's `ra` from the ra slot and restore `sp = sp0`, with no tail.
* `prefixC`/`wrapper_end2end` — the concrete ABI0 entry `SPe = 8` on a memory holding the
  argument frame and the `.data.rel.local` slot: the full chain composition.

What is *not* modelled: the callee's own return from its program to the wrapper's instruction 8
(the model has no cross-program return: a `ret` to a different code region is not a step of
`Riscv.run`), so the end-to-end theorem takes the post-return state as `returned s` (same
registers, memory and `ra`/`sp` as the call boundary, `pc := 8`, `halted := false`) and proves
the epilogue from there.  The stack-check preamble is abstracted as well (see the kernel model).
-/

open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Kernels.Riscv.WrapperLinux
open Hashtree.Proofs.RvRegs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Proofs.RvWrapperLinux

/-- Runs compose with a leading step. -/
theorem run_succ (prog : Array Instr) (env : Env) (mem0 : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (n : Nat) (s : State W32 Int) (i : Instr)
    (h : s.halted = false) (hi : prog[s.pc]? = some i) :
    run prog env mem0 orc (n + 1) s = run prog env mem0 orc n (exec env mem0 orc i s) := by
  unfold run
  simp only [h, Bool.false_eq_true, ite_false, hi]
  cases n <;> rfl

theorem next_mem (s : State W32 Int) : s.next.mem = s.mem := rfl

theorem rset_mem (s : State W32 Int) (d : Nat) (v : Val W32 Int) : (rset s d v).mem = s.mem := by
  unfold rset; split <;> rfl

theorem okOr_mem (s : State W32 Int) (res : Except String (State W32 Int))
    (hok : ∀ s', res = .ok s' → s'.mem = s.mem) : (okOr s res).mem = s.mem := by
  cases res with
  | ok s' => exact hok s' rfl
  | error e =>
    simp only [okOr, State.fail]
    split <;> rfl

theorem readCell_mem_congr (mem0c : Addr Int → Cell W32 Int) (s s' : State W32 Int)
    (h : s.mem = s'.mem) (a : Addr Int) : readCell mem0c s a = readCell mem0c s' a := by
  simp only [readCell, h]

theorem pbRest_mem_congr (mem0c : Addr Int → Cell W32 Int) (s s' : State W32 Int)
    (h : s.mem = s'.mem) :
    ∀ (p a : Addr Int) (n k : Nat), pbRest mem0c s p a n k = pbRest mem0c s' p a n k := by
  intro p a n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    simp only [pbRest, readCell_mem_congr mem0c s s' h, ih (k + 1)]

theorem loadLane_mem_congr (mem0c : Addr Int → Cell W32 Int) (s s' : State W32 Int)
    (h : s.mem = s'.mem) (a : Addr Int) : loadLane mem0c s a = loadLane mem0c s' a := by
  simp only [loadLane, readCell_mem_congr mem0c s s' h]

theorem loadVal_mem_congr (mem0c : Addr Int → Cell W32 Int) (s s' : State W32 Int)
    (h : s.mem = s'.mem) (a : Addr Int) : loadVal mem0c s a = loadVal mem0c s' a := by
  simp only [loadVal, readCell_mem_congr mem0c s s' h, pbRest_mem_congr mem0c s s' h,
    loadLane_mem_congr mem0c s s' h]

theorem exec_ld_mem (env : Env) (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (d b : Nat) (off : Int) (s : State W32 Int) :
    (exec env mem0c orc (.ld d b off) s).mem = s.mem := by
  unfold exec
  split
  · rfl
  · refine okOr_mem s _ ?_
    intro s' hs
    obtain ⟨a, -, hs⟩ := bind_ok_of _ _ s' hs
    obtain ⟨v, -, hs⟩ := bind_ok_of _ _ s' hs
    have e := pure_ok_state _ s' hs
    rw [← e]
    exact (next_mem (rset s d v)).trans (rset_mem s d v)

/-- `rset s d v` read back at `d` -/
theorem rset_getG_self (s : State W32 Int) (d : Nat) (v : Val W32 Int) (hd : d ≠ 0)
    (hlen : d < s.gpr.length) : (rset s d v).getG d = v := by
  unfold rset
  split
  · rename_i h; exact absurd h hd
  · exact getG_setG_self s d v hlen

/-- `sd ra, off(sp)` -/
theorem exec_sd_off (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : State W32 Int) (off : Int) (sp0 : Int) (p : Addr Int)
    (hh : s.halted = false) (hra : s.getG 1 = .ptr p) (hsp : s.getG 2 = .ptr ⟨rStack, sp0⟩) :
    exec wenv mem0c orc (.sd 1 2 off) s =
      { s with
        mem := ((List.range 8).reverse.map (fun (i : Nat) =>
          ((⟨rStack, sp0 + off⟩ : Addr Int).plusI (Int.ofNat i), Cell.pb p i))) ++ s.mem,
        pc := s.pc + 1 } := by
  simp [exec, hh, okOr, ea, rget, hra, hsp, checkWritable, wenv, rWro, rWgot, rStack, rNum,
    storeVal, State.next, State.setG, Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt,
    reduceCtorEq, Int.reduceLE, Int.reduceLT]
  rfl

/-- `addi sp, sp, -8` -/
theorem exec_addi_sp_m8 (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : State W32 Int) (sp0 : Int) (hh : s.halted = false)
    (hsp : s.getG 2 = .ptr ⟨rStack, sp0⟩) :
    exec wenv mem0c orc (.addi 2 2 (-8)) s =
      { s with gpr := s.gpr.set 2 (.ptr ⟨rStack, sp0 + (-8)⟩), pc := s.pc + 1 } := by
  simp [exec, hh, okOr, addVal, ctlOf, rget, hsp, rset, State.setG, State.next, lanesOfInt,
    Addr.plus, Ctl.add, Ctl.ofInt, rStack, rNum, sint64]
  rfl

/-- `ld d, off(b)` -/
theorem exec_ld (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (env : Env)
    (s : State W32 Int) (d b : Nat) (off : Int) (spBase : Int) (v : Val W32 Int)
    (hd : d ≠ 0) (hb : b ≠ 0) (hh : s.halted = false)
    (hsp : s.getG b = .ptr ⟨rStack, spBase⟩)
    (hl : loadVal mem0c s ⟨rStack, spBase + off⟩ = .ok v) :
    exec env mem0c orc (.ld d b off) s =
      { s with gpr := s.gpr.set d v, pc := s.pc + 1 } := by
  simp only [rStack] at hl
  simp [exec, hh, okOr, ea, rget, hsp, hd, hb, rset, State.setG, State.next, hl, Addr.plusI,
    Addr.plus, Ctl.add, Ctl.ofInt, rStack, rNum]
  rfl

/-- `auipc ra, %pcrel_hi(hashtree_hash)` in the wrapper -/
theorem exec_auipc (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int)
    (hh : s.halted = false) :
    exec wenv mem0c orc (.auipc 1 (.sym "hashtree_hash" 0)) s =
      { s with gpr := s.gpr.set 1 (.ptr ⟨rSymHH, 0⟩), pc := s.pc + 1 } := by
  simp [exec, hh, okOr, Env.target, wenv, rset, State.next, State.setG, Ctl.ofInt, pure,
    Except.pure, Except.bind, reduceCtorEq, Int.reduceLE, Int.reduceLT]
  rfl

/-- `jalr ra, ra, 0` calling `hashtree_hash` -/
theorem exec_call (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int)
    (hh : s.halted = false) (h : s.getG 1 = .ptr ⟨rSymHH, 0⟩) :
    exec wenv mem0c orc (.jalr 1 1 0) s =
      callOut (link wenv s 1) (s.pc + 1) "call:hashtree_hash" := by
  simp [exec, hh, okOr, ctlOf, rget, h, jumpTo, link, Env.nameOf, wenv, Addr.plusI, Addr.plus,
    pure, Except.pure, Ctl.add, Ctl.ofInt, Ctl.asInt, State.setG, State.next, Bind.bind,
    Except.bind, MonadExcept.throw, Except.error, rRet, rNum]
  rfl

/-- `jalr zero, 0(ra)` returning to the caller -/
theorem exec_ret (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int)
    (hh : s.halted = false) (h : s.getG 1 = .ptr ⟨rRet, 0⟩) :
    exec wenv mem0c orc (.jalr 0 1 0) s = halt s := by
  simp [exec, hh, okOr, ctlOf, rget, h, jumpTo, rRet, Addr.plusI, Addr.plus, pure,
    Except.pure, Ctl.add, Ctl.ofInt, Ctl.asInt, Bind.bind, Except.bind, State.fail]

/-- A register of a state update. -/
theorem rec_getG_self (s : State W32 Int) (d : Nat) (v : Val W32 Int) (hlen : d < s.gpr.length) :
    ({ s with gpr := s.gpr.set d v, pc := s.pc + 1 } : State W32 Int).getG d = v := by
  simp [State.getG, List.getD_eq_getElem?_getD, List.getElem?_set_self hlen]

theorem rec_getG_ne (s : State W32 Int) (d : Nat) (v : Val W32 Int) (r : Nat) (h : r ≠ d) :
    ({ s with gpr := s.gpr.set d v, pc := s.pc + 1 } : State W32 Int).getG r = s.getG r := by
  simp [State.getG, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem rset_len (s : State W32 Int) (d : Nat) (v : Val W32 Int) :
    (rset s d v).gpr.length = s.gpr.length := by
  unfold rset; split
  · rfl
  · simp [State.setG, List.length_set]

theorem callOut_len (s : State W32 Int) (pc : Nat) (name : String) :
    (callOut s pc name).gpr.length = s.gpr.length := rfl

theorem haltLen (s : State W32 Int) : (halt s).gpr.length = s.gpr.length := rfl

theorem haltTailLen (s : State W32 Int) (name : String) :
    (haltTail s name).gpr.length = s.gpr.length := rfl

theorem run_one (prog : Array Instr) (env : Env) (mem0 : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (s : State W32 Int) (i : Instr)
    (h : s.halted = false) (hi : prog[s.pc]? = some i) :
    run prog env mem0 orc 1 s = exec env mem0 orc i s := by
  rw [show (1 : Nat) = 0 + 1 by rfl, run_succ prog env mem0 orc 0 s i h hi]
  rfl

/-- **The wrapper prefix** (instructions 0-7 of `wrapper_linux_riscv64.s`): from the ABI0 entry
(`ra` = the return target, `sp = sp0`) on a frame whose argument words at `sp0 + 8`, `+ 16`, `+ 24`
load as the output pointer, the input pointer and the count, the run reaches the
`CALL hashtree_hash` after 8 instructions with `ra` = the return point 8, the callee stack pointer
`sp0 - 8`, and the three arguments in `a0`/`a1`/`a2`. -/
theorem wrapper_prefix (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (sp0 : Int)
    (aOut aIn : Addr Int) (k : Int) (s0 : State W32 Int)
    (hglen : s0.gpr.length = 32)
    (h0 : s0.halted = false) (hpc : s0.pc = 0) (herr0 : s0.err = none)
    (hra : s0.getG 1 = .ptr ⟨rRet, 0⟩) (hsp : s0.getG 2 = .ptr ⟨rStack, sp0⟩)
    (hout : loadVal mem0c (run prog wenv mem0c orc 3 s0) ⟨rStack, sp0 + (-8) + 16⟩ = .ok (.ptr aOut))
    (hin : loadVal mem0c (run prog wenv mem0c orc 3 s0) ⟨rStack, sp0 + (-8) + 24⟩ = .ok (.ptr aIn))
    (hcnt : loadVal mem0c (run prog wenv mem0c orc 3 s0) ⟨rStack, sp0 + (-8) + 32⟩ = .ok (.ptr ⟨rNum, k⟩)) :
    (run prog wenv mem0c orc 8 s0).halted = true ∧
      (run prog wenv mem0c orc 8 s0).tail = some "call:hashtree_hash" ∧
      (run prog wenv mem0c orc 8 s0).err = none ∧
      (run prog wenv mem0c orc 8 s0).pc = 8 ∧
      (run prog wenv mem0c orc 8 s0).getG 1 = .ptr ⟨rWcode, 8⟩ ∧
      (run prog wenv mem0c orc 8 s0).getG 2 = .ptr ⟨rStack, sp0 + (-8)⟩ ∧
      (run prog wenv mem0c orc 8 s0).getG 10 = .ptr aOut ∧
      (run prog wenv mem0c orc 8 s0).getG 11 = .ptr aIn ∧
      (run prog wenv mem0c orc 8 s0).getG 12 = .ptr ⟨rNum, k⟩ ∧
      (run prog wenv mem0c orc 8 s0).gpr.length = 32 := by
  let s1 := exec wenv mem0c orc (.sd 1 2 (-8)) s0
  let s2 := exec wenv mem0c orc (.addi 2 2 (-8)) s1
  let s3 := exec wenv mem0c orc (.sd 1 2 0) s2
  let s4 := exec wenv mem0c orc (.ld 10 2 16) s3
  let s5 := exec wenv mem0c orc (.ld 11 2 24) s4
  let s6 := exec wenv mem0c orc (.ld 12 2 32) s5
  let s7 := exec wenv mem0c orc (.auipc 1 (.sym "hashtree_hash" 0)) s6
  let s8 := exec wenv mem0c orc (.jalr 1 1 0) s7
  have h1 := exec_sd_off mem0c orc s0 (-8) sp0 (⟨rRet, 0⟩ : Addr Int) h0 hra hsp
  have h1h : s1.halted = false := by dsimp only [s1]; rw [h1]; exact h0
  have h1pc : s1.pc = 1 := by dsimp only [s1]; rw [h1]; simp [hpc]
  have h1len : s1.gpr.length = 32 := by dsimp only [s1]; rw [h1]; exact hglen
  have h1err : s1.err = none := by dsimp only [s1]; rw [h1]; exact herr0
  have h1sp : s1.getG 2 = .ptr ⟨rStack, sp0⟩ := by dsimp only [s1]; rw [h1]; exact hsp
  have h2 := exec_addi_sp_m8 mem0c orc s1 sp0 h1h h1sp
  have h2h : s2.halted = false := by dsimp only [s2]; rw [h2]; exact h1h
  have h2pc : s2.pc = 2 := by dsimp only [s2]; rw [h2]; simp [h1pc]
  have h2len : s2.gpr.length = 32 := by dsimp only [s2]; rw [h2, List.length_set, h1len]
  have h2err : s2.err = none := by dsimp only [s2]; rw [h2]; exact h1err
  have h1ra : s1.getG 1 = .ptr ⟨rRet, 0⟩ := by
    dsimp only [s1]; rw [h1]; exact hra
  have h2sp : s2.getG 2 = .ptr ⟨rStack, sp0 + (-8)⟩ := by
    dsimp only [s2]; rw [h2]
    exact rec_getG_self _ 2 _ (by rw [h1len]; decide)
  have h2ra : s2.getG 1 = .ptr ⟨rRet, 0⟩ := by
    dsimp only [s2]; rw [h2]
    exact (rec_getG_ne _ 2 _ 1 (by decide)).trans h1ra
  have hs2 : run prog wenv mem0c orc 2 s0 = s2 := by
    rw [show (2 : Nat) = 1 + 1 by rfl, rvRun_add]
    rw [run_one prog wenv mem0c orc s0 (.sd 1 2 (-8)) h0 (by rw [hpc]; decide +kernel)]
    rw [run_one prog wenv mem0c orc s1 (.addi 2 2 (-8)) h1h (by rw [h1pc]; decide +kernel)]
  have hs3 : run prog wenv mem0c orc 3 s0 = s3 := by
    rw [show (3 : Nat) = 2 + 1 by rfl, rvRun_add, hs2]
    rw [run_one prog wenv mem0c orc s2 (.sd 1 2 0) h2h (by rw [h2pc]; decide +kernel)]
  rw [hs3] at hout hin hcnt
  have h3 := exec_sd_off mem0c orc s2 0 (sp0 + (-8)) (⟨rRet, 0⟩ : Addr Int) h2h h2ra h2sp
  have h3h : s3.halted = false := by dsimp only [s3]; rw [h3]; exact h2h
  have h3pc : s3.pc = 3 := by dsimp only [s3]; rw [h3]; simp [h2pc]
  have h3len : s3.gpr.length = 32 := by dsimp only [s3]; rw [h3]; exact h2len
  have h3err : s3.err = none := by dsimp only [s3]; rw [h3]; exact h2err
  have h3sp : s3.getG 2 = s2.getG 2 := by dsimp only [s3]; rw [h3]; rfl
  have h3p : s3.getG 2 = .ptr ⟨rStack, sp0 + (-8)⟩ := h3sp.trans h2sp
  have h4 := exec_ld mem0c orc wenv s3 10 2 16 (sp0 + (-8)) (.ptr aOut)
    (by decide) (by decide) h3h h3p hout
  have h4h : s4.halted = false := by dsimp only [s4]; rw [h4]; exact h3h
  have h4pc : s4.pc = 4 := by dsimp only [s4]; rw [h4]; simp [h3pc]
  have h4len : s4.gpr.length = 32 := by
    dsimp only [s4]; rw [h4, List.length_set, h3len]
  have h4err : s4.err = none := by dsimp only [s4]; rw [h4]; exact h3err
  have h4sp : s4.getG 2 = s3.getG 2 := by
    dsimp only [s4]; rw [h4]; exact rec_getG_ne _ 10 _ 2 (by decide)
  have h4p : s4.getG 2 = .ptr ⟨rStack, sp0 + (-8)⟩ := h4sp.trans h3p
  have h4a0 : s4.getG 10 = .ptr aOut := by
    dsimp only [s4]; rw [h4]
    exact rec_getG_self _ 10 _ (by rw [h3len]; decide)
  have h4mem : s4.mem = s3.mem := by dsimp only [s4]; rw [h4]
  have hin' : loadVal mem0c s4 ⟨rStack, sp0 + (-8) + 24⟩ = .ok (.ptr aIn) := by
    rw [loadVal_mem_congr mem0c s4 s3 h4mem]; exact hin
  have h5 := exec_ld mem0c orc wenv s4 11 2 24 (sp0 + (-8)) (.ptr aIn)
    (by decide) (by decide) h4h h4p hin'
  have h5h : s5.halted = false := by dsimp only [s5]; rw [h5]; exact h4h
  have h5pc : s5.pc = 5 := by dsimp only [s5]; rw [h5]; simp [h4pc]
  have h5len : s5.gpr.length = 32 := by
    dsimp only [s5]; rw [h5, List.length_set, h4len]
  have h5err : s5.err = none := by dsimp only [s5]; rw [h5]; exact h4err
  have h5sp : s5.getG 2 = s4.getG 2 := by
    dsimp only [s5]; rw [h5]; exact rec_getG_ne _ 11 _ 2 (by decide)
  have h5p : s5.getG 2 = .ptr ⟨rStack, sp0 + (-8)⟩ := h5sp.trans h4p
  have h5a0 : s5.getG 10 = s4.getG 10 := by
    dsimp only [s5]; rw [h5]; exact rec_getG_ne _ 11 _ 10 (by decide)
  have h5a1 : s5.getG 11 = .ptr aIn := by
    dsimp only [s5]; rw [h5]
    exact rec_getG_self _ 11 _ (by rw [h4len]; decide)
  have h5mem : s5.mem = s4.mem := by dsimp only [s5]; rw [h5]
  have hcnt' : loadVal mem0c s5 ⟨rStack, sp0 + (-8) + 32⟩ = .ok (.ptr ⟨rNum, k⟩) := by
    rw [loadVal_mem_congr mem0c s5 s4 h5mem, loadVal_mem_congr mem0c s4 s3 h4mem]; exact hcnt
  have h6 := exec_ld mem0c orc wenv s5 12 2 32 (sp0 + (-8)) (.ptr ⟨rNum, k⟩)
    (by decide) (by decide) h5h h5p hcnt'
  have h6h : s6.halted = false := by dsimp only [s6]; rw [h6]; exact h5h
  have h6pc : s6.pc = 6 := by dsimp only [s6]; rw [h6]; simp [h5pc]
  have h6len : s6.gpr.length = 32 := by
    dsimp only [s6]; rw [h6, List.length_set, h5len]
  have h6err : s6.err = none := by dsimp only [s6]; rw [h6]; exact h5err
  have h6sp : s6.getG 2 = s5.getG 2 := by
    dsimp only [s6]; rw [h6]; exact rec_getG_ne _ 12 _ 2 (by decide)
  have h6p : s6.getG 2 = .ptr ⟨rStack, sp0 + (-8)⟩ := h6sp.trans h5p
  have h6a0 : s6.getG 10 = s5.getG 10 := by
    dsimp only [s6]; rw [h6]; exact rec_getG_ne _ 12 _ 10 (by decide)
  have h6a1 : s6.getG 11 = s5.getG 11 := by
    dsimp only [s6]; rw [h6]; exact rec_getG_ne _ 12 _ 11 (by decide)
  have h6a2 : s6.getG 12 = .ptr ⟨rNum, k⟩ := by
    dsimp only [s6]; rw [h6]
    exact rec_getG_self _ 12 _ (by rw [h5len]; decide)
  have h7 := exec_auipc mem0c orc s6 h6h
  have h7h : s7.halted = false := by dsimp only [s7]; rw [h7]; exact h6h
  have h7pc : s7.pc = 7 := by dsimp only [s7]; rw [h7]; simp [h6pc]
  have h7len : s7.gpr.length = 32 := by
    dsimp only [s7]; rw [h7, List.length_set, h6len]
  have h7err : s7.err = none := by dsimp only [s7]; rw [h7]; exact h6err
  have h7sp : s7.getG 2 = s6.getG 2 := by
    dsimp only [s7]; rw [h7]; exact rec_getG_ne _ 1 _ 2 (by decide)
  have h7a0 : s7.getG 10 = s6.getG 10 := by
    dsimp only [s7]; rw [h7]; exact rec_getG_ne _ 1 _ 10 (by decide)
  have h7a1 : s7.getG 11 = s6.getG 11 := by
    dsimp only [s7]; rw [h7]; exact rec_getG_ne _ 1 _ 11 (by decide)
  have h7a2 : s7.getG 12 = s6.getG 12 := by
    dsimp only [s7]; rw [h7]; exact rec_getG_ne _ 1 _ 12 (by decide)
  have h7ra : s7.getG 1 = .ptr ⟨rSymHH, 0⟩ := by
    dsimp only [s7]; rw [h7]
    exact rec_getG_self _ 1 _ (by rw [h6len]; decide)
  have h8 := exec_call mem0c orc s7 h7h h7ra
  have hs4 : run prog wenv mem0c orc 4 s0 = s4 := by
    rw [show (4 : Nat) = 3 + 1 by rfl, rvRun_add, hs3]
    rw [run_one prog wenv mem0c orc s3 (.ld 10 2 16) h3h (by rw [h3pc]; decide +kernel)]
  have hs5 : run prog wenv mem0c orc 5 s0 = s5 := by
    rw [show (5 : Nat) = 4 + 1 by rfl, rvRun_add, hs4]
    rw [run_one prog wenv mem0c orc s4 (.ld 11 2 24) h4h (by rw [h4pc]; decide +kernel)]
  have hs6 : run prog wenv mem0c orc 6 s0 = s6 := by
    rw [show (6 : Nat) = 5 + 1 by rfl, rvRun_add, hs5]
    rw [run_one prog wenv mem0c orc s5 (.ld 12 2 32) h5h (by rw [h5pc]; decide +kernel)]
  have hs7 : run prog wenv mem0c orc 7 s0 = s7 := by
    rw [show (7 : Nat) = 6 + 1 by rfl, rvRun_add, hs6]
    rw [run_one prog wenv mem0c orc s6 (.auipc 1 (.sym "hashtree_hash" 0)) h6h
      (by rw [h6pc]; decide +kernel)]
  have hs8 : run prog wenv mem0c orc 8 s0 = s8 := by
    rw [show (8 : Nat) = 7 + 1 by rfl, rvRun_add, hs7]
    rw [run_one prog wenv mem0c orc s7 (.jalr 1 1 0) h7h (by rw [h7pc]; decide +kernel)]
  rw [hs8]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [s8]; rw [h8, callOut]
  · dsimp only [s8]; rw [h8, callOut]
  · dsimp only [s8]; rw [h8, callOut]; exact h7err
  · dsimp only [s8]; rw [h8, callOut]; simp [h7pc]
  · dsimp only [s8]; rw [h8, callOut_getG, link]
    rw [rset_getG_self s7 1 _ (by decide) (by rw [h7len]; decide)]
    rw [h7pc]; decide
  · dsimp only [s8]
    rw [h8, callOut_getG, link_getG wenv s7 1 2 (by decide), h7sp, h6sp, h5sp, h4sp, h3sp, h2sp]
  · dsimp only [s8]
    rw [h8, callOut_getG, link_getG wenv s7 1 10 (by decide), h7a0, h6a0, h5a0, h4a0]
  · dsimp only [s8]
    rw [h8, callOut_getG, link_getG wenv s7 1 11 (by decide), h7a1, h6a1, h5a1]
  · dsimp only [s8]
    rw [h8, callOut_getG, link_getG wenv s7 1 12 (by decide), h7a2, h6a2]
  · dsimp only [s8]; rw [h8, callOut_len, link, rset_len, h7len]


/-! ## The `hashtree_hash` stub at the wrapper's call state

`hashtree_hash` (`Kernels.Riscv.DispHash`) is three instructions: `auipc` the `.data.rel.local`
slot, load the pointer there, tail-jump through it.  `stub_run` is the concrete-state counterpart
of `RvDispatch.stub_correct`: it starts from any state (not only the all-location-variable entry),
so it applies to the wrapper's call state. -/

/-- The stub's program. -/
def sprog : Array Instr := Hashtree.Kernels.Riscv.DispHash.prog

/-- The stub's environment (`RvDispatch.pe`). -/
def senv : Env := Hashtree.Proofs.RvDispatch.pe

/-- `auipc a5, %pcrel_hi(.data.rel.local)` -/
theorem stub_auipc (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int)
    (hh : s.halted = false) :
    exec senv mem0c orc (.auipc 15 (.sym ".data.rel.local" 0)) s =
      { s with gpr := s.gpr.set 15 (.ptr (⟨60, 0⟩ : Addr Int)), pc := s.pc + 1 } := by
  simp [exec, hh, okOr, Env.target, senv, Hashtree.Proofs.RvDispatch.pe, Hashtree.Proofs.RvDispatch.syms,
    rset, State.next, State.setG, Ctl.ofInt, pure, Except.pure, Except.bind, reduceCtorEq,
    Int.reduceLE, Int.reduceLT]
  rfl

/-- `ld a5, 0(a5)` -/
theorem stub_ld (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int)
    (v : Val W32 Int) (hh : s.halted = false)
    (h15 : s.getG 15 = .ptr (⟨60, 0⟩ : Addr Int))
    (hl : loadVal mem0c s (⟨60, 0⟩ : Addr Int) = .ok v) :
    exec senv mem0c orc (.ld 15 15 0) s =
      { s with gpr := s.gpr.set 15 v, pc := s.pc + 1 } := by
  simp [exec, hh, okOr, ea, rget, h15, (by decide : ¬ ((15 : Nat) = 0)), rset, State.setG,
    State.next, hl, Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, reduceCtorEq, rNum]
  rfl

/-- `c.jr a5`: tail-call through the loaded pointer -/
theorem stub_jalr (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int)
    (hh : s.halted = false) (h15 : s.getG 15 = .ptr (⟨6, 0⟩ : Addr Int)) :
    exec senv mem0c orc (.jalr 0 15 0) s = haltTail s "init_and_hash" := by
  simp [exec, hh, okOr, ctlOf, rget, h15, jumpTo, senv, Hashtree.Proofs.RvDispatch.pe,
    Hashtree.Proofs.RvDispatch.syms, Env.nameOf, Addr.plusI, Addr.plus, pure, Except.pure,
    Ctl.add, Ctl.ofInt, Ctl.asInt, State.setG, State.next, Bind.bind, Except.bind, reduceCtorEq,
    rRet, rNum]

/-- The stub's three instructions name the registers they leave alone. -/
theorem sprog_pres (r : Nat) (hr : r = 1 ∨ r = 2 ∨ r = 10 ∨ r = 11 ∨ r = 12) :
    sprog.toList.all (fun i => !writes i r) = true := by
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- **The `hashtree_hash` stub from a concrete state**: with the `.data.rel.local` slot holding a
pointer to `init_and_hash`, the three instructions halt after 3 steps with
`tail = some "init_and_hash"`, without changing memory or `err`, and leaving `ra`, `sp` and the
three argument registers `a0`-`a2` untouched. -/
theorem stub_run (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int)
    (hh : s.halted = false) (hpc : s.pc = 0) (hglen : s.gpr.length = 32)
    (hsl : loadVal mem0c s (⟨60, 0⟩ : Addr Int) = .ok (.ptr (⟨6, 0⟩ : Addr Int))) :
    (run sprog senv mem0c orc 3 s).halted = true ∧
      (run sprog senv mem0c orc 3 s).tail = some "init_and_hash" ∧
      (run sprog senv mem0c orc 3 s).err = s.err ∧
      (run sprog senv mem0c orc 3 s).mem = s.mem ∧
      (run sprog senv mem0c orc 3 s).getG 1 = s.getG 1 ∧
      (run sprog senv mem0c orc 3 s).getG 2 = s.getG 2 ∧
      (run sprog senv mem0c orc 3 s).getG 10 = s.getG 10 ∧
      (run sprog senv mem0c orc 3 s).getG 11 = s.getG 11 ∧
      (run sprog senv mem0c orc 3 s).getG 12 = s.getG 12 := by
  let s1 := exec senv mem0c orc (.auipc 15 (.sym ".data.rel.local" 0)) s
  let s2 := exec senv mem0c orc (.ld 15 15 0) s1
  let s3 := exec senv mem0c orc (.jalr 0 15 0) s2
  have e1 := stub_auipc mem0c orc s hh
  have e1h : s1.halted = false := by dsimp only [s1]; rw [e1]; exact hh
  have e1pc : s1.pc = 1 := by dsimp only [s1]; rw [e1]; simp [hpc]
  have e1len : s1.gpr.length = 32 := by dsimp only [s1]; rw [e1, List.length_set, hglen]
  have e1a : s1.getG 15 = .ptr (⟨60, 0⟩ : Addr Int) := by
    dsimp only [s1]; rw [e1]
    exact rec_getG_self s 15 _ (by rw [hglen]; decide)
  have e1mem : s1.mem = s.mem := by dsimp only [s1]; rw [e1]
  have hsl1 : loadVal mem0c s1 (⟨60, 0⟩ : Addr Int) = .ok (.ptr (⟨6, 0⟩ : Addr Int)) := by
    rw [loadVal_mem_congr mem0c s1 s e1mem]; exact hsl
  have e2 := stub_ld mem0c orc s1 (.ptr (⟨6, 0⟩ : Addr Int)) e1h e1a hsl1
  have e2h : s2.halted = false := by dsimp only [s2]; rw [e2]; exact e1h
  have e2pc : s2.pc = 2 := by dsimp only [s2]; rw [e2]; simp [e1pc]
  have e2len : s2.gpr.length = 32 := by dsimp only [s2]; rw [e2, List.length_set, e1len]
  have e2a : s2.getG 15 = .ptr (⟨6, 0⟩ : Addr Int) := by
    dsimp only [s2]; rw [e2]
    exact rec_getG_self s1 15 _ (by rw [e1len]; decide)
  have e2mem : s2.mem = s.mem := by
    dsimp only [s2]; rw [e2]; dsimp only [s1]; rw [e1]
  have e1err : s1.err = s.err := by dsimp only [s1]; rw [e1]
  have e2err : s2.err = s.err := by
    dsimp only [s2]; rw [e2]; dsimp only [s1]; rw [e1]
  have e3 := stub_jalr mem0c orc s2 e2h e2a
  have r1 : run sprog senv mem0c orc 1 s = s1 :=
    run_one sprog senv mem0c orc s (.auipc 15 (.sym ".data.rel.local" 0)) hh
      (by rw [hpc]; decide +kernel)
  have r2 : run sprog senv mem0c orc 2 s = s2 := by
    rw [show (2 : Nat) = 1 + 1 by rfl, rvRun_add, r1]
    rw [run_one sprog senv mem0c orc s1 (.ld 15 15 0) e1h (by rw [e1pc]; decide +kernel)]
  have r3 : run sprog senv mem0c orc 3 s = s3 := by
    rw [show (3 : Nat) = 2 + 1 by rfl, rvRun_add, r2]
    rw [run_one sprog senv mem0c orc s2 (.jalr 0 15 0) e2h (by rw [e2pc]; decide +kernel)]
  have h3 : s3 = haltTail s2 "init_and_hash" := by dsimp only [s3]; rw [e3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r3]; dsimp only [s3]; rw [e3]; simp [haltTail]
  · rw [r3]; dsimp only [s3]; rw [e3]; simp [haltTail]
  · rw [r3]; dsimp only [s3]; rw [e3]; simp [haltTail]; exact e2err
  · rw [r3]; dsimp only [s3]; rw [e3]; simp [haltTail]; exact e2mem
  · exact run_gpr sprog senv mem0c orc s 1 (sprog_pres 1 (Or.inl rfl)) 3
  · exact run_gpr sprog senv mem0c orc s 2 (sprog_pres 2 (Or.inr (Or.inl rfl))) 3
  · exact run_gpr sprog senv mem0c orc s 10 (sprog_pres 10 (Or.inr (Or.inr (Or.inl rfl)))) 3
  · exact run_gpr sprog senv mem0c orc s 11 (sprog_pres 11 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) 3
  · exact run_gpr sprog senv mem0c orc s 12 (sprog_pres 12 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) 3


/-! ## The epilogue and the B7 stack-alignment invariant -/

/-- `addi sp, sp, 8` -/
theorem exec_addi_sp_p8 (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : State W32 Int) (sp0 : Int) (hh : s.halted = false)
    (hsp : s.getG 2 = .ptr ⟨rStack, sp0⟩) :
    exec wenv mem0c orc (.addi 2 2 8) s =
      { s with gpr := s.gpr.set 2 (.ptr ⟨rStack, sp0 + 8⟩), pc := s.pc + 1 } := by
  simp [exec, hh, okOr, addVal, ctlOf, rget, hsp, rset, State.setG, State.next, lanesOfInt,
    Addr.plus, Ctl.add, Ctl.ofInt, rStack, rNum, sint64]
  rfl

/-- **The wrapper epilogue** (instructions 8-10): once `hashtree_hash` has returned to the return
point 8 with `sp` still at the callee entry `cs` and the caller's `ra` still in the ra slot at
`⟨rStack, cs⟩`, the three instructions halt, restore `ra` from the slot and `sp` to
`sp0 = cs + 8` (the ABI0 entry stack pointer), leaving no tail. -/
theorem wrapper_epilogue (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : State W32 Int) (sp0 cs : Int)
    (hh : s.halted = false) (hpc : s.pc = 8) (htail : s.tail = none) (herr : s.err = none)
    (hglen : s.gpr.length = 32)
    (hsp : s.getG 2 = .ptr ⟨rStack, cs⟩)
    (hsave : loadVal mem0c s ⟨rStack, cs⟩ = .ok (.ptr ⟨rRet, 0⟩))
    (hcs : sp0 = cs + 8) :
    (run prog wenv mem0c orc 3 s).halted = true ∧
      (run prog wenv mem0c orc 3 s).tail = none ∧
      (run prog wenv mem0c orc 3 s).err = none ∧
      (run prog wenv mem0c orc 3 s).getG 1 = .ptr ⟨rRet, 0⟩ ∧
      (run prog wenv mem0c orc 3 s).getG 2 = .ptr ⟨rStack, sp0⟩ := by
  let s9 := exec wenv mem0c orc (.ld 1 2 0) s
  let s10 := exec wenv mem0c orc (.addi 2 2 8) s9
  let s11 := exec wenv mem0c orc (.jalr 0 1 0) s10
  have e1 := exec_ld mem0c orc wenv s 1 2 0 cs (.ptr ⟨rRet, 0⟩) (by decide) (by decide) hh hsp
    (by simpa using hsave)
  have e1h : s9.halted = false := by dsimp only [s9]; rw [e1]; exact hh
  have e1pc : s9.pc = 9 := by dsimp only [s9]; rw [e1]; simp [hpc]
  have e1len : s9.gpr.length = 32 := by dsimp only [s9]; rw [e1, List.length_set, hglen]
  have e1ra : s9.getG 1 = .ptr ⟨rRet, 0⟩ := by
    dsimp only [s9]; rw [e1]
    exact rec_getG_self s 1 _ (by rw [hglen]; decide)
  have e1sp : s9.getG 2 = s.getG 2 := by
    dsimp only [s9]; rw [e1]; exact rec_getG_ne s 1 _ 2 (by decide)
  have e1tail : s9.tail = none := by dsimp only [s9]; rw [e1]; exact htail
  have e1err : s9.err = none := by dsimp only [s9]; rw [e1]; exact herr
  have e2 := exec_addi_sp_p8 mem0c orc s9 cs e1h (e1sp.trans hsp)
  have e2h : s10.halted = false := by dsimp only [s10]; rw [e2]; exact e1h
  have e2pc : s10.pc = 10 := by dsimp only [s10]; rw [e2]; simp [e1pc]
  have e2ra : s10.getG 1 = .ptr ⟨rRet, 0⟩ := by
    dsimp only [s10]; rw [e2]
    exact (rec_getG_ne s9 2 _ 1 (by decide)).trans e1ra
  have e2sp : s10.getG 2 = .ptr ⟨rStack, cs + 8⟩ := by
    dsimp only [s10]; rw [e2]
    exact rec_getG_self s9 2 _ (by rw [e1len]; decide)
  have e2tail : s10.tail = none := by dsimp only [s10]; rw [e2]; exact e1tail
  have e2err : s10.err = none := by dsimp only [s10]; rw [e2]; exact e1err
  have e3 := exec_ret mem0c orc s10 e2h e2ra
  have r1 : run prog wenv mem0c orc 1 s = s9 :=
    run_one prog wenv mem0c orc s (.ld 1 2 0) hh (by rw [hpc]; decide +kernel)
  have r2 : run prog wenv mem0c orc 2 s = s10 := by
    rw [show (2 : Nat) = 1 + 1 by rfl, rvRun_add, r1]
    rw [run_one prog wenv mem0c orc s9 (.addi 2 2 8) e1h (by rw [e1pc]; decide +kernel)]
  have r3 : run prog wenv mem0c orc 3 s = s11 := by
    rw [show (3 : Nat) = 2 + 1 by rfl, rvRun_add, r2]
    rw [run_one prog wenv mem0c orc s10 (.jalr 0 1 0) e2h (by rw [e2pc]; decide +kernel)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [r3]; dsimp only [s11]; rw [e3]; simp [halt]
  · rw [r3]; dsimp only [s11]; rw [e3]; simp [halt]; exact e2tail
  · rw [r3]; dsimp only [s11]; rw [e3]; simp [halt]; exact e2err
  · rw [r3]; dsimp only [s11]; rw [e3]; simp [halt]; exact e2ra
  · rw [r3]; dsimp only [s11]; rw [e3, halt_getG s10 2]
    rw [e2sp, hcs]

/-- **B7, the Go->asm stack-alignment invariant**: at a Go ABI0 call the stack pointer is
`8 mod 16`; after the wrapper's 8-byte frame (`sp0 + (-8)`, the callee's entry stack) it is
`0 mod 16`, which is what the RISC-V psABI requires of a function entry. -/
theorem b7_entry (sp0 : Int) (h : sp0 % 16 = 8) : (sp0 + (-8)) % 16 = 0 := by omega

theorem b7_callee (sp0 : Int) (h : (sp0 + (-8)) % 16 = 0) : sp0 % 16 = 8 := by omega

/-- The B7 instance at the concrete ABI0 entry `sp = 8`. -/
theorem b7_concrete : ((8 : Int) + (-8)) % 16 = 0 := by decide


/-! ## The concrete ABI0 entry, the call boundary and the end-to-end run -/

/-- The concrete memory: the ABI0 argument frame of `entryC` plus the `hashtree_hash` GOT slot
(region 60, bytes `[0, 8)`) holding a pointer to `init_and_hash`. -/
def cMem : Addr Int → Cell W32 Int := fun a =>
  if a.region = 60 ∧ 0 ≤ a.off ∧ a.off < 8 then .pb ⟨6, 0⟩ a.off.toNat else memC a

/-- The wrapper's prefix at the concrete ABI0 entry `SPe = 8`, on `cMem`. -/
theorem prefixC  :
    (run prog wenv cMem (fun _ => false) 8 entryC).halted = true ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).tail = some "call:hashtree_hash" ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).err = none ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).pc = 8 ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).getG 1 = .ptr ⟨rWcode, 8⟩ ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).getG 2 = .ptr ⟨rStack, 8 + (-8)⟩ ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).getG 10 = .ptr cOut ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).getG 11 = .ptr cIn ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).getG 12 = .ptr ⟨rNum, 3⟩ ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).gpr.length = 32 :=
  wrapper_prefix cMem (fun _ => false) 8 cOut cIn cCount entryC
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl)

/-- The state the callee starts in: the wrapper's call state with `pc` reset. -/
def calleeEntry (s : State W32 Int) : State W32 Int :=
  { s with pc := 0, halted := false, tail := none }

theorem calleeEntry_getG (s : State W32 Int) (r : Nat) : (calleeEntry s).getG r = s.getG r := rfl

theorem calleeEntry_len (s : State W32 Int) : (calleeEntry s).gpr.length = s.gpr.length := rfl

theorem calleeEntry_mem (s : State W32 Int) : (calleeEntry s).mem = s.mem := rfl

theorem calleeEntry_halted (s : State W32 Int) : (calleeEntry s).halted = false := rfl

theorem calleeEntry_pc (s : State W32 Int) : (calleeEntry s).pc = 0 := rfl

/-- **`hashtree_hash` at the wrapper's call: it tail-calls `init_and_hash`.**  From the wrapper's
call state (registers and memory of the CALL boundary, `pc` reset to 0), with the `.data.rel.local`
slot pointing at `init_and_hash`, the stub halts on `tail = some "init_and_hash"`, without writing
memory and without changing `ra`, `sp` or the argument registers.  (This is the concrete-state form
of `RvDispatch.stub_correct`, which is stated over the all-location-variable entry.) -/
theorem stub_at_call (mem0c : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int)
    (hglen : s.gpr.length = 32)
    (hsl : loadVal mem0c s (⟨60, 0⟩ : Addr Int) = .ok (.ptr (⟨6, 0⟩ : Addr Int))) :
    (run sprog senv mem0c orc 3 (calleeEntry s)).halted = true ∧
      (run sprog senv mem0c orc 3 (calleeEntry s)).tail = some "init_and_hash" ∧
      (run sprog senv mem0c orc 3 (calleeEntry s)).mem = s.mem ∧
      (run sprog senv mem0c orc 3 (calleeEntry s)).getG 1 = s.getG 1 ∧
      (run sprog senv mem0c orc 3 (calleeEntry s)).getG 2 = s.getG 2 ∧
      (run sprog senv mem0c orc 3 (calleeEntry s)).getG 10 = s.getG 10 ∧
      (run sprog senv mem0c orc 3 (calleeEntry s)).getG 11 = s.getG 11 ∧
      (run sprog senv mem0c orc 3 (calleeEntry s)).getG 12 = s.getG 12 := by
  have h := stub_run mem0c orc (calleeEntry s) (calleeEntry_halted s) (calleeEntry_pc s)
    (by rw [calleeEntry_len]; exact hglen) (by dsimp only [calleeEntry]; exact hsl)
  refine ⟨h.1, h.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.2.2.2.1]; exact (calleeEntry_mem s).symm ▸ rfl
  · exact h.2.2.2.2.1.trans (calleeEntry_getG s 1)
  · exact h.2.2.2.2.2.1.trans (calleeEntry_getG s 2)
  · exact h.2.2.2.2.2.2.1.trans (calleeEntry_getG s 10)
  · exact h.2.2.2.2.2.2.2.1.trans (calleeEntry_getG s 11)
  · exact h.2.2.2.2.2.2.2.2.trans (calleeEntry_getG s 12)

/-- The wrapper state at the return point after the callee has returned. -/
def returned (s : State W32 Int) : State W32 Int := { s with pc := 8, halted := false, tail := none }

theorem returned_getG (s : State W32 Int) (r : Nat) : (returned s).getG r = s.getG r := rfl

theorem returned_len (s : State W32 Int) : (returned s).gpr.length = s.gpr.length := rfl

theorem returned_halted (s : State W32 Int) : (returned s).halted = false := rfl

theorem returned_pc (s : State W32 Int) : (returned s).pc = 8 := rfl

theorem returned_tail (s : State W32 Int) : (returned s).tail = none := rfl

/-- **The wrapper end to end** (concrete ABI0 entry `SPe = 8`): after 8 steps the wrapper is at the
`CALL hashtree_hash` with the three arguments in `a0`-`a2` and the callee stack pointer
`SPe - 8` (`0 mod 16`, B7); the stub then tail-calls `init_and_hash` without touching `ra`, `sp`,
the arguments or memory; and once `init_and_hash` returns to the return point, the epilogue halts
with `ra` reloaded from the ra slot and `sp` restored to `SPe = 8`. -/
theorem wrapper_end2end
    (hslot : loadVal cMem (run prog wenv cMem (fun _ => false) 8 entryC) (⟨60, 0⟩ : Addr Int) =
      .ok (.ptr (⟨6, 0⟩ : Addr Int)))
    (hsave : loadVal cMem (returned (run prog wenv cMem (fun _ => false) 8 entryC)) (⟨rStack, 0⟩ : Addr Int) =
      .ok (.ptr ⟨rRet, 0⟩)) :
    (run prog wenv cMem (fun _ => false) 8 entryC).halted = true ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).tail = some "call:hashtree_hash" ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).getG 10 = .ptr cOut ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).getG 11 = .ptr cIn ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).getG 12 = .ptr ⟨rNum, 3⟩ ∧
      (run prog wenv cMem (fun _ => false) 8 entryC).getG 2 = .ptr ⟨rStack, 0⟩ ∧
      (run sprog senv cMem (fun _ => false) 3 (calleeEntry (run prog wenv cMem (fun _ => false) 8 entryC))).tail =
        some "init_and_hash" ∧
      (run sprog senv cMem (fun _ => false) 3 (calleeEntry (run prog wenv cMem (fun _ => false) 8 entryC))).mem =
        (run prog wenv cMem (fun _ => false) 8 entryC).mem ∧
      (run sprog senv cMem (fun _ => false) 3 (calleeEntry (run prog wenv cMem (fun _ => false) 8 entryC))).getG 1 =
        (run prog wenv cMem (fun _ => false) 8 entryC).getG 1 ∧
      (run prog wenv cMem (fun _ => false) 3 (returned (run prog wenv cMem (fun _ => false) 8 entryC))).halted = true ∧
      (run prog wenv cMem (fun _ => false) 3 (returned (run prog wenv cMem (fun _ => false) 8 entryC))).getG 1 =
        .ptr ⟨rRet, 0⟩ ∧
      (run prog wenv cMem (fun _ => false) 3 (returned (run prog wenv cMem (fun _ => false) 8 entryC))).getG 2 =
        .ptr ⟨rStack, 8⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := prefixC
  have hzero : (8 : Int) + (-8) = 0 := by decide
  rw [hzero] at h6
  have hstub := stub_at_call cMem (fun _ => false) (run prog wenv cMem (fun _ => false) 8 entryC) h10 hslot
  have hepi := wrapper_epilogue cMem (fun _ => false) (returned (run prog wenv cMem (fun _ => false) 8 entryC)) 8 0
    (returned_halted _) (returned_pc _) (returned_tail _) (by dsimp only [returned]; exact h3)
    (by rw [returned_len]; exact h10)
    (by rw [returned_getG]; exact h6)
    hsave (by decide)
  exact ⟨h1, h2, h7, h8, h9, h6, hstub.2.1, hstub.2.2.1, hstub.2.2.2.1, hepi.1, hepi.2.2.2.1, hepi.2.2.2.2⟩

end Hashtree.Proofs.RvWrapperLinux
