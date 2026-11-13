import Hashtree.Proofs.AvxX1W
import Hashtree.Proofs.WrapperPre

/-!
# Entry-prefix facts for the AVX-x1 kernel

The x1 program starts with eight instructions that never read the flags
(`nop`, six `push`, and `sub 64, rsp, 88`); the `sub` clears them.  A tail
call into x1 therefore may arrive with arbitrary flags, and the first eight
steps compute the same state from any two states that agree on everything
but the flags.

This file collects the per-instruction facts needed to unroll those eight
steps: flag-irrelevance of each prefix instruction and register/halted/pc
preservation for `nop` and `push`.
-/

set_option maxRecDepth 1000000

namespace Hashtree.Proofs.AvxX1W
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW

theorem exec_nop_flags (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : CState) (f : Option (Int × Int)) (hh : s.halted = false) :
    exec ro m orc .nop {s with flags := f} = {exec ro m orc .nop s with flags := f} := by
  simp only [exec, hh, Bool.false_eq_true, ite_false, State.next]

theorem exec_push_flags (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (f : Option (Int × Int)) (hh : s.halted = false)
    (sp q : Addr Int) (hsp : s.getG rsp = .ptr sp) (hrp : s.getG r = .ptr q) :
    exec ro m orc (.push r) {s with flags := f} = {exec ro m orc (.push r) s with flags := f} := by
  have hsp' : s.gpr.getD rsp (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
  have hrp' : s.gpr.getD r (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr q := hrp
  simp only [exec, hh, Bool.false_eq_true, ite_false, okOr, State.getG]
  rw [hsp', hrp']
  simp only [storeVal, State.setG, State.next]
  dsimp only [pure, Except.pure]
  simp [hh]

theorem exec_sub88_flags (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : CState) (f : Option (Int × Int)) (hh : s.halted = false)
    (sp : Addr Int) (hsp : s.getG 4 = .ptr sp) :
    exec ro m orc (.sub 64 4 (.imm 88)) {s with flags := f}
      = exec ro m orc (.sub 64 4 (.imm 88)) s := by
  have hsp' : s.gpr.getD 4 (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
  simp only [exec, hh, Bool.false_eq_true, ite_false, okOr, gCtl, State.getG]
  rw [hsp']
  dsimp only [pure, Except.pure, Bind.bind, Except.bind]
  simp [hh, State.setG, setFlags, State.next]

/-- `getG` facts used to track the registers across the entry prefix. -/
theorem storeLane_getG {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (a : Addr γ) (x : α)
    (i : Nat) : (storeLane s a x).getG i = s.getG i := rfl

theorem storeLanes_getG {α γ : Type} [Lane α] [Ctl γ] :
    ∀ (xs : List α) (s : State α γ) (a : Addr γ) (i : Nat), (storeLanes s a xs).getG i = s.getG i
  | [], _, _, _ => rfl
  | x :: xs, s, a, i => by
    simp only [storeLanes, storeLane_getG, storeLanes_getG xs]

theorem next_getG {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (i : Nat) :
    s.next.getG i = s.getG i := rfl

theorem next_pc {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) : s.next.pc = s.pc + 1 := rfl

theorem next_halted {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) :
    s.next.halted = s.halted := rfl

theorem setG_getG_ne {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (i j : Nat) (v : Val α γ)
    (h : i ≠ j) : (s.setG j v).getG i = s.getG i := by
  simp [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem exec_nop_getG (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Nat) (s : CState) : (exec ro m orc .nop s).getG i = s.getG i := by
  cases hh : s.halted
  · have e : exec ro m orc .nop s = State.next s := by simp [exec, hh]
    rw [e]; simp only [next_getG]
  · have e : exec ro m orc .nop s = s := by simp [exec, hh]
    rw [e]

theorem exec_nop_halted (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : CState) (hh : s.halted = false) : (exec ro m orc .nop s).halted = false := by
  simp [exec, hh, next_halted]

theorem exec_nop_pc (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : CState) (hh : s.halted = false) : (exec ro m orc .nop s).pc = s.pc + 1 := by
  simp [exec, hh, next_pc]

theorem exec_push_getG (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r i : Nat) (hi : i ≠ rsp) (s : CState) : (exec ro m orc (.push r) s).getG i = s.getG i := by
  cases hh : s.halted
  · cases hsp : s.getG rsp
    · have e : exec ro m orc (.push r) s = s.fail "rsp not a pointer" := by
        simp only [exec, hh, hsp, okOr, throw_eq, Bool.false_eq_true, ite_false]
      rw [e, State.fail]
      cases hs : s.err <;> simp [State.getG]
    · rename_i sp
      have e : exec ro m orc (.push r) s
          = ((storeVal s (sp.plusI (-8)) (s.getG r)).setG rsp (.ptr (sp.plusI (-8)))).next := by
        simp only [exec, hh, hsp, okOr, pure_ok, Bool.false_eq_true, ite_false]
      rw [e, next_getG]
      cases hr : s.getG r
      · simp only [storeVal]
        rw [setG_getG_ne _ _ _ _ hi]
        simp only [storeLane_getG]
      · simp only [storeVal]
        rw [setG_getG_ne _ _ _ _ hi]
        rfl
  · have e : exec ro m orc (.push r) s = s := by simp [exec, hh]
    rw [e]


theorem exec_push_ptr (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp q : Addr Int) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) (hrp : s.getG r = .ptr q) :
    exec ro m orc (.push r) s
      = ((storeVal s (sp.plusI (-8)) (.ptr q)).setG rsp (.ptr (sp.plusI (-8)))).next := by
  have hsp' : s.gpr.getD rsp (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
  have hrp' : s.gpr.getD r (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr q := hrp
  simp only [exec, hh, Bool.false_eq_true, ite_false, okOr, State.getG]
  rw [hsp', hrp']
  simp only [storeVal]
  dsimp only [pure, Except.pure]

theorem exec_push_ptr_halted (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp q : Addr Int) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) (hrp : s.getG r = .ptr q) :
    (exec ro m orc (.push r) s).halted = false := by
  rw [exec_push_ptr ro m orc r s sp q hh hsp hrp]
  show ((storeVal s (sp.plusI (-8)) (Val.ptr q)).setG rsp (Val.ptr (sp.plusI (-8)))).next.halted = false
  rw [next_halted]
  exact hh

theorem exec_push_ptr_pc (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp q : Addr Int) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) (hrp : s.getG r = .ptr q) :
    (exec ro m orc (.push r) s).pc = s.pc + 1 := by
  rw [exec_push_ptr ro m orc r s sp q hh hsp hrp]
  show ((storeVal s (sp.plusI (-8)) (Val.ptr q)).setG rsp (Val.ptr (sp.plusI (-8)))).next.pc = s.pc + 1
  rw [next_pc]
  rfl

theorem setG_getG_self {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (i : Nat) (v : Val α γ)
    (h : i < s.gpr.length) : (s.setG i v).getG i = v := by
  simp [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set_self h]

theorem setG_length {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (i : Nat) (v : Val α γ) :
    (s.setG i v).gpr.length = s.gpr.length := by simp [State.setG]

theorem exec_push_ptr_rsp (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp q : Addr Int) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) (hrp : s.getG r = .ptr q) (hg : rsp < s.gpr.length) :
    (exec ro m orc (.push r) s).getG rsp = .ptr (sp.plusI (-8)) := by
  rw [exec_push_ptr ro m orc r s sp q hh hsp hrp]
  show (((storeVal s (sp.plusI (-8)) (Val.ptr q)).setG rsp (Val.ptr (sp.plusI (-8)))).next).getG rsp
    = Val.ptr (sp.plusI (-8))
  rw [next_getG]
  exact setG_getG_self _ _ _ (by simpa [storeVal, State.setG] using hg)

theorem storeLane_flags {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (a : Addr γ) (x : α)
    (f : Option (γ × γ)) : storeLane {s with flags := f} a x = {storeLane s a x with flags := f} := rfl

theorem storeVal_flags {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (a : Addr γ) (v : Val α γ)
    (f : Option (γ × γ)) : storeVal {s with flags := f} a v = {storeVal s a v with flags := f} := by
  cases v <;> rfl

theorem setG_flags {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (i : Nat) (v : Val α γ)
    (f : Option (γ × γ)) : ({s with flags := f} : State α γ).setG i v = {s.setG i v with flags := f} := rfl

theorem next_flags {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (f : Option (γ × γ)) :
    {s with flags := f}.next = {s.next with flags := f} := rfl

theorem getG_flags {α γ : Type} [Lane α] [Ctl γ] (s : State α γ) (i : Nat) (f : Option (γ × γ)) :
    ({s with flags := f} : State α γ).getG i = s.getG i := rfl

theorem exec_push_flags2 (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (f : Option (Int × Int)) (hh : s.halted = false)
    (sp : Addr Int) (hsp : s.getG rsp = .ptr sp) :
    exec ro m orc (.push r) {s with flags := f} = {exec ro m orc (.push r) s with flags := f} := by
  have hh' : ({s with flags := f} : CState).halted = false := hh
  cases hr : s.getG r
  · rename_i lo hi
    have hr' : ({s with flags := f} : CState).getG r = .num lo hi := hr
    have hsp' : ({s with flags := f} : CState).getG rsp = .ptr sp := hsp
    have eR : exec ro m orc (.push r) s
        = ((storeVal s (sp.plusI (-8)) (.num lo hi)).setG rsp (.ptr (sp.plusI (-8)))).next := by
      have h4 : s.gpr.getD rsp (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
      have h5 : s.gpr.getD r (Val.num (Lane.const 0) (Lane.const 0)) = Val.num lo hi := hr
      simp only [exec, hh, Bool.false_eq_true, ite_false, okOr, State.getG]
      rw [h4, h5]
      simp only [storeVal]
      dsimp only [pure, Except.pure]
    have eL : exec ro m orc (.push r) {s with flags := f}
        = ((storeVal {s with flags := f} (sp.plusI (-8)) (.num lo hi)).setG rsp (.ptr (sp.plusI (-8)))).next := by
      have h4 : ({s with flags := f} : CState).gpr.getD rsp (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
      have h5 : ({s with flags := f} : CState).gpr.getD r (Val.num (Lane.const 0) (Lane.const 0)) = Val.num lo hi := hr
      simp only [exec, hh, hh', Bool.false_eq_true, ite_false, okOr, State.getG]
      rw [h4, h5]
      simp only [storeVal]
      dsimp only [pure, Except.pure]
    rw [eL, eR, storeVal_flags, setG_flags, next_flags]
  · rename_i a
    have hr' : ({s with flags := f} : CState).getG r = .ptr a := hr
    have hsp' : ({s with flags := f} : CState).getG rsp = .ptr sp := hsp
    have eR : exec ro m orc (.push r) s
        = ((storeVal s (sp.plusI (-8)) (.ptr a)).setG rsp (.ptr (sp.plusI (-8)))).next := by
      have h4 : s.gpr.getD rsp (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
      have h5 : s.gpr.getD r (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr a := hr
      simp only [exec, hh, Bool.false_eq_true, ite_false, okOr, State.getG]
      rw [h4, h5]
      simp only [storeVal]
      dsimp only [pure, Except.pure]
    have eL : exec ro m orc (.push r) {s with flags := f}
        = ((storeVal {s with flags := f} (sp.plusI (-8)) (.ptr a)).setG rsp (.ptr (sp.plusI (-8)))).next := by
      have h4 : ({s with flags := f} : CState).gpr.getD rsp (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
      have h5 : ({s with flags := f} : CState).gpr.getD r (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr a := hr
      simp only [exec, hh, hh', Bool.false_eq_true, ite_false, okOr, State.getG]
      rw [h4, h5]
      simp only [storeVal]
      dsimp only [pure, Except.pure]
    rw [eL, eR, storeVal_flags, setG_flags, next_flags]


theorem exec_push_num (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp : Addr Int) (lo hi : W32) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) (hr : s.getG r = .num lo hi) :
    exec ro m orc (.push r) s
      = ((storeVal s (sp.plusI (-8)) (.num lo hi)).setG rsp (.ptr (sp.plusI (-8)))).next := by
  have h4 : s.gpr.getD rsp (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
  have h5 : s.gpr.getD r (Val.num (Lane.const 0) (Lane.const 0)) = Val.num lo hi := hr
  simp only [exec, hh, Bool.false_eq_true, ite_false, okOr, State.getG]
  rw [h4, h5]
  simp only [storeVal]
  dsimp only [pure, Except.pure]

theorem exec_push_sm (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp : Addr Int) (p : Addr Int) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) (hr : s.getG r = .ptr p) :
    exec ro m orc (.push r) s
      = ((storeVal s (sp.plusI (-8)) (.ptr p)).setG rsp (.ptr (sp.plusI (-8)))).next := by
  have h4 : s.gpr.getD rsp (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
  have h5 : s.gpr.getD r (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr p := hr
  simp only [exec, hh, Bool.false_eq_true, ite_false, okOr, State.getG]
  rw [h4, h5]
  simp only [storeVal]
  dsimp only [pure, Except.pure]

theorem exec_push_halted2 (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp : Addr Int) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) : (exec ro m orc (.push r) s).halted = false := by
  cases hr : s.getG r
  · rename_i lo hi
    rw [exec_push_num ro m orc r s sp lo hi hh hsp hr]
    show ((storeVal s (sp.plusI (-8)) (Val.num lo hi)).setG rsp (Val.ptr (sp.plusI (-8)))).next.halted = false
    rw [next_halted]
    exact hh
  · rename_i p
    rw [exec_push_sm ro m orc r s sp p hh hsp hr]
    show ((storeVal s (sp.plusI (-8)) (Val.ptr p)).setG rsp (Val.ptr (sp.plusI (-8)))).next.halted = false
    rw [next_halted]
    exact hh

theorem exec_push_pc2 (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp : Addr Int) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) : (exec ro m orc (.push r) s).pc = s.pc + 1 := by
  cases hr : s.getG r
  · rename_i lo hi
    rw [exec_push_num ro m orc r s sp lo hi hh hsp hr]
    show ((storeVal s (sp.plusI (-8)) (Val.num lo hi)).setG rsp (Val.ptr (sp.plusI (-8)))).next.pc = s.pc + 1
    rw [next_pc]
    rfl
  · rename_i p
    rw [exec_push_sm ro m orc r s sp p hh hsp hr]
    show ((storeVal s (sp.plusI (-8)) (Val.ptr p)).setG rsp (Val.ptr (sp.plusI (-8)))).next.pc = s.pc + 1
    rw [next_pc]
    rfl

theorem exec_push_rsp2 (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp : Addr Int) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) (hg : rsp < s.gpr.length) :
    (exec ro m orc (.push r) s).getG rsp = .ptr (sp.plusI (-8)) := by
  cases hr : s.getG r
  · rename_i lo hi
    rw [exec_push_num ro m orc r s sp lo hi hh hsp hr]
    show ((storeVal s (sp.plusI (-8)) (Val.num lo hi)).setG rsp (Val.ptr (sp.plusI (-8)))).next.getG rsp
      = Val.ptr (sp.plusI (-8))
    rw [next_getG]
    exact setG_getG_self _ _ _ (by simpa [storeVal, storeLane, State.setG] using hg)
  · rename_i p
    rw [exec_push_sm ro m orc r s sp p hh hsp hr]
    show ((storeVal s (sp.plusI (-8)) (Val.ptr p)).setG rsp (Val.ptr (sp.plusI (-8)))).next.getG rsp
      = Val.ptr (sp.plusI (-8))
    rw [next_getG]
    exact setG_getG_self _ _ _ (by simpa [storeVal, storeLane, State.setG] using hg)

theorem exec_push_len2 (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (r : Nat) (s : CState) (sp : Addr Int) (hh : s.halted = false)
    (hsp : s.getG rsp = .ptr sp) : (exec ro m orc (.push r) s).gpr.length = s.gpr.length := by
  cases hr : s.getG r
  · rename_i lo hi
    rw [exec_push_num ro m orc r s sp lo hi hh hsp hr]
    simp [State.next, State.setG, storeVal, storeLane]
  · rename_i p
    rw [exec_push_sm ro m orc r s sp p hh hsp hr]
    simp [State.next, State.setG, storeVal, storeLane]

theorem exec_nop_len (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : CState) (hh : s.halted = false) : (exec ro m orc .nop s).gpr.length = s.gpr.length := by
  simp [exec, hh, State.next]

theorem exec_sub88_halted (ro : Region) (m : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (s : CState) (hh : s.halted = false) (sp : Addr Int) (hsp : s.getG 4 = .ptr sp) :
    (exec ro m orc (.sub 64 4 (.imm 88)) s).halted = false := by
  have hsp' : s.gpr.getD 4 (Val.num (Lane.const 0) (Lane.const 0)) = Val.ptr sp := hsp
  simp only [exec, hh, Bool.false_eq_true, ite_false, okOr, gCtl, State.getG]
  rw [hsp']
  dsimp only [pure, Except.pure, Bind.bind, Except.bind]
  simp [hh, State.setG, setFlags, State.next]



open Hashtree.Kernels.X86.AvxX1
open Hashtree.Proofs.WrapperAmd64 (run_step)

/-- **The entry prefix ignores the incoming flags.**  After the eight prefix instructions
(`nop`, `push rbx/rbp/r12/r13/r14/r15`, `sub rsp, 88`) the state does not depend on the
flags it started with: the `sub` overwrites them.  Hence a tail call into the x1 kernel may
arrive with flags set by the caller's last comparison; only `sp` (a pointer in `rsp`) and
`rsp < gpr.length` are needed. -/
theorem run8_flags (m : Addr Int → Cell W32 Int) (orc : Nat → Bool) (B : CState)
    (f : Option (Int × Int)) (hpc : B.pc = 0) (hh : B.halted = false)
    (sp : Addr Int) (h4 : B.getG rsp = .ptr sp) (hg : rsp < B.gpr.length) :
    run prog 4 m orc 8 {B with flags := f} = run prog 4 m orc 8 B := by
  let sp1 : Addr Int := sp.plusI (-8)
  let sp2 : Addr Int := sp1.plusI (-8)
  let sp3 : Addr Int := sp2.plusI (-8)
  let sp4 : Addr Int := sp3.plusI (-8)
  let sp5 : Addr Int := sp4.plusI (-8)
  let sp6 : Addr Int := sp5.plusI (-8)
  let sp7 : Addr Int := sp6.plusI (-8)
  let t1 : CState := exec 4 m orc .nop B
  let t2 : CState := exec 4 m orc (.push 3) t1
  let t3 : CState := exec 4 m orc (.push 5) t2
  let t4 : CState := exec 4 m orc (.push 12) t3
  let t5 : CState := exec 4 m orc (.push 13) t4
  let t6 : CState := exec 4 m orc (.push 14) t5
  let t7 : CState := exec 4 m orc (.push 15) t6
  have t1h : t1.halted = false := exec_nop_halted 4 m orc B hh
  have t1pc : t1.pc = 1 := by
    show (exec 4 m orc .nop B).pc = 1
    rw [exec_nop_pc 4 m orc B hh, hpc]
  have t1g : t1.getG rsp = .ptr sp := by
    have h := exec_nop_getG 4 m orc rsp B
    rw [show t1.getG rsp = B.getG rsp from h, h4]
  have t1len : t1.gpr.length = B.gpr.length := exec_nop_len 4 m orc B hh
  have t2h : t2.halted = false := exec_push_halted2 4 m orc 3 t1 sp t1h t1g
  have t2pc : t2.pc = 2 := by
    show (exec 4 m orc (.push 3) t1).pc = 2
    rw [exec_push_pc2 4 m orc 3 t1 sp t1h t1g, t1pc]
  have t2g : t2.getG rsp = .ptr sp1 :=
    exec_push_rsp2 4 m orc 3 t1 sp t1h t1g (by rw [t1len]; exact hg)
  have t2len : t2.gpr.length = B.gpr.length := by
    rw [exec_push_len2 4 m orc 3 t1 sp t1h t1g]; exact t1len
  have t3h : t3.halted = false := exec_push_halted2 4 m orc 5 t2 sp1 t2h t2g
  have t3pc : t3.pc = 3 := by
    show (exec 4 m orc (.push 5) t2).pc = 3
    rw [exec_push_pc2 4 m orc 5 t2 sp1 t2h t2g, t2pc]
  have t3g : t3.getG rsp = .ptr sp2 :=
    exec_push_rsp2 4 m orc 5 t2 sp1 t2h t2g (by rw [t2len]; exact hg)
  have t3len : t3.gpr.length = B.gpr.length := by
    rw [exec_push_len2 4 m orc 5 t2 sp1 t2h t2g]; exact t2len
  have t4h : t4.halted = false := exec_push_halted2 4 m orc 12 t3 sp2 t3h t3g
  have t4pc : t4.pc = 4 := by
    show (exec 4 m orc (.push 12) t3).pc = 4
    rw [exec_push_pc2 4 m orc 12 t3 sp2 t3h t3g, t3pc]
  have t4g : t4.getG rsp = .ptr sp3 :=
    exec_push_rsp2 4 m orc 12 t3 sp2 t3h t3g (by rw [t3len]; exact hg)
  have t4len : t4.gpr.length = B.gpr.length := by
    rw [exec_push_len2 4 m orc 12 t3 sp2 t3h t3g]; exact t3len
  have t5h : t5.halted = false := exec_push_halted2 4 m orc 13 t4 sp3 t4h t4g
  have t5pc : t5.pc = 5 := by
    show (exec 4 m orc (.push 13) t4).pc = 5
    rw [exec_push_pc2 4 m orc 13 t4 sp3 t4h t4g, t4pc]
  have t5g : t5.getG rsp = .ptr sp4 :=
    exec_push_rsp2 4 m orc 13 t4 sp3 t4h t4g (by rw [t4len]; exact hg)
  have t5len : t5.gpr.length = B.gpr.length := by
    rw [exec_push_len2 4 m orc 13 t4 sp3 t4h t4g]; exact t4len
  have t6h : t6.halted = false := exec_push_halted2 4 m orc 14 t5 sp4 t5h t5g
  have t6pc : t6.pc = 6 := by
    show (exec 4 m orc (.push 14) t5).pc = 6
    rw [exec_push_pc2 4 m orc 14 t5 sp4 t5h t5g, t5pc]
  have t6g : t6.getG rsp = .ptr sp5 :=
    exec_push_rsp2 4 m orc 14 t5 sp4 t5h t5g (by rw [t5len]; exact hg)
  have t6len : t6.gpr.length = B.gpr.length := by
    rw [exec_push_len2 4 m orc 14 t5 sp4 t5h t5g]; exact t5len
  have t7h : t7.halted = false := exec_push_halted2 4 m orc 15 t6 sp5 t6h t6g
  have t7pc : t7.pc = 7 := by
    show (exec 4 m orc (.push 15) t6).pc = 7
    rw [exec_push_pc2 4 m orc 15 t6 sp5 t6h t6g, t6pc]
  have t7g : t7.getG rsp = .ptr sp6 :=
    exec_push_rsp2 4 m orc 15 t6 sp5 t6h t6g (by rw [t6len]; exact hg)
  rw [run_step prog m orc 7 {B with flags := f} .nop (by simpa using hh)
    (by rw [show ({B with flags := f} : CState).pc = 0 from hpc]; rfl)]
  rw [exec_nop_flags 4 m orc B f hh]
  rw [run_step prog m orc 6 {t1 with flags := f} (.push 3) (by simpa [t1] using t1h)
    (by rw [show ({t1 with flags := f} : CState).pc = 1 from t1pc]; rfl)]
  rw [exec_push_flags2 4 m orc 3 t1 f t1h sp t1g]
  rw [run_step prog m orc 5 {t2 with flags := f} (.push 5) (by simpa [t2] using t2h)
    (by rw [show ({t2 with flags := f} : CState).pc = 2 from t2pc]; rfl)]
  rw [exec_push_flags2 4 m orc 5 t2 f t2h sp1 t2g]
  rw [run_step prog m orc 4 {t3 with flags := f} (.push 12) (by simpa [t3] using t3h)
    (by rw [show ({t3 with flags := f} : CState).pc = 3 from t3pc]; rfl)]
  rw [exec_push_flags2 4 m orc 12 t3 f t3h sp2 t3g]
  rw [run_step prog m orc 3 {t4 with flags := f} (.push 13) (by simpa [t4] using t4h)
    (by rw [show ({t4 with flags := f} : CState).pc = 4 from t4pc]; rfl)]
  rw [exec_push_flags2 4 m orc 13 t4 f t4h sp3 t4g]
  rw [run_step prog m orc 2 {t5 with flags := f} (.push 14) (by simpa [t5] using t5h)
    (by rw [show ({t5 with flags := f} : CState).pc = 5 from t5pc]; rfl)]
  rw [exec_push_flags2 4 m orc 14 t5 f t5h sp4 t5g]
  rw [run_step prog m orc 1 {t6 with flags := f} (.push 15) (by simpa [t6] using t6h)
    (by rw [show ({t6 with flags := f} : CState).pc = 6 from t6pc]; rfl)]
  rw [exec_push_flags2 4 m orc 15 t6 f t6h sp5 t6g]
  rw [run_step prog m orc 0 {t7 with flags := f} (.sub 64 4 (.imm 88)) (by simpa [t7] using t7h)
    (by rw [show ({t7 with flags := f} : CState).pc = 7 from t7pc]; rfl)]
  rw [exec_sub88_flags 4 m orc t7 f t7h sp6 t7g]
  rw [run_step prog m orc 7 B .nop hh (by rw [hpc]; rfl)]
  rw [run_step prog m orc 6 t1 (.push 3) t1h (by rw [t1pc]; rfl)]
  rw [run_step prog m orc 5 t2 (.push 5) t2h (by rw [t2pc]; rfl)]
  rw [run_step prog m orc 4 t3 (.push 12) t3h (by rw [t3pc]; rfl)]
  rw [run_step prog m orc 3 t4 (.push 13) t4h (by rw [t4pc]; rfl)]
  rw [run_step prog m orc 2 t5 (.push 14) t5h (by rw [t5pc]; rfl)]
  rw [run_step prog m orc 1 t6 (.push 15) t6h (by rw [t6pc]; rfl)]
  rw [run_step prog m orc 0 t7 (.sub 64 4 (.imm 88)) t7h (by rw [t7pc]; rfl)]


end Hashtree.Proofs.AvxX1W
