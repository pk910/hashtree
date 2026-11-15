import Hashtree.Asm.Slice
import Hashtree.Proofs.WinShaniFront
import Hashtree.Proofs.FrameLift
import Hashtree.Kernels.X86Win.SseX1

/-!
# R5: the windows `sse_x1` prologue replay

Eighteen instructions carry the call state to the body entry: nine pushes (`rbx, r8, rsi, rdi,
rbp, r12, r13, r14, r15` at pcs 0-8), `sub rsp, 192` (pc 9) and eight `xmm6`-`xmm13` saves at
`[rsp+64+16m]` (pcs 10-17).  `run_front`: from a state with `rsp = a` at pc 0, the state after
18 steps is `frontSt st a`: `rsp = a - 264`, the flags of the `sub`, the eight save slots at
`a-200..a-88` over the push cells at `a-8..a-72` (newest first), pc 18.
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinSseFront

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.RunExit Hashtree.Asm.MemCells
open Hashtree.Proofs.WinShaniFront (laneLog exec_sub_rsp exec_vstore_rsp run_succ_step)
open Hashtree.Proofs.FrameLift (exec_push getG_setG_rsp storeVal_gpr storeVal_vr storeVal_flags storeVal_pc)

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.SseX1.prog

/-- The pushed registers, in push order. -/
def pushRegs : List Nat := [3, 8, 6, 7, 5, 12, 13, 14, 15]

theorem push_lookup (k : Nat) (hk : k < 9) : winProg[k]? = some (.push (pushRegs.getD k 0)) := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem sub_lookup : winProg[9]? = some (.sub 64 4 (.imm 192)) := by decide +kernel

def saveStep (m : Nat) : Instr := .vstore 4 { base := some 4, disp := ((64 + 16 * m : Nat) : Int) } (6 + m)

theorem save_lookup (m : Nat) (hm : m < 8) : winProg[10 + m]? = some (saveStep m) := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem storeVal_assume (u : State W32 Int) (b : Addr Int) (v : Val W32 Int) : (storeVal u b v).assume = u.assume := by
  cases v <;> rfl

theorem set_set_rsp (l : List (Val W32 Int)) (x y : Val W32 Int) : (l.set 4 x).set rsp y = l.set 4 y := by
  show (l.set 4 x).set 4 y = l.set 4 y
  exact List.set_set x

theorem getElem?_of_getG' (s : State W32 Int) (j : Nat) (hj : j < s.gpr.length) : s.gpr[j]? = some (s.getG j) := by
  rw [List.getElem?_eq_getElem hj]
  simp only [State.getG, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-! ## The pushes -/

/-- The push cells after `k` pushes (newest first) over the tail. -/
def pushLog (st : State W32 Int) (a : Addr Int) : Nat → List (Addr Int × Cell W32 Int) → List (Addr Int × Cell W32 Int)
  | 0, tail => tail
  | k + 1, tail => storeCells (a.plusI (-(8 * (k + 1) : Int))) (st.getG (pushRegs.getD k 0)) ++ pushLog st a k tail

/-- The state after `k` pushes from a state with `rsp = a` at pc 0. -/
def pushSt (st : State W32 Int) (a : Addr Int) (k : Nat) : State W32 Int :=
  { st with gpr := st.gpr.set 4 (.ptr (a.plusI (-(8 * k : Int)))), mem := pushLog st a k st.mem, pc := k }

theorem pushRegs_ne4 (k : Nat) (hk : k < 9) : pushRegs.getD k 0 ≠ 4 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem exec_pushSt (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (hlen : st.gpr.length = 16) (k : Nat) (hk : k < 9) :
    exec 4 mem0 orc (.push (pushRegs.getD k 0)) (pushSt st a k) = pushSt st a (k + 1) := by
  have h4 : (pushSt st a k).getG rsp = .ptr (a.plusI (-(8 * k : Int))) := by
    simp only [pushSt]
    exact getG_setG_rsp st _ (by rw [hlen]; decide)
  have hh' : (pushSt st a k).halted = false := by simp only [pushSt, hh]
  have hg : (pushSt st a k).getG (pushRegs.getD k 0) = st.getG (pushRegs.getD k 0) := by
    simp only [pushSt]
    exact getG_setG_of_ne _ _ _ _ (pushRegs_ne4 k hk)
  have ha : (a.plusI (-(8 * k : Int))).plusI (-8) = a.plusI (-(8 * (k + 1) : Int)) := by
    rw [plusI_int, plusI_int, plusI_int]
    show Addr.mk a.region (a.off + -(8 * (k : Int)) + -8) = Addr.mk a.region (a.off + -(8 * ((k + 1 : Nat) : Int)))
    congr 1; push_cast; omega
  rw [exec_push _ hh' h4, hg, ha]
  simp only [State.next, State.setG, storeVal_gpr, storeVal_vr, storeVal_flags, storeVal_pc,
    Hashtree.Proofs.FrameLift.storeVal_halted, Hashtree.Proofs.FrameLift.storeVal_tail, Hashtree.Proofs.FrameLift.storeVal_err,
    storeVal_assume, storeVal_mem, pushSt, set_set_rsp, pushLog]
  first | rfl | (push_cast; rfl)

theorem run_pushes (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (hlen : st.gpr.length = 16) :
    ∀ (m k : Nat), m + k ≤ 9 → run winProg 4 mem0 orc k (pushSt st a m) = pushSt st a (m + k) := by
  intro m k
  induction k generalizing m with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hm : m < 9 := by omega
    rw [run_succ_step winProg 4 mem0 orc k (pushSt st a m) (.push (pushRegs.getD m 0)) (by simp only [pushSt, hh])
      (by simp only [pushSt]; exact push_lookup m hm)]
    rw [exec_pushSt mem0 orc st a hh hlen m hm, ih (m + 1) (by omega)]
    rw [show (m + 1) + k = m + (k + 1) from by omega]

/-! ## The frame and the saves -/

/-- The save log of `m` slots at `[b+64+16j]` (newest first) over the tail. -/
def saveLog (st : State W32 Int) (b : Addr Int) : Nat → List (Addr Int × Cell W32 Int) → List (Addr Int × Cell W32 Int)
  | 0, tail => tail
  | k + 1, tail => laneLog (b.plusI ((64 + 16 * k : Nat) : Int)) ((st.getV (6 + k)).take 4) ++ saveLog st b k tail

/-- The state after the nine pushes, the `sub` and `m` saves. -/
def frontSt (st : State W32 Int) (a : Addr Int) (m : Nat) : State W32 Int :=
  { gpr := st.gpr.set 4 (.ptr (a.plusI (-264))), vr := st.vr, flags := some (Addr.off (a.plusI (-72)), 192),
    mem := saveLog st (a.plusI (-264)) m (pushLog st a 9 st.mem), pc := 10 + m, halted := st.halted,
    tail := st.tail, err := st.err, assume := st.assume }

theorem exec_frontSt (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (hlen : st.gpr.length = 16) (m : Nat) :
    exec 4 mem0 orc (saveStep m) (frontSt st a m) = frontSt st a (m + 1) := by
  have h4 : (frontSt st a m).getG rsp = .ptr (a.plusI (-264)) := by
    simp only [frontSt]
    exact getG_setG_rsp st _ (by rw [hlen]; decide)
  have hh' : (frontSt st a m).halted = false := by simp only [frontSt, hh]
  rw [show saveStep m = .vstore 4 { base := some rsp, disp := ((64 + 16 * m : Nat) : Int) } (6 + m) from rfl]
  rw [exec_vstore_rsp 4 mem0 orc _ 4 (6 + m) ((64 + 16 * m : Nat) : Int) (a.plusI (-264)) hh' h4]
  simp only [frontSt, saveLog, State.getV]
  rw [show 10 + m + 1 = 10 + (m + 1) from by omega]

theorem run_saves (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (hlen : st.gpr.length = 16) :
    ∀ (m k : Nat), m + k ≤ 8 → run winProg 4 mem0 orc k (frontSt st a m) = frontSt st a (m + k) := by
  intro m k
  induction k generalizing m with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hm : m < 8 := by omega
    rw [run_succ_step winProg 4 mem0 orc k (frontSt st a m) (saveStep m) (by simp only [frontSt, hh])
      (by simp only [frontSt]; exact save_lookup m hm)]
    rw [exec_frontSt mem0 orc st a hh hlen m, ih (m + 1) (by omega)]
    rw [show (m + 1) + k = m + (k + 1) from by omega]

theorem pushSt_zero (st : State W32 Int) (a : Addr Int) (h4 : st.getG rsp = .ptr a) (hlen : st.gpr.length = 16) :
    pushSt st a 0 = { st with pc := 0 } := by
  have e : a.plusI (-(8 * ((0 : Nat) : Int))) = a := by rw [plusI_int]; cases a; simp
  simp only [pushSt, pushLog, e]
  have hs : st.gpr.set 4 (.ptr a) = st.gpr := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i = 4
    · subst hi
      rw [List.getElem?_set_self (by rw [hlen]; decide), getElem?_of_getG' st 4 (by rw [hlen]; decide)]
      exact congrArg some h4.symm
    · exact List.getElem?_set_ne (Ne.symm hi)
  rw [hs]

theorem exec_sub_front (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (hlen : st.gpr.length = 16) :
    exec 4 mem0 orc (.sub 64 4 (.imm 192)) (pushSt st a 9) = frontSt st a 0 := by
  have h4 : (pushSt st a 9).getG rsp = .ptr (a.plusI (-72)) := by
    have e : a.plusI (-(8 * ((9 : Nat) : Int))) = a.plusI (-72) := by
      rw [plusI_int, plusI_int]
      show Addr.mk a.region (a.off + -(8 * ((9 : Nat) : Int))) = Addr.mk a.region (a.off + -72)
      congr 1
      try (push_cast; omega)
    show (st.gpr.set 4 (.ptr (a.plusI (-(8 * ((9 : Nat) : Int)))))).getD 4 (.num (Lane.const 0) (Lane.const 0)) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hlen]; decide), e]
    try rfl
  show exec 4 mem0 orc (.sub 64 rsp (.imm 192)) (pushSt st a 9) = frontSt st a 0
  rw [exec_sub_rsp 4 mem0 orc _ 192 (a.plusI (-72)) (by simp only [pushSt, hh]) h4]
  have ha : (a.plusI (-72)).plusI (-192) = a.plusI (-264) := by
    rw [plusI_int, plusI_int, plusI_int]
    show Addr.mk a.region (a.off + -72 + -192) = Addr.mk a.region (a.off + -264)
    congr 1; omega
  simp only [pushSt, frontSt, saveLog, set_set_rsp, ha]

/-- **The `sse_x1` prologue.** -/
theorem run_front (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (h4 : st.getG rsp = .ptr a) (hlen : st.gpr.length = 16) :
    run winProg 4 mem0 orc 18 { st with pc := 0 } = frontSt st a 8 := by
  rw [← pushSt_zero st a h4 hlen, show (18 : Nat) = 9 + (1 + 8) from rfl, run_add, run_pushes mem0 orc st a hh hlen 0 9 (by omega)]
  rw [run_add, run_succ_step winProg 4 mem0 orc 0 (pushSt st a 9) (.sub 64 4 (.imm 192)) (by simp only [pushSt, hh])
    (by simp only [pushSt]; exact sub_lookup)]
  rw [exec_sub_front mem0 orc st a hh hlen]
  show run winProg 4 mem0 orc 8 (frontSt st a 0) = frontSt st a 8
  exact run_saves mem0 orc st a hh hlen 0 8 (by omega)

end Hashtree.Proofs.WinSseFront
