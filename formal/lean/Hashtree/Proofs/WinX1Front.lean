import Hashtree.Asm.Slice
import Hashtree.Proofs.WinShaniFront
import Hashtree.Proofs.FrameLift

/-!
# R5: the windows x1 prologue replay, generic in the stream

The windows `sse_x1` and `avx_x1` streams share one prologue shape: nine pushes (`rbx, r8, rsi,
rdi, rbp, r12, r13, r14, r15` at pcs `p0 .. p0+8`), `sub rsp, 192` (`p0+9`) and eight `xmm6`-`xmm13`
saves at `[rsp+64+16m]` (`p0+10 .. p0+17`); `sse_x1` has `p0 = 0`, `avx_x1` has an `endbr64` (`nop`)
first and `p0 = 1`.  Everything here is stated for any program whose instructions at those pcs are
these (`hpush`, `hsub`, `hsave`); the two kernels instantiate it (`WinSseFront`, `WinAvxFront`).

`run_front`: from a state with `rsp = a` at pc `p0`, the state after 18 steps is `frontSt p0 st a 8`:
`rsp = a - 264`, the flags of the `sub`, the eight save slots at `a-200..a-88` over the push cells
at `a-8..a-72` (newest first), pc `p0 + 18`.
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinX1Front

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.RunExit Hashtree.Asm.MemCells
open Hashtree.Proofs.WinShaniFront (laneLog exec_sub_rsp exec_vstore_rsp run_succ_step)
open Hashtree.Proofs.FrameLift (exec_push getG_setG_rsp storeVal_gpr storeVal_vr storeVal_flags storeVal_pc)

/-- The pushed registers, in push order. -/
def pushRegs : List Nat := [3, 8, 6, 7, 5, 12, 13, 14, 15]

/-- The `m`-th save: `vstore 4 [rsp + 64 + 16m] xmm{6+m}`. -/
def saveStep (m : Nat) : Instr := .vstore 4 { base := some 4, disp := ((64 + 16 * m : Nat) : Int) } (6 + m)

theorem storeVal_assume (u : State W32 Int) (b : Addr Int) (v : Val W32 Int) : (storeVal u b v).assume = u.assume := by
  cases v <;> rfl

theorem set_set_rsp (l : List (Val W32 Int)) (x y : Val W32 Int) : (l.set 4 x).set rsp y = l.set 4 y := by
  show (l.set 4 x).set 4 y = l.set 4 y
  exact List.set_set x

theorem getElem?_of_getG' (s : State W32 Int) (j : Nat) (hj : j < s.gpr.length) : s.gpr[j]? = some (s.getG j) := by
  rw [List.getElem?_eq_getElem hj]
  simp only [State.getG, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem pushRegs_ne4 (k : Nat) (hk : k < 9) : pushRegs.getD k 0 ≠ 4 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## The pushes -/

/-- The push cells after `k` pushes (newest first) over the tail. -/
def pushLog (st : State W32 Int) (a : Addr Int) : Nat → List (Addr Int × Cell W32 Int) → List (Addr Int × Cell W32 Int)
  | 0, tail => tail
  | k + 1, tail => storeCells (a.plusI (-(8 * (k + 1) : Int))) (st.getG (pushRegs.getD k 0)) ++ pushLog st a k tail

/-- The state after `k` pushes from a state with `rsp = a` at pc `p0`. -/
def pushSt (p0 : Nat) (st : State W32 Int) (a : Addr Int) (k : Nat) : State W32 Int :=
  { st with gpr := st.gpr.set 4 (.ptr (a.plusI (-(8 * k : Int)))), mem := pushLog st a k st.mem, pc := p0 + k }

theorem exec_pushSt (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (p0 : Nat) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (hlen : st.gpr.length = 16) (k : Nat) (hk : k < 9) :
    exec 4 mem0 orc (.push (pushRegs.getD k 0)) (pushSt p0 st a k) = pushSt p0 st a (k + 1) := by
  have h4 : (pushSt p0 st a k).getG rsp = .ptr (a.plusI (-(8 * k : Int))) := by
    simp only [pushSt]
    exact getG_setG_rsp st _ (by rw [hlen]; decide)
  have hh' : (pushSt p0 st a k).halted = false := by simp only [pushSt, hh]
  have hg : (pushSt p0 st a k).getG (pushRegs.getD k 0) = st.getG (pushRegs.getD k 0) := by
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
  first | rfl | (push_cast; rfl) | (congr 1; omega)

theorem run_pushes (prog : Array Instr) (p0 : Nat) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hpush : ∀ k, k < 9 → prog[p0 + k]? = some (.push (pushRegs.getD k 0)))
    (st : State W32 Int) (a : Addr Int) (hh : st.halted = false) (hlen : st.gpr.length = 16) :
    ∀ (m k : Nat), m + k ≤ 9 → run prog 4 mem0 orc k (pushSt p0 st a m) = pushSt p0 st a (m + k) := by
  intro m k
  induction k generalizing m with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hm : m < 9 := by omega
    rw [run_succ_step prog 4 mem0 orc k (pushSt p0 st a m) (.push (pushRegs.getD m 0)) (by simp only [pushSt, hh])
      (by simp only [pushSt]; exact hpush m hm)]
    rw [exec_pushSt mem0 orc p0 st a hh hlen m hm, ih (m + 1) (by omega)]
    rw [show (m + 1) + k = m + (k + 1) from by omega]

/-! ## The frame and the saves -/

/-- The save log of `m` slots at `[b+64+16j]` (newest first) over the tail. -/
def saveLog (st : State W32 Int) (b : Addr Int) : Nat → List (Addr Int × Cell W32 Int) → List (Addr Int × Cell W32 Int)
  | 0, tail => tail
  | k + 1, tail => laneLog (b.plusI ((64 + 16 * k : Nat) : Int)) ((st.getV (6 + k)).take 4) ++ saveLog st b k tail

/-- The state after the nine pushes, the `sub` and `m` saves. -/
def frontSt (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) : State W32 Int :=
  { gpr := st.gpr.set 4 (.ptr (a.plusI (-264))), vr := st.vr, flags := some (Addr.off (a.plusI (-72)), 192),
    mem := saveLog st (a.plusI (-264)) m (pushLog st a 9 st.mem), pc := p0 + 10 + m, halted := st.halted,
    tail := st.tail, err := st.err, assume := st.assume }

theorem exec_frontSt (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (p0 : Nat) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (hlen : st.gpr.length = 16) (m : Nat) :
    exec 4 mem0 orc (saveStep m) (frontSt p0 st a m) = frontSt p0 st a (m + 1) := by
  have h4 : (frontSt p0 st a m).getG rsp = .ptr (a.plusI (-264)) := by
    simp only [frontSt]
    exact getG_setG_rsp st _ (by rw [hlen]; decide)
  have hh' : (frontSt p0 st a m).halted = false := by simp only [frontSt, hh]
  rw [show saveStep m = .vstore 4 { base := some rsp, disp := ((64 + 16 * m : Nat) : Int) } (6 + m) from rfl]
  rw [exec_vstore_rsp 4 mem0 orc _ 4 (6 + m) ((64 + 16 * m : Nat) : Int) (a.plusI (-264)) hh' h4]
  simp only [frontSt, saveLog, State.getV]
  rw [show p0 + 10 + m + 1 = p0 + 10 + (m + 1) from by omega]

theorem run_saves (prog : Array Instr) (p0 : Nat) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hsave : ∀ m, m < 8 → prog[p0 + 10 + m]? = some (saveStep m))
    (st : State W32 Int) (a : Addr Int) (hh : st.halted = false) (hlen : st.gpr.length = 16) :
    ∀ (m k : Nat), m + k ≤ 8 → run prog 4 mem0 orc k (frontSt p0 st a m) = frontSt p0 st a (m + k) := by
  intro m k
  induction k generalizing m with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hm : m < 8 := by omega
    rw [run_succ_step prog 4 mem0 orc k (frontSt p0 st a m) (saveStep m) (by simp only [frontSt, hh])
      (by simp only [frontSt]; exact hsave m hm)]
    rw [exec_frontSt mem0 orc p0 st a hh hlen m, ih (m + 1) (by omega)]
    rw [show (m + 1) + k = m + (k + 1) from by omega]

theorem pushSt_zero (p0 : Nat) (st : State W32 Int) (a : Addr Int) (h4 : st.getG rsp = .ptr a) (hlen : st.gpr.length = 16) :
    pushSt p0 st a 0 = { st with pc := p0 } := by
  have e : a.plusI (-(8 * ((0 : Nat) : Int))) = a := by rw [plusI_int]; cases a; simp
  simp only [pushSt, pushLog, e, Nat.add_zero]
  have hs : st.gpr.set 4 (.ptr a) = st.gpr := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i = 4
    · subst hi
      rw [List.getElem?_set_self (by rw [hlen]; decide), getElem?_of_getG' st 4 (by rw [hlen]; decide)]
      exact congrArg some h4.symm
    · exact List.getElem?_set_ne (Ne.symm hi)
  rw [hs]

theorem exec_sub_front (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (p0 : Nat) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (hlen : st.gpr.length = 16) :
    exec 4 mem0 orc (.sub 64 4 (.imm 192)) (pushSt p0 st a 9) = frontSt p0 st a 0 := by
  have h4 : (pushSt p0 st a 9).getG rsp = .ptr (a.plusI (-72)) := by
    have e : a.plusI (-(8 * ((9 : Nat) : Int))) = a.plusI (-72) := by
      rw [plusI_int, plusI_int]
      show Addr.mk a.region (a.off + -(8 * ((9 : Nat) : Int))) = Addr.mk a.region (a.off + -72)
      congr 1
      try (push_cast; omega)
    show (st.gpr.set 4 (.ptr (a.plusI (-(8 * ((9 : Nat) : Int)))))).getD 4 (.num (Lane.const 0) (Lane.const 0)) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hlen]; decide), e]
    try rfl
  show exec 4 mem0 orc (.sub 64 rsp (.imm 192)) (pushSt p0 st a 9) = frontSt p0 st a 0
  rw [exec_sub_rsp 4 mem0 orc _ 192 (a.plusI (-72)) (by simp only [pushSt, hh]) h4]
  have ha : (a.plusI (-72)).plusI (-192) = a.plusI (-264) := by
    rw [plusI_int, plusI_int, plusI_int]
    show Addr.mk a.region (a.off + -72 + -192) = Addr.mk a.region (a.off + -264)
    congr 1; omega
  simp only [pushSt, frontSt, saveLog, set_set_rsp, ha]
  first | rfl | (congr 1; omega) | skip

/-- **The x1 prologue**: 18 steps from pc `p0`. -/
theorem run_front (prog : Array Instr) (p0 : Nat) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hpush : ∀ k, k < 9 → prog[p0 + k]? = some (.push (pushRegs.getD k 0)))
    (hsub : prog[p0 + 9]? = some (.sub 64 4 (.imm 192)))
    (hsave : ∀ m, m < 8 → prog[p0 + 10 + m]? = some (saveStep m))
    (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (h4 : st.getG rsp = .ptr a) (hlen : st.gpr.length = 16) :
    run prog 4 mem0 orc 18 { st with pc := p0 } = frontSt p0 st a 8 := by
  rw [← pushSt_zero p0 st a h4 hlen, show (18 : Nat) = 9 + (1 + 8) from rfl, run_add,
    run_pushes prog p0 mem0 orc hpush st a hh hlen 0 9 (by omega)]
  rw [run_add, run_succ_step prog 4 mem0 orc 0 (pushSt p0 st a 9) (.sub 64 4 (.imm 192)) (by simp only [pushSt, hh])
    (by simp only [pushSt]; exact hsub)]
  rw [exec_sub_front mem0 orc p0 st a hh hlen]
  show run prog 4 mem0 orc 8 (frontSt p0 st a 0) = frontSt p0 st a 8
  exact run_saves prog p0 mem0 orc hsave st a hh hlen 0 8 (by omega)

/-- `nop` (the `endbr64` of `avx_x1`) only advances the pc. -/
theorem exec_nop {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool} (s : State W32 Int)
    (hh : s.halted = false) : exec ro mem0 orc .nop s = s.next := by
  simp only [exec, hh, Bool.false_eq_true, ite_false]

/-- **The x1 prologue behind a leading `nop`**: 19 steps from pc `p0`. -/
theorem run_front_nop (prog : Array Instr) (p0 : Nat) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (hnop : prog[p0]? = some .nop)
    (hpush : ∀ k, k < 9 → prog[p0 + 1 + k]? = some (.push (pushRegs.getD k 0)))
    (hsub : prog[p0 + 1 + 9]? = some (.sub 64 4 (.imm 192)))
    (hsave : ∀ m, m < 8 → prog[p0 + 1 + 10 + m]? = some (saveStep m))
    (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (h4 : st.getG rsp = .ptr a) (hlen : st.gpr.length = 16) :
    run prog 4 mem0 orc 19 { st with pc := p0 } = frontSt (p0 + 1) st a 8 := by
  rw [show (19 : Nat) = 1 + 18 from rfl, run_add,
    run_succ_step prog 4 mem0 orc 0 { st with pc := p0 } .nop hh hnop, exec_nop { st with pc := p0 } hh]
  show run prog 4 mem0 orc 18 { st with pc := p0 + 1 } = _
  exact run_front prog (p0 + 1) mem0 orc hpush hsub hsave st a hh h4 hlen

/-! ## Projections of `frontSt` -/

theorem frontSt_halted (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) :
    (frontSt p0 st a m).halted = st.halted := rfl
theorem frontSt_pc (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) :
    (frontSt p0 st a m).pc = p0 + 10 + m := rfl
theorem frontSt_vr (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) :
    (frontSt p0 st a m).vr = st.vr := rfl
theorem frontSt_mem (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) :
    (frontSt p0 st a m).mem = saveLog st (a.plusI (-264)) m (pushLog st a 9 st.mem) := rfl
theorem frontSt_err (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) :
    (frontSt p0 st a m).err = st.err := rfl
theorem frontSt_tail (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) :
    (frontSt p0 st a m).tail = st.tail := rfl
theorem frontSt_gpr_len (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) :
    (frontSt p0 st a m).gpr.length = st.gpr.length := by
  show (st.gpr.set 4 _).length = _
  rw [List.length_set]

theorem frontSt_rsp (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) (hlen : st.gpr.length = 16) :
    (frontSt p0 st a m).getG rsp = .ptr (a.plusI (-264)) := by
  show (st.gpr.set 4 _).getD 4 _ = _
  rw [getD_set_self_r5 _ _ (by rw [hlen]; decide)]

theorem frontSt_getG_ne (p0 : Nat) (st : State W32 Int) (a : Addr Int) (m : Nat) (j : Nat) (hj : j ≠ 4) :
    (frontSt p0 st a m).getG j = st.getG j := by
  show (st.gpr.set 4 _).getD j _ = _
  rw [getD_set_ne_r5 _ _ _ (Ne.symm hj)]
  rfl

end Hashtree.Proofs.WinX1Front
