import Hashtree.Proofs.WinShani
import Hashtree.Proofs.WinFrameStack

/-!
# R5: `shani_x2` prologue steps

The first steps of the windows `shani_x2` prologue, proved from the machine semantics:

```
pc 0     : sub rsp, 248                     -- exec_sub_rsp
pc 1..10 : vstore 4 [rsp + 16k] (xmm{6+k})  -- exec_vstore_rsp
```

`laneLog` is the write log of a `storeLanes` (four byte cells per lane, newest first), so
`mem_storeLanes` reads the prologue's memory effect, which is the prefix `saveLog` of the
composition in `formal/notes/R5.md` section 6.
-/

open Hashtree.Asm Hashtree.Asm.X86
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Hashtree.Proofs.WinShaniFront

/-! ## `Except` reductions (copies of the one-liners in `Proofs.Win64`) -/

theorem gCtl_reg_ptr (s : State W32 Int) (d : Nat) (a : Addr Int) (h : s.getG d = .ptr a) :
    gCtl s (.reg d) = .ok a := by
  simp only [gCtl, h]
  rfl

theorem gCtl_imm (s : State W32 Int) (v : Int) :
    gCtl s (.imm v) = .ok (⟨rNum, v⟩ : Addr Int) := by
  simp only [gCtl]
  rfl

theorem bind_ok_eq {β δ : Type} (b : β) (k : β → Except String δ) :
    ((Except.ok b : Except String β) >>= k) = k b := rfl

theorem okOr_pure (s t : State W32 Int) : okOr s (pure t) = t := rfl

/-! ## The write log of `storeLanes` -/

/-- The cells written by `storeLanes s a xs` (newest first), as a function of `a` and `xs`. -/
def laneLog (a : Addr Int) : List W32 → List (Addr Int × Cell W32 Int)
  | [] => []
  | x :: xs => laneLog (a.plusI 4) xs ++ [(a.plusI 3, .dat x 3), (a.plusI 2, .dat x 2), (a.plusI 1, .dat x 1), (a, .dat x 0)]

/-- `storeLanes` changes only `mem`. -/
theorem storeLanes_rec (s : State W32 Int) (a : Addr Int) (xs : List W32) :
    storeLanes s a xs = { s with mem := laneLog a xs ++ s.mem } := by
  induction xs generalizing a s with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [laneLog, storeLanes]
    rw [ih]
    simp only [storeLane, List.append_assoc, List.cons_append, List.nil_append]

theorem mem_storeLanes (s : State W32 Int) (a : Addr Int) (xs : List W32) :
    (storeLanes s a xs).mem = laneLog a xs ++ s.mem := by
  rw [storeLanes_rec]

/-! ## The `sub rsp, imm` prologue instruction -/

/-- `sub 64 rsp (imm v)` on a state whose `rsp` holds the pointer `a`: `rsp` becomes `a - v`,
the flags record the subtraction, and the pc advances. -/
theorem exec_sub_rsp (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int) (v : Int) (a : Addr Int) (hh : s.halted = false) (h4 : s.getG rsp = .ptr a) :
    exec ro mem0 orc (.sub 64 rsp (.imm v)) s = { s with gpr := s.gpr.set rsp (.ptr (a.plusI (-v))), flags := some (a.off, v), pc := s.pc + 1 } := by
  have hg : gCtl s (.reg rsp) = .ok a := gCtl_reg_ptr s rsp a h4
  have hi : gCtl s (.imm v) = .ok (⟨rNum, (v : Int)⟩ : Addr Int) := gCtl_imm s v
  have hr : (a.plus (Ctl.smul (-1) v) : Addr Int) = a.plusI (-v) := by
    simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.smul, Ctl.ofInt, id_eq]
    rw [show (-1 : Int) * v = -v from by omega]
  simp only [exec, hh, Bool.false_eq_true, ite_false]
  rw [ite_eq_left trivial]
  rw [hg, bind_ok_eq, hi, bind_ok_eq]
  rw [ite_eq_left rfl]
  rw [okOr_pure, hr]
  simp only [State.next, State.setG, setFlags, hh]

/-! ## The `vstore 4 [rsp + d] src` prologue instruction -/

/-- `vstore w [rsp + d] src` on a state whose `rsp` holds the pointer `a`: the `w` lanes of `src`
are stored at `a + d` (four byte cells each), `mem` grows by `laneLog`, and the pc advances. -/
theorem exec_vstore_rsp (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int) (w src : Nat) (d : Int) (a : Addr Int) (hh : s.halted = false) (h4 : s.getG rsp = .ptr a) :
    exec ro mem0 orc (.vstore w { base := some rsp, disp := d } src) s = { s with mem := laneLog (a.plusI d) ((s.getV src).take w) ++ s.mem, pc := s.pc + 1 } := by
  have he : effAddr ro s ({ base := some rsp, disp := d } : MemRef) = .ok (a.plusI d) := by
    simp only [effAddr, baseAddr, regPtr, h4]
  simp only [exec, hh, Bool.false_eq_true, ite_false]
  rw [he, bind_ok_eq, okOr_pure, storeLanes_rec]
  simp only [State.next, hh]

end Hashtree.Proofs.WinShaniFront
