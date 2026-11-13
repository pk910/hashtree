import Hashtree.Proofs.WinFrameStack

/-!
# R5: the stack-memory shift of the `sse_x1`/`avx_x1` frame transfer

`sse_x1`/`avx_x1` keep the linux `rsp`-relative displacements but their body-entry `rsp` is 128
lower (`entry_rsp-264` against `entry_rsp-136`), so the windows body touches cells 128 below the
linux ones.  The shani frame transfer (`WinFrameStack.exec_frame`) cannot apply: it needs
`δ + d = 0`, i.e. both runs touching the same absolute cells.

This module starts the relation the transfer needs (R5.md section 12): a shift of the `rStack`
part of the address space and of the memory log, lifting to a state `shSt μ`.  `shCell` shifts
the *payload* of pointer cells as well, because a saved stack pointer is itself shifted in the
windows run.

Proved here: the address algebra (`shAddr` commutes with `plusI`, preserves regions and the
address comparison `AddrEq.same`).  The `lookup`/`readCell`/store/load commutation and the
39-case `exec_sh` dispatch are the next step; see R5.md section 12.
-/

open Hashtree.Asm
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.deprecated false

namespace Hashtree.Asm.X86

/-- Shift an address into the stack region by `μ`: `⟨rStack, o⟩ ↦ ⟨rStack, o + μ⟩`; every other
address is unchanged. -/
def shAddr (μ : Int) (a : Addr Int) : Addr Int :=
  if a.region = rStack then a.plusI μ else a

/-- Shift the payload of a pointer cell: a `pb` cell of a stack pointer is itself shifted. -/
def shCell (μ : Int) : Cell W32 Int → Cell W32 Int
  | .dat x k => .dat x k
  | .pb a k => .pb (shAddr μ a) k

/-- Shift every address and every pointer payload of a memory log. -/
def shLog (μ : Int) (l : List (Addr Int × Cell W32 Int)) : List (Addr Int × Cell W32 Int) :=
  l.map (fun p => (shAddr μ p.1, shCell μ p.2))

/-- Shift a register value: a stack pointer is shifted, a number or any other pointer is not. -/
def shVal (μ : Int) : Val W32 Int → Val W32 Int
  | .ptr a => .ptr (shAddr μ a)
  | .num l h => .num l h

/-- The shifted state: every register value and every memory cell is shifted by `μ`. -/
def shSt (μ : Int) (s : State W32 Int) : State W32 Int :=
  { s with gpr := s.gpr.map (shVal μ), mem := shLog μ s.mem }

@[simp] theorem shSt_gpr (μ : Int) (s : State W32 Int) :
    (shSt μ s).gpr = s.gpr.map (shVal μ) := rfl

@[simp] theorem shSt_mem (μ : Int) (s : State W32 Int) :
    (shSt μ s).mem = shLog μ s.mem := rfl

@[simp] theorem shSt_vr (μ : Int) (s : State W32 Int) : (shSt μ s).vr = s.vr := rfl
@[simp] theorem shSt_flags (μ : Int) (s : State W32 Int) : (shSt μ s).flags = s.flags := rfl
@[simp] theorem shSt_pc (μ : Int) (s : State W32 Int) : (shSt μ s).pc = s.pc := rfl
@[simp] theorem shSt_halted (μ : Int) (s : State W32 Int) : (shSt μ s).halted = s.halted := rfl
@[simp] theorem shSt_tail (μ : Int) (s : State W32 Int) : (shSt μ s).tail = s.tail := rfl
@[simp] theorem shSt_err (μ : Int) (s : State W32 Int) : (shSt μ s).err = s.err := rfl
@[simp] theorem shSt_assume (μ : Int) (s : State W32 Int) : (shSt μ s).assume = s.assume := rfl

@[simp] theorem shCell_dat (μ : Int) (x : W32) (k : Nat) :
    shCell μ (.dat x k) = .dat x k := rfl

@[simp] theorem shCell_pb (μ : Int) (a : Addr Int) (k : Nat) :
    shCell μ (.pb a k) = .pb (shAddr μ a) k := rfl

@[simp] theorem shLog_nil (μ : Int) : shLog μ [] = [] := rfl

@[simp] theorem shLog_cons (μ : Int) (a : Addr Int) (c : Cell W32 Int)
    (l : List (Addr Int × Cell W32 Int)) :
    shLog μ ((a, c) :: l) = (shAddr μ a, shCell μ c) :: shLog μ l := rfl

@[simp] theorem shVal_ptr (μ : Int) (a : Addr Int) : shVal μ (.ptr a) = .ptr (shAddr μ a) := rfl
@[simp] theorem shVal_num (μ : Int) (l h : W32) : shVal μ (.num l h) = .num l h := rfl

/-- The shift of a stack address is the lowered address. -/
theorem shAddr_of_eq (μ : Int) (a : Addr Int) (h : a.region = rStack) :
    shAddr μ a = a.plusI μ := by
  rw [shAddr, ite_eq_left h]

/-- The shift fixes every address outside the stack region. -/
theorem shAddr_of_ne (μ : Int) (a : Addr Int) (h : a.region ≠ rStack) :
    shAddr μ a = a := by
  rw [shAddr, ite_eq_right h]

theorem shAddr_region (μ : Int) (a : Addr Int) : (shAddr μ a).region = a.region := by
  by_cases h : a.region = rStack
  · rw [shAddr_of_eq μ a h]
    obtain ⟨r, o⟩ := a
    rfl
  · rw [shAddr_of_ne μ a h]

/-- The shift commutes with adding a byte offset, so `lane`-sized walks of the log stay shifted
walks. -/
theorem shAddr_plusI (μ : Int) (a : Addr Int) (k : Int) :
    shAddr μ (a.plusI k) = (shAddr μ a).plusI k := by
  by_cases h : a.region = rStack
  · have h' : (a.plusI k).region = rStack := by
      obtain ⟨r, o⟩ := a
      exact h
    rw [shAddr_of_eq μ _ h', shAddr_of_eq μ a h]
    obtain ⟨r, o⟩ := a
    simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq]
    congr 1
    omega
  · have h' : (a.plusI k).region ≠ rStack := by
      obtain ⟨r, o⟩ := a
      exact h
    rw [shAddr_of_ne μ _ h', shAddr_of_ne μ a h]

end Hashtree.Asm.X86
