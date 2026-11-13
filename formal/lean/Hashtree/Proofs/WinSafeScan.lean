import Hashtree.Proofs.WinFrameStack

/-!
# R5: kernel-reducible Boolean mirror of the frame side condition

`Proofs.WinFrameStack.frameSafe` is a `Prop`; its `Decidable` instance (like every instance built
from tactics) is fine for elaboration, but the *kernel* does not reduce it: `decide (frameSafe i)`
gets stuck on the `mSafe` branch, so a `decide +kernel` scan over the streams cannot run through
it.  (The `okI` instance reduces: it is the same shape as the one the avx512 scan already uses.)

This module therefore gives a Boolean mirror of `frameSafe` (and of its operand predicates) built
only from `Bool` operations, proves that the mirror agrees with the `Prop` (`frameSafeB_iff`), and
combines it with a kernel-reducible `okI` decision into `safeB`.  All scans in the windows proofs
go through `safeB`; the bridge to the `Prop` is `safeB_ok` / `safeB_frame`.

The mirror duplicates the 39-branch type-level case analysis of `frameSafe` on purpose: the two
definitions must stay syntactically in step, and any change to `frameSafe` must be mirrored here.
-/

open Hashtree.Asm Hashtree.Asm.X86
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Asm.X86

/-! ## Decidable instances for `okI` (as in `Proofs.WinAvx512`) -/

instance instDecMemOkScan (m : MemRef) : Decidable (memOk m) := by unfold memOk; infer_instance
instance instDecGsrcScan (s : GSrc) : Decidable (gsrcOk s) := by
  cases s <;> dsimp only [gsrcOk] <;> infer_instance
instance instDecVsrcScan (s : VSrc) : Decidable (vsrcOk s) := by
  cases s <;> dsimp only [vsrcOk] <;> infer_instance
instance instDecOkIScan (i : Instr) : Decidable (okI i) := by
  cases i <;> dsimp only [okI] <;> infer_instance

/-! ## Boolean mirrors of the operand predicates -/

/-- Boolean form of `gsSafe`. -/
def gsSafeB : GSrc → Bool
  | .reg r => !(r == 4)
  | .imm _ => true
  | .mem m => mSafeB m

/-- Boolean form of `vsSafe`. -/
def vsSafeB : VSrc → Bool
  | .reg _ => true
  | .mem m => mSafeB m

/-- Boolean form of `frameSafe`: same 39 branches, each predicate in `Bool`. -/
def frameSafeB : Instr → Bool
  | .nop => true
  | .vop _ _ _ _ _ s2 => vsSafeB s2
  | .vshift _ _ _ _ _ _ => true
  | .vshiftq _ _ _ _ _ => true
  | .vror _ _ _ _ => true
  | .vtern _ _ _ _ _ => true
  | .vload _ _ _ src => vsSafeB src
  | .vstore _ m _ => mSafeB m
  | .pshufd _ _ _ _ => true
  | .pshufb _ _ _ _ _ => true
  | .palignr _ _ _ _ _ => true
  | .pblendw _ _ _ => true
  | .shufps _ _ _ _ _ => true
  | .perm2f128 _ _ _ _ => true
  | .inserti128 _ _ m _ => mSafeB m
  | .inserti64x4 _ _ m _ => mSafeB m
  | .permi2d _ _ _ => true
  | .permi2q _ _ _ => true
  | .sha256rnds2 _ _ => true
  | .sha256msg1 _ _ => true
  | .sha256msg2 _ _ => true
  | .mov _ dn src => !(dn == 4) && gsSafeB src
  | .movst _ m src => mSafeB m && !(src == 4)
  | .alu _ _ dn src => !(dn == 4) && gsSafeB src
  | .sub _ dn src => !(dn == 4) && gsSafeB src
  | .lea dn m => !(dn == 4) && mSafeB m
  | .ror _ dn _ => !(dn == 4)
  | .shld _ dn src _ => !(dn == 4) && !(src == 4)
  | .shl _ dn _ => !(dn == 4)
  | .bswap _ dn => !(dn == 4)
  | .push _ => false
  | .pop _ => false
  | .cmp _ a b => !(a == 4) && gsSafeB b
  | .test _ a b => !(a == 4) && !(b == 4)
  | .jcc _ _ => true
  | .jmp _ => true
  | .jccTail _ _ => false
  | .jmpTail _ => false
  | .ret => false

/-! ## Agreement of the mirrors with the `Prop` definitions -/

theorem gsSafeB_iff (s : GSrc) : (gsSafeB s = true) ↔ gsSafe s := by
  cases s with
  | reg r => simp [gsSafeB, gsSafe]
  | imm v => simp [gsSafeB, gsSafe]
  | mem m => exact mSafeB_iff m

theorem vsSafeB_iff (s : VSrc) : (vsSafeB s = true) ↔ vsSafe s := by
  cases s with
  | reg i => simp [vsSafeB, vsSafe]
  | mem m => exact mSafeB_iff m

theorem frameSafeB_iff (i : Instr) : (frameSafeB i = true) ↔ frameSafe i := by
  cases i <;>
    simp only [frameSafeB, frameSafe, Bool.and_eq_true, Bool.not_eq_true, beq_iff_eq,
      Bool.false_eq_true, beq_eq_false_iff_ne, gsSafeB_iff, vsSafeB_iff, mSafeB_iff]
  all_goals simp

/-! ## The combined per-instruction side condition -/

/-- `okI` and `frameSafe` of one instruction, as a Boolean.  `frameSafe` is decided through the
kernel-reducible mirror `frameSafeB`. -/
def safeB (i : Instr) : Bool := decide (okI i) && frameSafeB i

/-- `decide p = true` implies `p`, for any honest instance. -/
theorem of_decide_eq_true {p : Prop} (inst : Decidable p) (h : @decide p inst = true) : p := by
  cases inst with
  | isTrue hp => exact hp
  | isFalse hp =>
    have h' : @decide p (isFalse hp) = false := rfl
    rw [h'] at h
    exact Bool.noConfusion h

theorem safeB_ok {i : Instr} (h : safeB i = true) : okI i :=
  of_decide_eq_true _ (by
    have h' := h
    simp only [safeB, Bool.and_eq_true] at h'
    exact h'.1)

theorem safeB_frame {i : Instr} (h : safeB i = true) : frameSafe i :=
  (frameSafeB_iff i).1 (by
    have h' := h
    simp only [safeB, Bool.and_eq_true] at h'
    exact h'.2)

theorem safeB_and {i : Instr} (h : safeB i = true) : okI i ∧ frameSafe i :=
  ⟨safeB_ok h, safeB_frame h⟩

end Hashtree.Asm.X86
