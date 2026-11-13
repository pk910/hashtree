import Hashtree.Asm.ArmShift
import Hashtree.Asm.ArmSym
import Hashtree.Asm.ArmCall
import Hashtree.Asm.ArmRet

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# Stack shift at the entry and exit cuts

`ArmShift` commutes a concrete run with the stack shift, leaving the entry and exit states to
this module: the symbolic entry `entryS` at `SP = sp0` is the shift of the one at `SP = 0`,
`retOff` commutes with the shift (its `x30` region is not the stack), and `ShaX1Exit` is
transported along `Rel`.
-/

namespace Hashtree.Asm.ArmShift
open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun Hashtree.Asm.ArmRename
  Hashtree.Asm.ArmRet Hashtree.Asm.ArmSym

/-! ### The shift of the entry and exit states -/

theorem entryS_map_sh (env0 : Key → W32) (σ : Nat → Int) (k : Int) :
    mapState env0 σ (Hashtree.Asm.ArmSym.entryS k) =
      sh k (mapState env0 σ (Hashtree.Asm.ArmSym.entryS 0)) := by
  simp only [mapState, Hashtree.Asm.ArmSym.entryS, sh, shLog, List.map_map,
    State.mk.injEq]
  refine ⟨?_, by trivial, by trivial, by trivial, by trivial, by trivial, by trivial, by trivial, by trivial⟩
  apply List.map_congr_left
  intro i hi
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
    by_cases h30 : i = 30 <;> by_cases h31 : i = 31 <;>
    simp [h0, h1, h2, h30, h31, mapVal, shVal, mapAddr, Hashtree.Asm.mapAddr,
      Lin.ofInt, Lin.eval, dotC, rNum, rIn, rOut, rRet, rStack] <;>
    first | rfl | omega

theorem retOff_sh (k kk : Int) (s : CS) :
    retOff kk (sh k s) = sh k (retOff kk s) := by
  unfold retOff
  exact setG_ptr_symbolic_sh k s 30 rRet kk (by decide : ¬ (rRet : Region) = rStack)

theorem ShaX1Exit_shift {k : Int} {s1 s2 : CS} (h : Rel k s1 s2)
    (hx : Hashtree.Asm.ArmCall.ShaX1Exit 0 s2) :
    Hashtree.Asm.ArmCall.ShaX1Exit k s1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h.err]; exact hx.err
  · rw [h.halted]; exact hx.halted
  · rw [h.tail]; exact hx.tail
  · have hg30 : s1.getG 30 = (sh k s2).getG 30 := by simp only [State.getG, h.gpr]
    rw [hg30, getG_sh, hx.ret]
    simp [shVal, mapAddr, rRet, rStack]
  · have hg31 : s1.getG 31 = (sh k s2).getG 31 := by simp only [State.getG, h.gpr]
    rw [hg31, getG_sh, hx.sp]
    simp [shVal, mapAddr, rStack]

end Hashtree.Asm.ArmShift
