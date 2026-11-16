import Hashtree.Proofs.Avx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Proofs.Avx2X8WShift
open Hashtree.Proofs.Avx2X8WStrip

/-!
# The vector-register shape of the avx2_x8 exit cuts

The hand-off to `avx_x4` rebuilds the x4 entry state's vector lanes from the x8 exit cut's
own vector registers (`Avx2X8X4WAgree.cutEnv8`), which needs the cut to carry 32 registers
of 16 lanes.  One kernel evaluation of each exit cut (`KTE r` after a single pass, `KTEs r`
after the loop) at each ABI residue.
-/

namespace Hashtree.Proofs.Avx2X8ExitShape

/-- 32 registers of 16 lanes. -/
def vrShape (K : State E Lin) : Bool :=
  (K.vr.length == 32) && K.vr.all (fun l => l.length == 16)

theorem KTE_shape_0 : vrShape (KTE 0) = true := by decide +kernel
theorem KTE_shape_16 : vrShape (KTE 16) = true := by decide +kernel
theorem KTEs_shape_0 : vrShape (KTEs 0) = true := by decide +kernel
theorem KTEs_shape_16 : vrShape (KTEs 16) = true := by decide +kernel

theorem vrShape_len {K : State E Lin} (h : vrShape K = true) : K.vr.length = 32 := by
  simp only [vrShape, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem vrShape_lanes {K : State E Lin} (h : vrShape K = true) :
    ∀ l ∈ K.vr, l.length = 16 := by
  simp only [vrShape, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.2

end Hashtree.Proofs.Avx2X8ExitShape
