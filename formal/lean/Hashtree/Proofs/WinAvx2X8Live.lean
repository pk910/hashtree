import Hashtree.Asm.RunAgree
import Hashtree.Kernels.X86Win.Avx2X8

/-!
# R5: the run-invariance certificate of the windows `Avx2X8` program

The per-pc live register sets (`live`), their certificate (`certB`, `decide +kernel`), and the
entry live set, for `RunAgree.run_agree`.  The program pushes the Win64 callee-saved registers
(their entry values are in the set), so its bridge needs the frame-slot certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvx2X8Live

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.RunAgree

abbrev prog : Array Instr := Hashtree.Kernels.X86Win.Avx2X8.prog

/-- Per-pc live register sets (the fixpoint). -/
def liveT : List (List Nat) := live prog

theorem certB_ok : certB prog liveT = true := by decide +kernel

/-- The certificate `run_agree` consumes. -/
theorem cert : Cert prog (fun p => liveT.getD p []) := Cert_of_certB certB_ok

theorem live_entry_eq : liveT.getD 0 [] = [8, 4, 5, 6, 12, 13, 14, 15, 2, 1] := by decide +kernel

/-- Closure: the entry live set is inside the read set `[8, 4, 5, 6, 12, 13, 14, 15, 2, 1]`. -/
theorem live_entry : ∀ r, r ∈ liveT.getD 0 [] → r ∈ [8, 4, 5, 6, 12, 13, 14, 15, 2, 1] := by
  rw [live_entry_eq]; exact fun _ h => h

end Hashtree.Proofs.WinAvx2X8Live
