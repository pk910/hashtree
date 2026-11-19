import Hashtree.Asm.RunAgree
import Hashtree.Kernels.X86Win.AvxX1

/-!
# R5: the run-invariance certificate of the windows `AvxX1` program

The per-pc live register sets (`live`), their certificate (`certB`, `decide +kernel`), and the
entry live set, for `RunAgree.run_agree`.  The program pushes the Win64 callee-saved
registers (their entry values are in the set), so its bridge needs the frame-slot certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvxX1Live

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.RunAgree

abbrev prog : Array Instr := Hashtree.Kernels.X86Win.AvxX1.prog

/-- Per-pc live register sets (the fixpoint). -/
def liveT : List (List Nat) := live prog

/-- Per-pc flags live-in bits. -/
def liveFT : List Bool := liveF prog

theorem certB_ok : certB prog liveT liveFT [] = true := by decide +kernel

/-- The certificate `run_agree` consumes. -/
theorem cert : Cert prog (fun p => liveT.getD p []) (fun p => liveFT.getD p false) [] := Cert_of_certB certB_ok

/-- The flags are not live at entry. -/
theorem liveF_entry : liveFT.getD 0 false = false := by decide +kernel

theorem live_entry_eq : liveT.getD 0 [] = [4, 3, 8, 6, 7, 5, 12, 13, 14, 15, 1, 2] := by decide +kernel

/-- Closure: the entry live set is inside the read set `[4, 3, 8, 6, 7, 5, 12, 13, 14, 15, 1, 2]`. -/
theorem live_entry : ∀ r, r ∈ liveT.getD 0 [] → r ∈ [4, 3, 8, 6, 7, 5, 12, 13, 14, 15, 1, 2] := by
  rw [live_entry_eq]; exact fun _ h => h

end Hashtree.Proofs.WinAvxX1Live
