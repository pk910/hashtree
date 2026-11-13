import Hashtree.Asm.RunAgree
import Hashtree.Asm.RunExit
import Hashtree.Kernels.X86Win.Avx512X16

/-!
# R5: the run-invariance certificate of the windows `Avx512X16` program

The per-pc live register sets (`live`), their certificate (`certB`, `decide +kernel`), and the
entry live set, for `RunAgree.run_agree`.  The program has no `push`/`pop`, so register
agreement on the entry set plus full memory agreement is the relation its bridge uses.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvx512Live

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.RunAgree

abbrev prog : Array Instr := Hashtree.Kernels.X86Win.Avx512X16.prog

/-- The tail seed: the registers of the avx2_x8 entry set (`WinAvx2X8Live.live_entry_eq`,
`[8,4,5,6,12,13,14,15,2,1]`) that this program writes; the others (`[5,6,12,13,14,15]`) it never
writes (`unwritten`), so they reach the tail by preservation. -/
def T8 : List Nat := [8, 4, 2, 1]

/-- Per-pc live register sets (the fixpoint), seeded with `T8` at the tail. -/
def liveT : List (List Nat) := live prog T8

/-- Per-pc flags live-in bits. -/
def liveFT : List Bool := liveF prog

theorem certB_ok : certB prog liveT liveFT T8 = true := by decide +kernel

/-- The certificate `run_agree` consumes. -/
theorem cert : Cert prog (fun p => liveT.getD p []) (fun p => liveFT.getD p false) T8 := Cert_of_certB certB_ok

/-- The flags are not live at entry. -/
theorem liveF_entry : liveFT.getD 0 false = false := by decide +kernel

theorem live_entry_eq : liveT.getD 0 [] = [8, 4, 2, 1] := by decide +kernel

/-- Closure: the entry live set is inside the read set `[8, 4, 2, 1]`. -/
theorem live_entry : ∀ r, r ∈ liveT.getD 0 [] → r ∈ [8, 4, 2, 1] := by
  rw [live_entry_eq]; exact fun _ h => h

/-- The stream never writes the Win64 callee-saved general registers (nor `rsi`/`rdi`). -/
theorem unwritten : Hashtree.Asm.RunExit.unwrittenScan prog [3, 5, 6, 7, 12, 13, 14, 15] = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx512Live
