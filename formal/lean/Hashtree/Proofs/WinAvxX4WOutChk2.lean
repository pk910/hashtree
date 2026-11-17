import Hashtree.Proofs.WinAvxX4WStripDefs
import Hashtree.Gen.WinAvxX4P.D203

/-! R2c windows x4 — the loop tails re-checked with the pilot's trees `T203`, part 2 (generated). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.AvxX4 Hashtree.Gen.WinAvxX4P
open Hashtree.Proofs.WinAvxX4W (m0W shiftKW orcB orcEx KT KTE)
open Hashtree.Proofs.WinAvxX4WStrip (m0WP stripKW KHs KH3s KTs KTEs)

namespace Hashtree.Proofs.WinAvxX4WOut

theorem w4chkT_turnS : sliceCheck prog 4 m0WP orcB 25 (stripKW K203) KTs T203 = true := by
  decide +kernel

theorem w4chkT_exitS : sliceCheck prog 4 m0WP orcEx 37 (stripKW K203) KTEs T203 = true := by
  decide +kernel

end Hashtree.Proofs.WinAvxX4WOut
