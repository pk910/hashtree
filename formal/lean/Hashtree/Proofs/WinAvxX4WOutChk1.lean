import Hashtree.Proofs.WinAvxX4WShift
import Hashtree.Gen.WinAvxX4P.D203

/-! R2c windows x4 — the loop tails re-checked with the pilot's trees `T203`, part 1 (generated). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.AvxX4 Hashtree.Gen.WinAvxX4P
open Hashtree.Proofs.WinAvxX4W (m0W shiftKW orcB orcEx KT KTE)

namespace Hashtree.Proofs.WinAvxX4WOut

theorem w4chkT_turn : sliceCheck prog 4 m0W orcB 25 (shiftKW K203) KT T203 = true := by
  decide +kernel

theorem w4chkT_exit : sliceCheck prog 4 m0W orcEx 37 (shiftKW K203) KTE T203 = true := by
  decide +kernel

end Hashtree.Proofs.WinAvxX4WOut
