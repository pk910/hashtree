import Hashtree.Proofs.WinAvx2X8WOutTab
import Hashtree.Proofs.WinAvx2X8WStripDefs

/-! R2c windows x8 — the cut `KTs 8`: its tail slice re-checked with the pilot's trees `T211` (generated; one `decide +kernel`). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip

namespace Hashtree.Proofs.WinAvx2X8WOut

theorem chkTS_8 : sliceCheck prog 4 (m8P 8) orcB 24 (stripK8 8 K211) (KTs 8) T211 = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8WOut
