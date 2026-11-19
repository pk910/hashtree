import Hashtree.Proofs.WinAvx2X8WOutTab
import Hashtree.Proofs.WinAvx2X8WStripDefs

/-! R2c windows x8 — the cut `KTE 24`: its 256 output cells (generated; one `decide +kernel`). -/

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

theorem cellsX_24 : tab8w.all (fun t => outCell (KTE 24) t.1 t.2.1 t.2.2) = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8WOut
