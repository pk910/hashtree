import Hashtree.Proofs.Avx2X8WOutTab
import Hashtree.Proofs.Avx2X8WStripDefs

/-! R2c x8 — the cut `KTs 16`: its tail slice re-checked with the pilot's trees `T210`,
its output cells and the shape of its log (generated). -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.Avx2X8 Hashtree.Gen.Avx2X8P
open Hashtree.Proofs.Avx2X8Align
open Hashtree.Proofs.Avx2X8WShift
open Hashtree.Proofs.Avx2X8WStrip

namespace Hashtree.Proofs.Avx2X8WOut

theorem chkTS_16 : sliceCheck prog 4 (m8P 16) orcB 27 (stripK8 16 K210) (KTs 16) T210t = true := by
  decide +kernel

theorem cellsTS_16 : tab8.all (fun t => outCell (KTs 16) t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem shapeTS_16 : outShape8 (KTs 16) = true := by
  decide +kernel

end Hashtree.Proofs.Avx2X8WOut
