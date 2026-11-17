import Hashtree.Proofs.WinAvxX4WOutCells1
import Hashtree.Proofs.WinAvxX4WStripDefs

/-! R2c windows x4 — the tail cuts' log shapes and output-cell tables, part 2 (generated; one `decide +kernel` per fact). -/

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

theorem w4shape_KTs : outShapeW4 KTs = true := by decide +kernel

theorem w4cells_KTs : w4tab.all (fun t => outCell KTs t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem w4cell_KTs (o id b : Nat) (h : (o, id, b) ∈ w4tab) : outCell KTs o id b = true :=
  List.all_eq_true.mp w4cells_KTs (o, id, b) h

theorem w4shape_KTEs : outShapeW4 KTEs = true := by decide +kernel

theorem w4cells_KTEs : w4tab.all (fun t => outCell KTEs t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem w4cell_KTEs (o id b : Nat) (h : (o, id, b) ∈ w4tab) : outCell KTEs o id b = true :=
  List.all_eq_true.mp w4cells_KTEs (o, id, b) h

end Hashtree.Proofs.WinAvxX4WOut
