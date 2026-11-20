import Hashtree.Proofs.AvxX4LoopWOutLab
import Hashtree.Proofs.AvxX4LoopWEntry

/-! R2c x4 — W-mode slices re-checked with the pilot's trees, part 1/8 (generated). -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.AvxX4 Hashtree.Gen.AvxX4P
open Hashtree.Proofs.AvxX4W (entryWx shiftK)
open Hashtree.Proofs.AvxX4LoopW (m0W KHL2W KHpW)
open Hashtree.Proofs.AvxX4LoopWExit (orcW orcExitW K201W)

namespace Hashtree.Proofs.AvxX4LoopWOut

theorem chkT_entry : sliceCheck prog 4 m0W orcW 72 entryWx Hashtree.Proofs.AvxX4LoopW.K1W T0 = true := by
  decide +kernel

theorem chkT_head : sliceCheck prog 4 m0W (fun _ => false) 68 KHL2W Hashtree.Proofs.AvxX4LoopW.K1W T0 = true := by
  decide +kernel

theorem chkT_1 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K1W Hashtree.Proofs.AvxX4LoopW.K2W T1 = true := by
  decide +kernel

theorem chkT_2 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K2W Hashtree.Proofs.AvxX4LoopW.K3W T2 = true := by
  decide +kernel

theorem chkT_3 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K3W Hashtree.Proofs.AvxX4LoopW.K4W T3 = true := by
  decide +kernel

theorem chkT_4 : sliceCheck prog 4 m0W (fun _ => false) 55 Hashtree.Proofs.AvxX4LoopW.K4W Hashtree.Proofs.AvxX4LoopW.K5W T4 = true := by
  decide +kernel

theorem chkT_5 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K5W Hashtree.Proofs.AvxX4LoopW.K6W T5 = true := by
  decide +kernel

theorem chkT_6 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K6W Hashtree.Proofs.AvxX4LoopW.K7W T6 = true := by
  decide +kernel

theorem chkT_7 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K7W Hashtree.Proofs.AvxX4LoopW.K8W T7 = true := by
  decide +kernel

theorem chkT_8 : sliceCheck prog 4 m0W (fun _ => false) 55 Hashtree.Proofs.AvxX4LoopW.K8W Hashtree.Proofs.AvxX4LoopW.K9W T8 = true := by
  decide +kernel

theorem chkT_9 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K9W Hashtree.Proofs.AvxX4LoopW.K10W T9 = true := by
  decide +kernel

theorem chkT_10 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K10W Hashtree.Proofs.AvxX4LoopW.K11W T10 = true := by
  decide +kernel

theorem chkT_11 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K11W Hashtree.Proofs.AvxX4LoopW.K12W T11 = true := by
  decide +kernel

theorem chkT_12 : sliceCheck prog 4 m0W (fun _ => false) 55 Hashtree.Proofs.AvxX4LoopW.K12W Hashtree.Proofs.AvxX4LoopW.K13W T12 = true := by
  decide +kernel

theorem chkT_13 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K13W Hashtree.Proofs.AvxX4LoopW.K14W T13 = true := by
  decide +kernel

theorem chkT_14 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K14W Hashtree.Proofs.AvxX4LoopW.K15W T14 = true := by
  decide +kernel

theorem chkT_15 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K15W Hashtree.Proofs.AvxX4LoopW.K16W T15 = true := by
  decide +kernel

theorem chkT_16 : sliceCheck prog 4 m0W (fun _ => false) 26 Hashtree.Proofs.AvxX4LoopW.K16W Hashtree.Proofs.AvxX4LoopW.K17W T16 = true := by
  decide +kernel

theorem chkT_17 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K17W Hashtree.Proofs.AvxX4LoopW.K18W T17 = true := by
  decide +kernel

theorem chkT_18 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K18W Hashtree.Proofs.AvxX4LoopW.K19W T18 = true := by
  decide +kernel

theorem chkT_19 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K19W Hashtree.Proofs.AvxX4LoopW.K20W T19 = true := by
  decide +kernel

theorem chkT_20 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K20W Hashtree.Proofs.AvxX4LoopW.K21W T20 = true := by
  decide +kernel

theorem chkT_21 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K21W Hashtree.Proofs.AvxX4LoopW.K22W T21 = true := by
  decide +kernel

theorem chkT_22 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K22W Hashtree.Proofs.AvxX4LoopW.K23W T22 = true := by
  decide +kernel

theorem chkT_23 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K23W Hashtree.Proofs.AvxX4LoopW.K24W T23 = true := by
  decide +kernel

theorem chkT_24 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K24W Hashtree.Proofs.AvxX4LoopW.K25W T24 = true := by
  decide +kernel

end Hashtree.Proofs.AvxX4LoopWOut
