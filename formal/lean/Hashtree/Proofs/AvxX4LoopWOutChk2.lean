import Hashtree.Proofs.AvxX4LoopWOutLab
import Hashtree.Proofs.AvxX4LoopWEntry

/-! R2c x4 — W-mode slices re-checked with the pilot's trees, part 2/8 (generated). -/
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

theorem chkT_25 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K25W Hashtree.Proofs.AvxX4LoopW.K26W T25 = true := by
  decide +kernel

theorem chkT_26 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K26W Hashtree.Proofs.AvxX4LoopW.K27W T26 = true := by
  decide +kernel

theorem chkT_27 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K27W Hashtree.Proofs.AvxX4LoopW.K28W T27 = true := by
  decide +kernel

theorem chkT_28 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K28W Hashtree.Proofs.AvxX4LoopW.K29W T28 = true := by
  decide +kernel

theorem chkT_29 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K29W Hashtree.Proofs.AvxX4LoopW.K30W T29 = true := by
  decide +kernel

theorem chkT_30 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K30W Hashtree.Proofs.AvxX4LoopW.K31W T30 = true := by
  decide +kernel

theorem chkT_31 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K31W Hashtree.Proofs.AvxX4LoopW.K32W T31 = true := by
  decide +kernel

theorem chkT_32 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K32W Hashtree.Proofs.AvxX4LoopW.K33W T32 = true := by
  decide +kernel

theorem chkT_33 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K33W Hashtree.Proofs.AvxX4LoopW.K34W T33 = true := by
  decide +kernel

theorem chkT_34 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K34W Hashtree.Proofs.AvxX4LoopW.K35W T34 = true := by
  decide +kernel

theorem chkT_35 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K35W Hashtree.Proofs.AvxX4LoopW.K36W T35 = true := by
  decide +kernel

theorem chkT_36 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K36W Hashtree.Proofs.AvxX4LoopW.K37W T36 = true := by
  decide +kernel

theorem chkT_37 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K37W Hashtree.Proofs.AvxX4LoopW.K38W T37 = true := by
  decide +kernel

theorem chkT_38 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K38W Hashtree.Proofs.AvxX4LoopW.K39W T38 = true := by
  decide +kernel

theorem chkT_39 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K39W Hashtree.Proofs.AvxX4LoopW.K40W T39 = true := by
  decide +kernel

theorem chkT_40 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K40W Hashtree.Proofs.AvxX4LoopW.K41W T40 = true := by
  decide +kernel

theorem chkT_41 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K41W Hashtree.Proofs.AvxX4LoopW.K42W T41 = true := by
  decide +kernel

theorem chkT_42 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K42W Hashtree.Proofs.AvxX4LoopW.K43W T42 = true := by
  decide +kernel

theorem chkT_43 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K43W Hashtree.Proofs.AvxX4LoopW.K44W T43 = true := by
  decide +kernel

theorem chkT_44 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K44W Hashtree.Proofs.AvxX4LoopW.K45W T44 = true := by
  decide +kernel

theorem chkT_45 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K45W Hashtree.Proofs.AvxX4LoopW.K46W T45 = true := by
  decide +kernel

theorem chkT_46 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K46W Hashtree.Proofs.AvxX4LoopW.K47W T46 = true := by
  decide +kernel

theorem chkT_47 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K47W Hashtree.Proofs.AvxX4LoopW.K48W T47 = true := by
  decide +kernel

theorem chkT_48 : sliceCheck prog 4 m0W (fun _ => false) 27 Hashtree.Proofs.AvxX4LoopW.K48W Hashtree.Proofs.AvxX4LoopW.K49W T48 = true := by
  decide +kernel

theorem chkT_49 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K49W Hashtree.Proofs.AvxX4LoopW.K50W T49 = true := by
  decide +kernel

theorem chkT_50 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K50W Hashtree.Proofs.AvxX4LoopW.K51W T50 = true := by
  decide +kernel

end Hashtree.Proofs.AvxX4LoopWOut
