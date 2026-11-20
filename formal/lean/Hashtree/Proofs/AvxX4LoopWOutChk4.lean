import Hashtree.Proofs.AvxX4LoopWOutLab
import Hashtree.Proofs.AvxX4LoopWEntry

/-! R2c x4 — W-mode slices re-checked with the pilot's trees, part 4/8 (generated). -/
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

theorem chkT_77 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K77W Hashtree.Proofs.AvxX4LoopW.K78W T77 = true := by
  decide +kernel

theorem chkT_78 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K78W Hashtree.Proofs.AvxX4LoopW.K79W T78 = true := by
  decide +kernel

theorem chkT_79 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K79W Hashtree.Proofs.AvxX4LoopW.K80W T79 = true := by
  decide +kernel

theorem chkT_80 : sliceCheck prog 4 m0W (fun _ => false) 27 Hashtree.Proofs.AvxX4LoopW.K80W Hashtree.Proofs.AvxX4LoopW.K81W T80 = true := by
  decide +kernel

theorem chkT_81 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K81W Hashtree.Proofs.AvxX4LoopW.K82W T81 = true := by
  decide +kernel

theorem chkT_82 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K82W Hashtree.Proofs.AvxX4LoopW.K83W T82 = true := by
  decide +kernel

theorem chkT_83 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K83W Hashtree.Proofs.AvxX4LoopW.K84W T83 = true := by
  decide +kernel

theorem chkT_84 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K84W Hashtree.Proofs.AvxX4LoopW.K85W T84 = true := by
  decide +kernel

theorem chkT_85 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K85W Hashtree.Proofs.AvxX4LoopW.K86W T85 = true := by
  decide +kernel

theorem chkT_86 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K86W Hashtree.Proofs.AvxX4LoopW.K87W T86 = true := by
  decide +kernel

theorem chkT_87 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K87W Hashtree.Proofs.AvxX4LoopW.K88W T87 = true := by
  decide +kernel

theorem chkT_88 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K88W Hashtree.Proofs.AvxX4LoopW.K89W T88 = true := by
  decide +kernel

theorem chkT_89 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K89W Hashtree.Proofs.AvxX4LoopW.K90W T89 = true := by
  decide +kernel

theorem chkT_90 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K90W Hashtree.Proofs.AvxX4LoopW.K91W T90 = true := by
  decide +kernel

theorem chkT_91 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K91W Hashtree.Proofs.AvxX4LoopW.K92W T91 = true := by
  decide +kernel

theorem chkT_92 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K92W Hashtree.Proofs.AvxX4LoopW.K93W T92 = true := by
  decide +kernel

theorem chkT_93 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K93W Hashtree.Proofs.AvxX4LoopW.K94W T93 = true := by
  decide +kernel

theorem chkT_94 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K94W Hashtree.Proofs.AvxX4LoopW.K95W T94 = true := by
  decide +kernel

theorem chkT_95 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K95W Hashtree.Proofs.AvxX4LoopW.K96W T95 = true := by
  decide +kernel

theorem chkT_96 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K96W Hashtree.Proofs.AvxX4LoopW.K97W T96 = true := by
  decide +kernel

theorem chkT_97 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K97W Hashtree.Proofs.AvxX4LoopW.K98W T97 = true := by
  decide +kernel

theorem chkT_98 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K98W Hashtree.Proofs.AvxX4LoopW.K99W T98 = true := by
  decide +kernel

theorem chkT_99 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K99W Hashtree.Proofs.AvxX4LoopW.K100W T99 = true := by
  decide +kernel

theorem chkT_100 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K100W Hashtree.Proofs.AvxX4LoopW.K101W T100 = true := by
  decide +kernel

theorem chkT_101 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K101W Hashtree.Proofs.AvxX4LoopW.K102W T101 = true := by
  decide +kernel

theorem chkT_102 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K102W Hashtree.Proofs.AvxX4LoopW.K103W T102 = true := by
  decide +kernel

end Hashtree.Proofs.AvxX4LoopWOut
