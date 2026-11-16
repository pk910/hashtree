import Hashtree.Proofs.AvxX4LoopWOutLab
import Hashtree.Proofs.AvxX4LoopWEntry

/-! R2c x4 — W-mode slices re-checked with the pilot's trees, part 3/8 (generated). -/
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

theorem chkT_51 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K51W Hashtree.Proofs.AvxX4LoopW.K52W T51 = true := by
  decide +kernel

theorem chkT_52 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K52W Hashtree.Proofs.AvxX4LoopW.K53W T52 = true := by
  decide +kernel

theorem chkT_53 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K53W Hashtree.Proofs.AvxX4LoopW.K54W T53 = true := by
  decide +kernel

theorem chkT_54 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K54W Hashtree.Proofs.AvxX4LoopW.K55W T54 = true := by
  decide +kernel

theorem chkT_55 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K55W Hashtree.Proofs.AvxX4LoopW.K56W T55 = true := by
  decide +kernel

theorem chkT_56 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K56W Hashtree.Proofs.AvxX4LoopW.K57W T56 = true := by
  decide +kernel

theorem chkT_57 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K57W Hashtree.Proofs.AvxX4LoopW.K58W T57 = true := by
  decide +kernel

theorem chkT_58 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K58W Hashtree.Proofs.AvxX4LoopW.K59W T58 = true := by
  decide +kernel

theorem chkT_59 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K59W Hashtree.Proofs.AvxX4LoopW.K60W T59 = true := by
  decide +kernel

theorem chkT_60 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K60W Hashtree.Proofs.AvxX4LoopW.K61W T60 = true := by
  decide +kernel

theorem chkT_61 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K61W Hashtree.Proofs.AvxX4LoopW.K62W T61 = true := by
  decide +kernel

theorem chkT_62 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K62W Hashtree.Proofs.AvxX4LoopW.K63W T62 = true := by
  decide +kernel

theorem chkT_63 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K63W Hashtree.Proofs.AvxX4LoopW.K64W T63 = true := by
  decide +kernel

theorem chkT_64 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K64W Hashtree.Proofs.AvxX4LoopW.K65W T64 = true := by
  decide +kernel

theorem chkT_65 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K65W Hashtree.Proofs.AvxX4LoopW.K66W T65 = true := by
  decide +kernel

theorem chkT_66 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K66W Hashtree.Proofs.AvxX4LoopW.K67W T66 = true := by
  decide +kernel

theorem chkT_67 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K67W Hashtree.Proofs.AvxX4LoopW.K68W T67 = true := by
  decide +kernel

theorem chkT_68 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K68W Hashtree.Proofs.AvxX4LoopW.K69W T68 = true := by
  decide +kernel

theorem chkT_69 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K69W Hashtree.Proofs.AvxX4LoopW.K70W T69 = true := by
  decide +kernel

theorem chkT_70 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K70W Hashtree.Proofs.AvxX4LoopW.K71W T70 = true := by
  decide +kernel

theorem chkT_71 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K71W Hashtree.Proofs.AvxX4LoopW.K72W T71 = true := by
  decide +kernel

theorem chkT_72 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K72W Hashtree.Proofs.AvxX4LoopW.K73W T72 = true := by
  decide +kernel

theorem chkT_73 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K73W Hashtree.Proofs.AvxX4LoopW.K74W T73 = true := by
  decide +kernel

theorem chkT_74 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K74W Hashtree.Proofs.AvxX4LoopW.K75W T74 = true := by
  decide +kernel

theorem chkT_75 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K75W Hashtree.Proofs.AvxX4LoopW.K76W T75 = true := by
  decide +kernel

theorem chkT_76 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K76W Hashtree.Proofs.AvxX4LoopW.K77W T76 = true := by
  decide +kernel

end Hashtree.Proofs.AvxX4LoopWOut
