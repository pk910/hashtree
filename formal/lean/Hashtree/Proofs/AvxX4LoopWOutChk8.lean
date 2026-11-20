import Hashtree.Proofs.AvxX4LoopWOutLab
import Hashtree.Proofs.AvxX4LoopWEntry

/-! R2c x4 — W-mode slices re-checked with the pilot's trees, part 8/8 (generated). -/
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

theorem chkT_181 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K181W Hashtree.Proofs.AvxX4LoopW.K182W T181 = true := by
  decide +kernel

theorem chkT_182 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K182W Hashtree.Proofs.AvxX4LoopW.K183W T182 = true := by
  decide +kernel

theorem chkT_183 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K183W Hashtree.Proofs.AvxX4LoopW.K184W T183 = true := by
  decide +kernel

theorem chkT_184 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K184W Hashtree.Proofs.AvxX4LoopW.K185W T184 = true := by
  decide +kernel

theorem chkT_185 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K185W Hashtree.Proofs.AvxX4LoopW.K186W T185 = true := by
  decide +kernel

theorem chkT_186 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K186W Hashtree.Proofs.AvxX4LoopW.K187W T186 = true := by
  decide +kernel

theorem chkT_187 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K187W Hashtree.Proofs.AvxX4LoopW.K188W T187 = true := by
  decide +kernel

theorem chkT_188 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K188W Hashtree.Proofs.AvxX4LoopW.K189W T188 = true := by
  decide +kernel

theorem chkT_189 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K189W Hashtree.Proofs.AvxX4LoopW.K190W T189 = true := by
  decide +kernel

theorem chkT_190 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K190W Hashtree.Proofs.AvxX4LoopW.K191W T190 = true := by
  decide +kernel

theorem chkT_191 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K191W Hashtree.Proofs.AvxX4LoopW.K192W T191 = true := by
  decide +kernel

theorem chkT_192 : sliceCheck prog 4 m0W (fun _ => false) 2 Hashtree.Proofs.AvxX4LoopW.K192W Hashtree.Proofs.AvxX4LoopW.K193W T192 = true := by
  decide +kernel

theorem chkT_193 : sliceCheck prog 4 m0W (fun _ => false) 2 Hashtree.Proofs.AvxX4LoopW.K193W Hashtree.Proofs.AvxX4LoopW.K194W T193 = true := by
  decide +kernel

theorem chkT_194 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K194W Hashtree.Proofs.AvxX4LoopW.K195W T194 = true := by
  decide +kernel

theorem chkT_195 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K195W Hashtree.Proofs.AvxX4LoopW.K196W T195 = true := by
  decide +kernel

theorem chkT_196 : sliceCheck prog 4 m0W (fun _ => false) 4 Hashtree.Proofs.AvxX4LoopW.K196W Hashtree.Proofs.AvxX4LoopW.K197W T196 = true := by
  decide +kernel

theorem chkT_197 : sliceCheck prog 4 m0W (fun _ => false) 2 Hashtree.Proofs.AvxX4LoopW.K197W Hashtree.Proofs.AvxX4LoopW.K198W T197 = true := by
  decide +kernel

theorem chkT_198 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K198W Hashtree.Proofs.AvxX4LoopW.K199W T198 = true := by
  decide +kernel

theorem chkT_199 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K199W Hashtree.Proofs.AvxX4LoopW.K200W T199 = true := by
  decide +kernel

theorem chkT_turn : sliceCheck prog 4 m0W (fun _ => false) 23 Hashtree.Proofs.AvxX4LoopW.K200W KHpW T200 = true := by
  decide +kernel

theorem chkT_exit : sliceCheck prog 4 m0W orcExitW 27 Hashtree.Proofs.AvxX4LoopW.K200W K201W T200 = true := by
  decide +kernel

end Hashtree.Proofs.AvxX4LoopWOut
