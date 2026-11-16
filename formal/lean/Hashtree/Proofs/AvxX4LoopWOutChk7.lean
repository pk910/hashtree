import Hashtree.Proofs.AvxX4LoopWOutLab
import Hashtree.Proofs.AvxX4LoopWEntry

/-! R2c x4 — W-mode slices re-checked with the pilot's trees, part 7/8 (generated). -/
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

theorem chkT_155 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K155W Hashtree.Proofs.AvxX4LoopW.K156W T155 = true := by
  decide +kernel

theorem chkT_156 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K156W Hashtree.Proofs.AvxX4LoopW.K157W T156 = true := by
  decide +kernel

theorem chkT_157 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K157W Hashtree.Proofs.AvxX4LoopW.K158W T157 = true := by
  decide +kernel

theorem chkT_158 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K158W Hashtree.Proofs.AvxX4LoopW.K159W T158 = true := by
  decide +kernel

theorem chkT_159 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K159W Hashtree.Proofs.AvxX4LoopW.K160W T159 = true := by
  decide +kernel

theorem chkT_160 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K160W Hashtree.Proofs.AvxX4LoopW.K161W T160 = true := by
  decide +kernel

theorem chkT_161 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K161W Hashtree.Proofs.AvxX4LoopW.K162W T161 = true := by
  decide +kernel

theorem chkT_162 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K162W Hashtree.Proofs.AvxX4LoopW.K163W T162 = true := by
  decide +kernel

theorem chkT_163 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K163W Hashtree.Proofs.AvxX4LoopW.K164W T163 = true := by
  decide +kernel

theorem chkT_164 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K164W Hashtree.Proofs.AvxX4LoopW.K165W T164 = true := by
  decide +kernel

theorem chkT_165 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K165W Hashtree.Proofs.AvxX4LoopW.K166W T165 = true := by
  decide +kernel

theorem chkT_166 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K166W Hashtree.Proofs.AvxX4LoopW.K167W T166 = true := by
  decide +kernel

theorem chkT_167 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K167W Hashtree.Proofs.AvxX4LoopW.K168W T167 = true := by
  decide +kernel

theorem chkT_168 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K168W Hashtree.Proofs.AvxX4LoopW.K169W T168 = true := by
  decide +kernel

theorem chkT_169 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K169W Hashtree.Proofs.AvxX4LoopW.K170W T169 = true := by
  decide +kernel

theorem chkT_170 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K170W Hashtree.Proofs.AvxX4LoopW.K171W T170 = true := by
  decide +kernel

theorem chkT_171 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K171W Hashtree.Proofs.AvxX4LoopW.K172W T171 = true := by
  decide +kernel

theorem chkT_172 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K172W Hashtree.Proofs.AvxX4LoopW.K173W T172 = true := by
  decide +kernel

theorem chkT_173 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K173W Hashtree.Proofs.AvxX4LoopW.K174W T173 = true := by
  decide +kernel

theorem chkT_174 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K174W Hashtree.Proofs.AvxX4LoopW.K175W T174 = true := by
  decide +kernel

theorem chkT_175 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K175W Hashtree.Proofs.AvxX4LoopW.K176W T175 = true := by
  decide +kernel

theorem chkT_176 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K176W Hashtree.Proofs.AvxX4LoopW.K177W T176 = true := by
  decide +kernel

theorem chkT_177 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K177W Hashtree.Proofs.AvxX4LoopW.K178W T177 = true := by
  decide +kernel

theorem chkT_178 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K178W Hashtree.Proofs.AvxX4LoopW.K179W T178 = true := by
  decide +kernel

theorem chkT_179 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K179W Hashtree.Proofs.AvxX4LoopW.K180W T179 = true := by
  decide +kernel

theorem chkT_180 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K180W Hashtree.Proofs.AvxX4LoopW.K181W T180 = true := by
  decide +kernel

end Hashtree.Proofs.AvxX4LoopWOut
