import Hashtree.Proofs.AvxX4LoopWOutLab
import Hashtree.Proofs.AvxX4LoopWEntry

/-! R2c x4 — W-mode slices re-checked with the pilot's trees, part 6/8 (generated). -/
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

theorem chkT_129 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K129W Hashtree.Proofs.AvxX4LoopW.K130W T129 = true := by
  decide +kernel

theorem chkT_130 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K130W Hashtree.Proofs.AvxX4LoopW.K131W T130 = true := by
  decide +kernel

theorem chkT_131 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K131W Hashtree.Proofs.AvxX4LoopW.K132W T131 = true := by
  decide +kernel

theorem chkT_132 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K132W Hashtree.Proofs.AvxX4LoopW.K133W T132 = true := by
  decide +kernel

theorem chkT_133 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K133W Hashtree.Proofs.AvxX4LoopW.K134W T133 = true := by
  decide +kernel

theorem chkT_134 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K134W Hashtree.Proofs.AvxX4LoopW.K135W T134 = true := by
  decide +kernel

theorem chkT_135 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K135W Hashtree.Proofs.AvxX4LoopW.K136W T135 = true := by
  decide +kernel

theorem chkT_136 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K136W Hashtree.Proofs.AvxX4LoopW.K137W T136 = true := by
  decide +kernel

theorem chkT_137 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K137W Hashtree.Proofs.AvxX4LoopW.K138W T137 = true := by
  decide +kernel

theorem chkT_138 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K138W Hashtree.Proofs.AvxX4LoopW.K139W T138 = true := by
  decide +kernel

theorem chkT_139 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K139W Hashtree.Proofs.AvxX4LoopW.K140W T139 = true := by
  decide +kernel

theorem chkT_140 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K140W Hashtree.Proofs.AvxX4LoopW.K141W T140 = true := by
  decide +kernel

theorem chkT_141 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K141W Hashtree.Proofs.AvxX4LoopW.K142W T141 = true := by
  decide +kernel

theorem chkT_142 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K142W Hashtree.Proofs.AvxX4LoopW.K143W T142 = true := by
  decide +kernel

theorem chkT_143 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K143W Hashtree.Proofs.AvxX4LoopW.K144W T143 = true := by
  decide +kernel

theorem chkT_144 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K144W Hashtree.Proofs.AvxX4LoopW.K145W T144 = true := by
  decide +kernel

theorem chkT_145 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K145W Hashtree.Proofs.AvxX4LoopW.K146W T145 = true := by
  decide +kernel

theorem chkT_146 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K146W Hashtree.Proofs.AvxX4LoopW.K147W T146 = true := by
  decide +kernel

theorem chkT_147 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K147W Hashtree.Proofs.AvxX4LoopW.K148W T147 = true := by
  decide +kernel

theorem chkT_148 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K148W Hashtree.Proofs.AvxX4LoopW.K149W T148 = true := by
  decide +kernel

theorem chkT_149 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K149W Hashtree.Proofs.AvxX4LoopW.K150W T149 = true := by
  decide +kernel

theorem chkT_150 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K150W Hashtree.Proofs.AvxX4LoopW.K151W T150 = true := by
  decide +kernel

theorem chkT_151 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K151W Hashtree.Proofs.AvxX4LoopW.K152W T151 = true := by
  decide +kernel

theorem chkT_152 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K152W Hashtree.Proofs.AvxX4LoopW.K153W T152 = true := by
  decide +kernel

theorem chkT_153 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K153W Hashtree.Proofs.AvxX4LoopW.K154W T153 = true := by
  decide +kernel

theorem chkT_154 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K154W Hashtree.Proofs.AvxX4LoopW.K155W T154 = true := by
  decide +kernel

end Hashtree.Proofs.AvxX4LoopWOut
