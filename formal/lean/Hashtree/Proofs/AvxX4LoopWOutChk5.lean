import Hashtree.Proofs.AvxX4LoopWOutLab
import Hashtree.Proofs.AvxX4LoopWEntry

/-! R2c x4 — W-mode slices re-checked with the pilot's trees, part 5/8 (generated). -/
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

theorem chkT_103 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K103W Hashtree.Proofs.AvxX4LoopW.K104W T103 = true := by
  decide +kernel

theorem chkT_104 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K104W Hashtree.Proofs.AvxX4LoopW.K105W T104 = true := by
  decide +kernel

theorem chkT_105 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K105W Hashtree.Proofs.AvxX4LoopW.K106W T105 = true := by
  decide +kernel

theorem chkT_106 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K106W Hashtree.Proofs.AvxX4LoopW.K107W T106 = true := by
  decide +kernel

theorem chkT_107 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K107W Hashtree.Proofs.AvxX4LoopW.K108W T107 = true := by
  decide +kernel

theorem chkT_108 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K108W Hashtree.Proofs.AvxX4LoopW.K109W T108 = true := by
  decide +kernel

theorem chkT_109 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K109W Hashtree.Proofs.AvxX4LoopW.K110W T109 = true := by
  decide +kernel

theorem chkT_110 : sliceCheck prog 4 m0W (fun _ => false) 25 Hashtree.Proofs.AvxX4LoopW.K110W Hashtree.Proofs.AvxX4LoopW.K111W T110 = true := by
  decide +kernel

theorem chkT_111 : sliceCheck prog 4 m0W (fun _ => false) 38 Hashtree.Proofs.AvxX4LoopW.K111W Hashtree.Proofs.AvxX4LoopW.K112W T111 = true := by
  decide +kernel

theorem chkT_112 : sliceCheck prog 4 m0W (fun _ => false) 4 Hashtree.Proofs.AvxX4LoopW.K112W Hashtree.Proofs.AvxX4LoopW.K113W T112 = true := by
  decide +kernel

theorem chkT_113 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K113W Hashtree.Proofs.AvxX4LoopW.K114W T113 = true := by
  decide +kernel

theorem chkT_114 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K114W Hashtree.Proofs.AvxX4LoopW.K115W T114 = true := by
  decide +kernel

theorem chkT_115 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K115W Hashtree.Proofs.AvxX4LoopW.K116W T115 = true := by
  decide +kernel

theorem chkT_116 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K116W Hashtree.Proofs.AvxX4LoopW.K117W T116 = true := by
  decide +kernel

theorem chkT_117 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K117W Hashtree.Proofs.AvxX4LoopW.K118W T117 = true := by
  decide +kernel

theorem chkT_118 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K118W Hashtree.Proofs.AvxX4LoopW.K119W T118 = true := by
  decide +kernel

theorem chkT_119 : sliceCheck prog 4 m0W (fun _ => false) 1 Hashtree.Proofs.AvxX4LoopW.K119W Hashtree.Proofs.AvxX4LoopW.K120W T119 = true := by
  decide +kernel

theorem chkT_120 : sliceCheck prog 4 m0W (fun _ => false) 48 Hashtree.Proofs.AvxX4LoopW.K120W Hashtree.Proofs.AvxX4LoopW.K121W T120 = true := by
  decide +kernel

theorem chkT_121 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K121W Hashtree.Proofs.AvxX4LoopW.K122W T121 = true := by
  decide +kernel

theorem chkT_122 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K122W Hashtree.Proofs.AvxX4LoopW.K123W T122 = true := by
  decide +kernel

theorem chkT_123 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K123W Hashtree.Proofs.AvxX4LoopW.K124W T123 = true := by
  decide +kernel

theorem chkT_124 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K124W Hashtree.Proofs.AvxX4LoopW.K125W T124 = true := by
  decide +kernel

theorem chkT_125 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K125W Hashtree.Proofs.AvxX4LoopW.K126W T125 = true := by
  decide +kernel

theorem chkT_126 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K126W Hashtree.Proofs.AvxX4LoopW.K127W T126 = true := by
  decide +kernel

theorem chkT_127 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K127W Hashtree.Proofs.AvxX4LoopW.K128W T127 = true := by
  decide +kernel

theorem chkT_128 : sliceCheck prog 4 m0W (fun _ => false) 37 Hashtree.Proofs.AvxX4LoopW.K128W Hashtree.Proofs.AvxX4LoopW.K129W T128 = true := by
  decide +kernel

end Hashtree.Proofs.AvxX4LoopWOut
