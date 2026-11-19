import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.Shapes
import Hashtree.Gen.WinAvx2X8P.D2
import Hashtree.Gen.WinAvx2X8P.D1

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.Avx2X8 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvx2X8P

theorem slice2 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 8 K2 K3 T2 = true := by
  decide +kernel

theorem step2 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L2) (hm : HMem 512 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([] : List Nat))) 8 K2)) L3 := by
  exact invC_of_trees inp env _ T2 L3 (slice_trees_mem prog 4 _ _ 8 K2 K3 T2 slice2 env)
      trivial

end Hashtree.Gen.WinAvx2X8P
