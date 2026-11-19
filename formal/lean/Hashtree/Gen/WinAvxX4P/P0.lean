import Hashtree.Asm.Chain
import Hashtree.Asm.SpecQV
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Asm.X86SymWin
import Hashtree.Gen.WinAvxX4P.Ro
import Hashtree.Gen.WinAvxX4P.Shapes
import Hashtree.Gen.WinAvxX4P.D0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86Win.AvxX4 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX4P

theorem slice0 : sliceCheck prog 4 m0q (fun pc => decide (pc ∈ ([2] : List Nat))) 8 (entrySW 24) K1 T0 = true := by
  decide +kernel

theorem step0 (inp : Nat → Byte) (env : Key → W32) (hI : InvC inp env L0) (hm : HMem 256 inp env) :
    InvC inp (envAbs env (run prog 4 m0q (fun pc => decide (pc ∈ ([2] : List Nat))) 8 (entrySW 24))) L1 := by
  exact invC_of_trees inp env _ T0 L1 (slice_trees_mem prog 4 _ _ 8 (entrySW 24) K1 T0 slice0 env)
      trivial

end Hashtree.Gen.WinAvxX4P
