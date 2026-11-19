import Hashtree.Gen.WinSseX1LW.It.D30
import Hashtree.Gen.WinSseX1LW.It.D29
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice30 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K30 K31 T30 = true := by
  decide +kernel

theorem core30_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (28)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (28)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (27))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (29))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (28))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (30))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 30)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 30)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 30)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 30)))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (30))))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (28))))
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (29))))
    (_ : V (.A 0 0 (31)) = (V (.E 0 0 (27)) + Sigma1 (V (.E 0 0 (30))) + Ch (V (.E 0 0 (30))) (V (.E 0 0 (29))) (V (.E 0 0 (28))) + V (.KW 0 0 30)) + (Sigma0 (V (.A 0 0 (30))) + Maj (V (.A 0 0 (30))) (V (.A 0 0 (29))) (V (.A 0 0 (28))))) :
    E.eval env (.add (.add (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 22)) (.var (.n 0))) (.var (.n 20))) (.var (.n 0))) (.ror (.xor (.ror (.xor (.ror (.var (.n 20)) 14) (.var (.n 20))) 5) (.var (.n 20))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 14)) 9) (.var (.n 14))) 11) (.var (.n 14))) 2)) (.or (.and (.or (.var (.n 14)) (.var (.n 24))) (.var (.n 12))) (.and (.var (.n 14)) (.var (.n 24))))) = V (.A 0 0 (31)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (29)))) :
    E.eval env (.var (.n 12)) = V (.A 0 0 (29)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (30)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (30)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (27))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (27))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (29))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (28))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (30))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 30)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 30)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 30)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 30)))
    (_ : V (.E 0 0 (31)) = V (.A 0 0 (27)) + (V (.E 0 0 (27)) + Sigma1 (V (.E 0 0 (30))) + Ch (V (.E 0 0 (30))) (V (.E 0 0 (29))) (V (.E 0 0 (28))) + V (.KW 0 0 30))) :
    E.eval env (.add (.var (.n 18)) (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 22)) (.var (.n 0))) (.var (.n 20))) (.var (.n 0))) (.ror (.xor (.ror (.xor (.ror (.var (.n 20)) 14) (.var (.n 20))) 5) (.var (.n 20))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))))) = V (.E 0 0 (31)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (30)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (30)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (29)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (29)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (28)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (28)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 28)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : V (.W 0 0 44) = sigma1 (V (.W 0 0 42)) + V (.M2 0 0 28)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 29)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : V (.W 0 0 45) = sigma1 (V (.W 0 0 43)) + V (.M2 0 0 29)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 30))) :
    E.eval env (.add (.var (.n 102)) (.const 0)) = V (.M2 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 31))) :
    E.eval env (.add (.var (.n 103)) (.const 0)) = V (.M2 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 28)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : V (.W 0 0 44) = sigma1 (V (.W 0 0 42)) + V (.M2 0 0 28)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 28)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : V (.W 0 0 44) = sigma1 (V (.W 0 0 42)) + V (.M2 0 0 28)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 29)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : V (.W 0 0 45) = sigma1 (V (.W 0 0 43)) + V (.M2 0 0 29)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 29)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : V (.W 0 0 45) = sigma1 (V (.W 0 0 43)) + V (.M2 0 0 29)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 32))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 32) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 36))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 36) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 37))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 37) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 38))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 39))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 40) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 31))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 31))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 31))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core30_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 31))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step30 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L30 inp env) (hm : HMem 128 inp env) :
    Inv1 L31 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K30)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 0 (by decide)).trans (core30_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 1 (by decide)).trans (core30_6 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 2 (by decide)) (qA_succI inp 0 0 (30) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 2 (by decide)).trans (core30_12 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 3 (by decide)).trans (core30_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 4 (by decide)).trans (core30_18 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (qE_succI inp 0 0 (30) (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 5 (by decide)).trans (core30_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 6 (by decide)).trans (core30_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 7 (by decide)).trans (core30_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 8 (by decide)).trans (core30_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 44 (by decide) (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 9 (by decide)).trans (core30_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 45 (by decide) (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 10 (by decide)).trans (core30_102 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 11 (by decide)).trans (core30_103 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 12 (by decide)).trans (core30_132 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 44 (by decide) (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 13 (by decide)).trans (core30_133 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 44 (by decide) (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 14 (by decide)).trans (core30_134 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 45 (by decide) (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 15 (by decide)).trans (core30_135 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 45 (by decide) (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 16 (by decide)).trans (core30_164 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 17 (by decide)).trans (core30_165 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 18 (by decide)).trans (core30_166 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 19 (by decide)).trans (core30_167 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 20 (by decide)).trans (core30_180 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 21 (by decide)).trans (core30_181 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 22 (by decide)).trans (core30_182 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 23 (by decide)).trans (core30_183 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 24 (by decide)).trans (core30_196 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 25 (by decide)).trans (core30_197 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 26 (by decide)).trans (core30_198 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 27 (by decide)).trans (core30_199 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 28 (by decide)).trans (core30_1000 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 29 (by decide)).trans (core30_1001 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 30 (by decide)).trans (core30_1002 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 38 K30 K31 T30 slice30 env 31 (by decide)).trans (core30_1003 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | _ + 32, hk => simp only [L31, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
