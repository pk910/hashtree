import Hashtree.Gen.WinSseX1LW.It.D2
import Hashtree.Gen.WinSseX1LW.It.D1
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice2 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K2 K3 T2 = true := by
  decide +kernel

theorem core2_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (1))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (2))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 2)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 2)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 2)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 2)))
    (_ : V (.E 0 0 (3)) = V (.A 0 0 (-1)) + (V (.E 0 0 (-1)) + Sigma1 (V (.E 0 0 (2))) + Ch (V (.E 0 0 (2))) (V (.E 0 0 (1))) (V (.E 0 0 (0))) + V (.KW 0 0 2)))
    (_ : V (.A 0 0 (-1)) = V (.H 0 0 1))
    (_ : V (.H 0 0 1) = 3144134277#32)
    (_ : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (_ : V (.H 0 0 5) = 2600822924#32)
    (_ : V (.E 0 0 (0)) = V (.H 0 0 4))
    (_ : V (.H 0 0 4) = 1359893119#32) :
    E.eval env (.add (.const 3144134277) (.add (.const 2600822924) (.add (.add (.xor (.and (.xor (.var (.n 12)) (.const 1359893119)) (.var (.n 14))) (.const 1359893119)) (.ror (.xor (.ror (.xor (.ror (.var (.n 14)) 14) (.var (.n 14))) 5) (.var (.n 14))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))))) = V (.E 0 0 (3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (1)))) :
    E.eval env (.var (.n 12)) = V (.E 0 0 (1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (2)))) :
    E.eval env (.var (.n 14)) = V (.E 0 0 (2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (1))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (2))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 2)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 2)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 2)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 2)))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (2))))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (1))))
    (_ : V (.A 0 0 (3)) = (V (.E 0 0 (-1)) + Sigma1 (V (.E 0 0 (2))) + Ch (V (.E 0 0 (2))) (V (.E 0 0 (1))) (V (.E 0 0 (0))) + V (.KW 0 0 2)) + (Sigma0 (V (.A 0 0 (2))) + Maj (V (.A 0 0 (2))) (V (.A 0 0 (1))) (V (.A 0 0 (0)))))
    (_ : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (_ : V (.H 0 0 5) = 2600822924#32)
    (_ : V (.E 0 0 (0)) = V (.H 0 0 4))
    (_ : V (.H 0 0 4) = 1359893119#32)
    (_ : V (.A 0 0 (0)) = V (.H 0 0 0))
    (_ : V (.H 0 0 0) = 1779033703#32) :
    E.eval env (.add (.add (.add (.const 2600822924) (.add (.add (.xor (.and (.xor (.var (.n 12)) (.const 1359893119)) (.var (.n 14))) (.const 1359893119)) (.ror (.xor (.ror (.xor (.ror (.var (.n 14)) 14) (.var (.n 14))) 5) (.var (.n 14))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 20)) 9) (.var (.n 20))) 11) (.var (.n 20))) 2)) (.or (.and (.or (.var (.n 20)) (.const 1779033703)) (.var (.n 22))) (.and (.var (.n 20)) (.const 1779033703)))) = V (.A 0 0 (3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (2)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (1)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 0)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 14)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 14)))
    (_ : V (.W 0 0 16) = sigma1 (V (.W 0 0 14)) + V (.M2 0 0 0)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 1)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 15)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 15)))
    (_ : V (.W 0 0 17) = sigma1 (V (.W 0 0 15)) + V (.M2 0 0 1)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 2))) :
    E.eval env (.add (.var (.n 102)) (.const 0)) = V (.M2 0 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 3))) :
    E.eval env (.add (.var (.n 103)) (.const 0)) = V (.M2 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 0)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 14)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 14)))
    (_ : V (.W 0 0 16) = sigma1 (V (.W 0 0 14)) + V (.M2 0 0 0)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 0)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 14)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 14)))
    (_ : V (.W 0 0 16) = sigma1 (V (.W 0 0 14)) + V (.M2 0 0 0)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 1)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 15)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 15)))
    (_ : V (.W 0 0 17) = sigma1 (V (.W 0 0 15)) + V (.M2 0 0 1)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 1)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 15)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 15)))
    (_ : V (.W 0 0 17) = sigma1 (V (.W 0 0 15)) + V (.M2 0 0 1)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 4))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 4) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 8) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 12) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 13))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 13) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 3))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 3))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 3))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core2_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 3))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step2 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L2 inp env) (hm : HMem 128 inp env) :
    Inv1 L3 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K2)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 0 (by decide)).trans (core2_6 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qE_succI inp 0 0 (2) (by decide)) (qA_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)))
  | 1, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 1 (by decide)).trans (core2_12 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 2 (by decide)).trans (core2_14 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 3 (by decide)).trans (core2_18 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 3 (by decide)) (qA_succI inp 0 0 (2) (by decide)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)))
  | 4, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 4 (by decide)).trans (core2_20 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 5 (by decide)).trans (core2_22 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 6 (by decide)).trans (core2_100 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 9 (by decide)) (qW_recM2 inp 0 0 16 (by decide) (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 7 (by decide)).trans (core2_101 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 10 (by decide)) (inv1_get hI 11 (by decide)) (qW_recM2 inp 0 0 17 (by decide) (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 8 (by decide)).trans (core2_102 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 9 (by decide)).trans (core2_103 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 10 (by decide)).trans (core2_132 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 9 (by decide)) (qW_recM2 inp 0 0 16 (by decide) (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 11 (by decide)).trans (core2_133 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 9 (by decide)) (qW_recM2 inp 0 0 16 (by decide) (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 12 (by decide)).trans (core2_134 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 10 (by decide)) (inv1_get hI 11 (by decide)) (qW_recM2 inp 0 0 17 (by decide) (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 13 (by decide)).trans (core2_135 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 10 (by decide)) (inv1_get hI 11 (by decide)) (qW_recM2 inp 0 0 17 (by decide) (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 14 (by decide)).trans (core2_180 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 15 (by decide)).trans (core2_181 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 16 (by decide)).trans (core2_182 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 17 (by decide)).trans (core2_183 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 18 (by decide)).trans (core2_196 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 19 (by decide)).trans (core2_197 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 20 (by decide)).trans (core2_198 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 21 (by decide)).trans (core2_199 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 22 (by decide)).trans (core2_212 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 23 (by decide)).trans (core2_213 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 24 (by decide)).trans (core2_214 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 25 (by decide)).trans (core2_215 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 26 (by decide)).trans (core2_1000 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 27 (by decide)).trans (core2_1001 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 28 (by decide)).trans (core2_1002 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 38 K2 K3 T2 slice2 env 29 (by decide)).trans (core2_1003 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | _ + 30, hk => simp only [L3, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
