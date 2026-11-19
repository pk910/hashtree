import Hashtree.Gen.WinSseX1LW.It.D14
import Hashtree.Gen.WinSseX1LW.It.D13
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice14 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K14 K15 T14 = true := by
  decide +kernel

theorem core14_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (12)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (12)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (11))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (13))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (12))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (14))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 14)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 14)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 14)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 14)))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (14))))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (12))))
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (13))))
    (_ : V (.A 0 0 (15)) = (V (.E 0 0 (11)) + Sigma1 (V (.E 0 0 (14))) + Ch (V (.E 0 0 (14))) (V (.E 0 0 (13))) (V (.E 0 0 (12))) + V (.KW 0 0 14)) + (Sigma0 (V (.A 0 0 (14))) + Maj (V (.A 0 0 (14))) (V (.A 0 0 (13))) (V (.A 0 0 (12))))) :
    E.eval env (.add (.add (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 22)) (.var (.n 0))) (.var (.n 20))) (.var (.n 0))) (.ror (.xor (.ror (.xor (.ror (.var (.n 20)) 14) (.var (.n 20))) 5) (.var (.n 20))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 14)) 9) (.var (.n 14))) 11) (.var (.n 14))) 2)) (.or (.and (.or (.var (.n 14)) (.var (.n 24))) (.var (.n 12))) (.and (.var (.n 14)) (.var (.n 24))))) = V (.A 0 0 (15)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (13)))) :
    E.eval env (.var (.n 12)) = V (.A 0 0 (13)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (14)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (14)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (11))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (11))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (13))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (12))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (14))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 14)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 14)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 14)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 14)))
    (_ : V (.E 0 0 (15)) = V (.A 0 0 (11)) + (V (.E 0 0 (11)) + Sigma1 (V (.E 0 0 (14))) + Ch (V (.E 0 0 (14))) (V (.E 0 0 (13))) (V (.E 0 0 (12))) + V (.KW 0 0 14))) :
    E.eval env (.add (.var (.n 18)) (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 22)) (.var (.n 0))) (.var (.n 20))) (.var (.n 0))) (.ror (.xor (.ror (.xor (.ror (.var (.n 20)) 14) (.var (.n 20))) 5) (.var (.n 20))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))))) = V (.E 0 0 (15)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (14)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (14)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (13)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (13)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (12)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (12)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 12)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 26)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 26)))
    (_ : V (.W 0 0 28) = sigma1 (V (.W 0 0 26)) + V (.M2 0 0 12)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 28) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 13)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 27)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 27)))
    (_ : V (.W 0 0 29) = sigma1 (V (.W 0 0 27)) + V (.M2 0 0 13)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 29) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 14))) :
    E.eval env (.add (.var (.n 102)) (.const 0)) = V (.M2 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 15))) :
    E.eval env (.add (.var (.n 103)) (.const 0)) = V (.M2 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 12)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 26)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 26)))
    (_ : V (.W 0 0 28) = sigma1 (V (.W 0 0 26)) + V (.M2 0 0 12)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 28) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 12)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 26)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 26)))
    (_ : V (.W 0 0 28) = sigma1 (V (.W 0 0 26)) + V (.M2 0 0 12)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 28) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 13)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 27)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 27)))
    (_ : V (.W 0 0 29) = sigma1 (V (.W 0 0 27)) + V (.M2 0 0 13)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 29) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 13)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 27)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 27)))
    (_ : V (.W 0 0 29) = sigma1 (V (.W 0 0 27)) + V (.M2 0 0 13)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 29) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 20) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 24))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 24) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 25))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 25) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 26))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 26) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 27))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 27) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 15))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 15))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 15))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core14_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 15))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step14 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L14 inp env) (hm : HMem 128 inp env) :
    Inv1 L15 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K14)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 0 (by decide)).trans (core14_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 1 (by decide)).trans (core14_6 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 2 (by decide)) (qA_succI inp 0 0 (14) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 2 (by decide)).trans (core14_12 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 3 (by decide)).trans (core14_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 4 (by decide)).trans (core14_18 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (qE_succI inp 0 0 (14) (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 5 (by decide)).trans (core14_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 6 (by decide)).trans (core14_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 7 (by decide)).trans (core14_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 8 (by decide)).trans (core14_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 28 (by decide) (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 9 (by decide)).trans (core14_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 29 (by decide) (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 10 (by decide)).trans (core14_102 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 11 (by decide)).trans (core14_103 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 12 (by decide)).trans (core14_132 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 28 (by decide) (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 13 (by decide)).trans (core14_133 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 28 (by decide) (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 14 (by decide)).trans (core14_134 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 29 (by decide) (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 15 (by decide)).trans (core14_135 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 29 (by decide) (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 16 (by decide)).trans (core14_164 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 17 (by decide)).trans (core14_165 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 18 (by decide)).trans (core14_166 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 19 (by decide)).trans (core14_167 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 20 (by decide)).trans (core14_180 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 21 (by decide)).trans (core14_181 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 22 (by decide)).trans (core14_182 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 23 (by decide)).trans (core14_183 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 24 (by decide)).trans (core14_196 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 25 (by decide)).trans (core14_197 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 26 (by decide)).trans (core14_198 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 27 (by decide)).trans (core14_199 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 28 (by decide)).trans (core14_1000 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 29 (by decide)).trans (core14_1001 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 30 (by decide)).trans (core14_1002 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 38 K14 K15 T14 slice14 env 31 (by decide)).trans (core14_1003 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | _ + 32, hk => simp only [L15, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
