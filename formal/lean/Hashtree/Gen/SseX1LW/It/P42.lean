import Hashtree.Gen.SseX1LW.It.D42
import Hashtree.Gen.SseX1LW.It.D41
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It
open Hashtree.Gen.SseX1LW

theorem slice42 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K42 K43 T42 = true := by
  decide +kernel

theorem core42_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (40)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (40)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (42)))) :
    E.eval env (.var (.n 2)) = V (.E 0 0 (42)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (39))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (39))))
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (41))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (40))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (42))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 42)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 42)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 42)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 42)))
    (_ : V (.E 0 0 (43)) = V (.A 0 0 (39)) + (V (.E 0 0 (39)) + Sigma1 (V (.E 0 0 (42))) + Ch (V (.E 0 0 (42))) (V (.E 0 0 (41))) (V (.E 0 0 (40))) + V (.KW 0 0 42))) :
    E.eval env (.add (.var (.n 6)) (.add (.var (.n 18)) (.add (.add (.xor (.and (.xor (.var (.n 16)) (.var (.n 24))) (.var (.n 2))) (.var (.n 24))) (.ror (.xor (.ror (.xor (.ror (.var (.n 2)) 14) (.var (.n 2))) 5) (.var (.n 2))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))))) = V (.E 0 0 (43)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (41)))) :
    E.eval env (.var (.n 16)) = V (.E 0 0 (41)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (39))))
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (41))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (40))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (42))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 42)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 42)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 42)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 42)))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (42))))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (40))))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (41))))
    (_ : V (.A 0 0 (43)) = (V (.E 0 0 (39)) + Sigma1 (V (.E 0 0 (42))) + Ch (V (.E 0 0 (42))) (V (.E 0 0 (41))) (V (.E 0 0 (40))) + V (.KW 0 0 42)) + (Sigma0 (V (.A 0 0 (42))) + Maj (V (.A 0 0 (42))) (V (.A 0 0 (41))) (V (.A 0 0 (40))))) :
    E.eval env (.add (.add (.add (.var (.n 18)) (.add (.add (.xor (.and (.xor (.var (.n 16)) (.var (.n 24))) (.var (.n 2))) (.var (.n 24))) (.ror (.xor (.ror (.xor (.ror (.var (.n 2)) 14) (.var (.n 2))) 5) (.var (.n 2))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 20)) 9) (.var (.n 20))) 11) (.var (.n 20))) 2)) (.or (.and (.or (.var (.n 20)) (.var (.n 0))) (.var (.n 22))) (.and (.var (.n 20)) (.var (.n 0))))) = V (.A 0 0 (43)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (42)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (42)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (41)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (41)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (40)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (40)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 40)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : V (.W 0 0 56) = sigma1 (V (.W 0 0 54)) + V (.M2 0 0 40)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 41)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : V (.W 0 0 57) = sigma1 (V (.W 0 0 55)) + V (.M2 0 0 41)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 42))) :
    E.eval env (.add (.var (.n 102)) (.const 0)) = V (.M2 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 43))) :
    E.eval env (.add (.var (.n 103)) (.const 0)) = V (.M2 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 40)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : V (.W 0 0 56) = sigma1 (V (.W 0 0 54)) + V (.M2 0 0 40)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 40)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : V (.W 0 0 56) = sigma1 (V (.W 0 0 54)) + V (.M2 0 0 40)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 41)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : V (.W 0 0 57) = sigma1 (V (.W 0 0 55)) + V (.M2 0 0 41)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 41)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : V (.W 0 0 57) = sigma1 (V (.W 0 0 55)) + V (.M2 0 0 41)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 48) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 43))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 43))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 43))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core42_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 43))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step42 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L42 inp env) (hm : HMem 128 inp env) :
    Inv1 L43 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K42)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 0 (by decide)).trans (core42_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 1 (by decide)).trans (core42_2 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 2 (by decide)).trans (core42_6 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (qE_succI inp 0 0 (42) (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 3 (by decide)).trans (core42_16 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 4 (by decide)).trans (core42_18 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 6 (by decide)) (qA_succI inp 0 0 (42) (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 5 (by decide)).trans (core42_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 6 (by decide)).trans (core42_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 7 (by decide)).trans (core42_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 8 (by decide)).trans (core42_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 56 (by decide) (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 9 (by decide)).trans (core42_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 57 (by decide) (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 10 (by decide)).trans (core42_102 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 11 (by decide)).trans (core42_103 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 12 (by decide)).trans (core42_132 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 56 (by decide) (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 13 (by decide)).trans (core42_133 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 56 (by decide) (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 14 (by decide)).trans (core42_134 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 57 (by decide) (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 15 (by decide)).trans (core42_135 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 57 (by decide) (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 16 (by decide)).trans (core42_164 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 17 (by decide)).trans (core42_165 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 18 (by decide)).trans (core42_166 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 19 (by decide)).trans (core42_167 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 20 (by decide)).trans (core42_180 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 21 (by decide)).trans (core42_181 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 22 (by decide)).trans (core42_182 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 23 (by decide)).trans (core42_183 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 24 (by decide)).trans (core42_212 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 25 (by decide)).trans (core42_213 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 26 (by decide)).trans (core42_214 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 27 (by decide)).trans (core42_215 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 28 (by decide)).trans (core42_1000 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 29 (by decide)).trans (core42_1001 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 30 (by decide)).trans (core42_1002 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 38 K42 K43 T42 slice42 env 31 (by decide)).trans (core42_1003 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | _ + 32, hk => simp only [L43, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It
