import Hashtree.Gen.WinAvxX1LW.It0.D22
import Hashtree.Gen.WinAvxX1LW.It0.D21
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It0
open Hashtree.Gen.WinAvxX1LW

theorem slice22 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 36 K22 K23 T22 = true := by
  decide +kernel

theorem core22_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (20)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (20)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (19))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (21))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (20))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (22))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 22)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 22)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 22)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 22)))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (22))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (20))))
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (21))))
    (_ : V (.A 0 0 (23)) = (V (.E 0 0 (19)) + Sigma1 (V (.E 0 0 (22))) + Ch (V (.E 0 0 (22))) (V (.E 0 0 (21))) (V (.E 0 0 (20))) + V (.KW 0 0 22)) + (Sigma0 (V (.A 0 0 (22))) + Maj (V (.A 0 0 (22))) (V (.A 0 0 (21))) (V (.A 0 0 (20))))) :
    E.eval env (.add (.add (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 24)) (.var (.n 0))) (.var (.n 22))) (.var (.n 0))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 27) (.shr (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 5)) (.var (.n 22))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 27) (.shr (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 5)) (.var (.n 22))) 6))) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 23) (.shr (.var (.n 14)) 9)) (.var (.n 14))) 21) (.shr (.xor (.or (.shl (.var (.n 14)) 23) (.shr (.var (.n 14)) 9)) (.var (.n 14))) 11)) (.var (.n 14))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 23) (.shr (.var (.n 14)) 9)) (.var (.n 14))) 21) (.shr (.xor (.or (.shl (.var (.n 14)) 23) (.shr (.var (.n 14)) 9)) (.var (.n 14))) 11)) (.var (.n 14))) 2))) (.or (.and (.or (.var (.n 14)) (.var (.n 18))) (.var (.n 10))) (.and (.var (.n 14)) (.var (.n 18))))) = V (.A 0 0 (23)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (21)))) :
    E.eval env (.var (.n 10)) = V (.A 0 0 (21)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (22)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (22)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (20)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (20)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (19))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (19))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (21))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (20))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (22))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 22)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 22)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 22)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 22)))
    (_ : V (.E 0 0 (23)) = V (.A 0 0 (19)) + (V (.E 0 0 (19)) + Sigma1 (V (.E 0 0 (22))) + Ch (V (.E 0 0 (22))) (V (.E 0 0 (21))) (V (.E 0 0 (20))) + V (.KW 0 0 22))) :
    E.eval env (.add (.var (.n 20)) (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 24)) (.var (.n 0))) (.var (.n 22))) (.var (.n 0))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 27) (.shr (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 5)) (.var (.n 22))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 27) (.shr (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 5)) (.var (.n 22))) 6))) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))))) = V (.E 0 0 (23)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (22)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (22)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (21)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (21)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 20)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : V (.W 0 0 36) = sigma1 (V (.W 0 0 34)) + V (.M2 0 0 20)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 36) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 21)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : V (.W 0 0 37) = sigma1 (V (.W 0 0 35)) + V (.M2 0 0 21)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 37) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 22))) :
    E.eval env (.add (.var (.n 102)) (.const 0)) = V (.M2 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 23))) :
    E.eval env (.add (.var (.n 103)) (.const 0)) = V (.M2 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 20)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : V (.W 0 0 36) = sigma1 (V (.W 0 0 34)) + V (.M2 0 0 20)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 36) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 20)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : V (.W 0 0 36) = sigma1 (V (.W 0 0 34)) + V (.M2 0 0 20)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 36) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 21)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : V (.W 0 0 37) = sigma1 (V (.W 0 0 35)) + V (.M2 0 0 21)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 37) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 21)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : V (.W 0 0 37) = sigma1 (V (.W 0 0 35)) + V (.M2 0 0 21)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 37) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 32))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 32) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 24))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 24) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 25))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 25) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 26))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 26) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 27))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 27) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 28))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 28) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 29))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 29) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 30))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 31))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 23))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 23))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 23))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core22_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 23))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step22 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L22 inp env) (hm : HMem 128 inp env) :
    Inv1 L23 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 36 K22)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 0 (by decide)).trans (core22_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 1 (by decide)).trans (core22_6 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 2 (by decide)) (qA_succI inp 0 0 (22) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 2 (by decide)).trans (core22_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 3 (by decide)).trans (core22_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 4 (by decide)).trans (core22_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 5 (by decide)).trans (core22_20 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (qE_succI inp 0 0 (22) (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 6 (by decide)).trans (core22_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 7 (by decide)).trans (core22_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 8 (by decide)).trans (core22_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 36 (by decide) (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 9 (by decide)).trans (core22_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 37 (by decide) (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 10 (by decide)).trans (core22_102 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 11 (by decide)).trans (core22_103 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 12 (by decide)).trans (core22_132 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 36 (by decide) (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 13 (by decide)).trans (core22_133 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 36 (by decide) (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 14 (by decide)).trans (core22_134 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 37 (by decide) (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 15 (by decide)).trans (core22_135 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 37 (by decide) (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 16 (by decide)).trans (core22_164 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 17 (by decide)).trans (core22_165 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 18 (by decide)).trans (core22_166 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 19 (by decide)).trans (core22_167 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 20 (by decide)).trans (core22_196 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 21 (by decide)).trans (core22_197 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 22 (by decide)).trans (core22_198 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 23 (by decide)).trans (core22_199 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 24 (by decide)).trans (core22_212 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 25 (by decide)).trans (core22_213 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 26 (by decide)).trans (core22_214 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 27 (by decide)).trans (core22_215 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 28 (by decide)).trans (core22_1000 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 29 (by decide)).trans (core22_1001 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 30 (by decide)).trans (core22_1002 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 36 K22 K23 T22 slice22 env 31 (by decide)).trans (core22_1003 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | _ + 32, hk => simp only [L23, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It0
