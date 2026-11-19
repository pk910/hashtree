import Hashtree.Gen.WinSseX1LW.It0.D38
import Hashtree.Gen.WinSseX1LW.It0.D37
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It0
open Hashtree.Gen.WinSseX1LW

theorem slice38 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K38 K39 T38 = true := by
  decide +kernel

theorem core38_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (36)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (36)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (35))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (37))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (36))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (38))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 38)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 38)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 38)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 38)))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (38))))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (36))))
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (37))))
    (_ : V (.A 0 0 (39)) = (V (.E 0 0 (35)) + Sigma1 (V (.E 0 0 (38))) + Ch (V (.E 0 0 (38))) (V (.E 0 0 (37))) (V (.E 0 0 (36))) + V (.KW 0 0 38)) + (Sigma0 (V (.A 0 0 (38))) + Maj (V (.A 0 0 (38))) (V (.A 0 0 (37))) (V (.A 0 0 (36))))) :
    E.eval env (.add (.add (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 22)) (.var (.n 0))) (.var (.n 20))) (.var (.n 0))) (.ror (.xor (.ror (.xor (.ror (.var (.n 20)) 14) (.var (.n 20))) 5) (.var (.n 20))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 14)) 9) (.var (.n 14))) 11) (.var (.n 14))) 2)) (.or (.and (.or (.var (.n 14)) (.var (.n 24))) (.var (.n 12))) (.and (.var (.n 14)) (.var (.n 24))))) = V (.A 0 0 (39)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (37)))) :
    E.eval env (.var (.n 12)) = V (.A 0 0 (37)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (38)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (38)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (35))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (35))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (37))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (36))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (38))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 38)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 38)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 38)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 38)))
    (_ : V (.E 0 0 (39)) = V (.A 0 0 (35)) + (V (.E 0 0 (35)) + Sigma1 (V (.E 0 0 (38))) + Ch (V (.E 0 0 (38))) (V (.E 0 0 (37))) (V (.E 0 0 (36))) + V (.KW 0 0 38))) :
    E.eval env (.add (.var (.n 18)) (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 22)) (.var (.n 0))) (.var (.n 20))) (.var (.n 0))) (.ror (.xor (.ror (.xor (.ror (.var (.n 20)) 14) (.var (.n 20))) 5) (.var (.n 20))) 6)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))))) = V (.E 0 0 (39)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (38)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (38)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (37)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (37)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (36)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (36)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 36)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : V (.W 0 0 52) = sigma1 (V (.W 0 0 50)) + V (.M2 0 0 36)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 37)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : V (.W 0 0 53) = sigma1 (V (.W 0 0 51)) + V (.M2 0 0 37)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 38))) :
    E.eval env (.add (.var (.n 102)) (.const 0)) = V (.M2 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 39))) :
    E.eval env (.add (.var (.n 103)) (.const 0)) = V (.M2 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 36)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : V (.W 0 0 52) = sigma1 (V (.W 0 0 50)) + V (.M2 0 0 36)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.M2 0 0 36)))
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : V (.W 0 0 52) = sigma1 (V (.W 0 0 50)) + V (.M2 0 0 36)) :
    E.eval env (.add (.var (.n 100)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 37)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : V (.W 0 0 53) = sigma1 (V (.W 0 0 51)) + V (.M2 0 0 37)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.M2 0 0 37)))
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : V (.W 0 0 53) = sigma1 (V (.W 0 0 51)) + V (.M2 0 0 37)) :
    E.eval env (.add (.var (.n 101)) (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24)))) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 48) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 40) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 39))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 39))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 39))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core38_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 39))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step38 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L38 inp env) (hm : HMem 128 inp env) :
    Inv1 L39 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K38)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 0 (by decide)).trans (core38_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 1 (by decide)).trans (core38_6 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 2 (by decide)) (qA_succI inp 0 0 (38) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 2 (by decide)).trans (core38_12 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 3 (by decide)).trans (core38_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 4 (by decide)).trans (core38_18 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (qE_succI inp 0 0 (38) (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 5 (by decide)).trans (core38_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 6 (by decide)).trans (core38_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 7 (by decide)).trans (core38_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 8 (by decide)).trans (core38_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 52 (by decide) (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 9 (by decide)).trans (core38_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 53 (by decide) (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 10 (by decide)).trans (core38_102 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 11 (by decide)).trans (core38_103 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 12 (by decide)).trans (core38_132 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 52 (by decide) (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 13 (by decide)).trans (core38_133 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (qW_recM2 inp 0 0 52 (by decide) (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 14 (by decide)).trans (core38_134 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 53 (by decide) (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 15 (by decide)).trans (core38_135 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (qW_recM2 inp 0 0 53 (by decide) (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 16 (by decide)).trans (core38_164 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 17 (by decide)).trans (core38_165 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 18 (by decide)).trans (core38_166 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 19 (by decide)).trans (core38_167 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 20 (by decide)).trans (core38_196 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 21 (by decide)).trans (core38_197 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 22 (by decide)).trans (core38_198 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 23 (by decide)).trans (core38_199 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 24 (by decide)).trans (core38_212 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 25 (by decide)).trans (core38_213 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 26 (by decide)).trans (core38_214 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 27 (by decide)).trans (core38_215 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 28 (by decide)).trans (core38_1000 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 29 (by decide)).trans (core38_1001 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 30 (by decide)).trans (core38_1002 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 38 K38 K39 T38 slice38 env 31 (by decide)).trans (core38_1003 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | _ + 32, hk => simp only [L39, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It0
