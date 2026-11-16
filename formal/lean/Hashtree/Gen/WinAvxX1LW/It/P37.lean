import Hashtree.Gen.WinAvxX1LW.It.D37
import Hashtree.Gen.WinAvxX1LW.It.D36
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It
open Hashtree.Gen.WinAvxX1LW

theorem slice37 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 36 K37 K38 T37 = true := by
  decide +kernel

theorem core37_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (36)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (36)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (35)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (35)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (37)))) :
    E.eval env (.var (.n 10)) = V (.A 0 0 (37)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (34))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (36))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (35))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (37))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 37)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 37)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 37)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 37)))
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (37))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (35))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (36))))
    (_ : V (.A 0 0 (38)) = (V (.E 0 0 (34)) + Sigma1 (V (.E 0 0 (37))) + Ch (V (.E 0 0 (37))) (V (.E 0 0 (36))) (V (.E 0 0 (35))) + V (.KW 0 0 37)) + (Sigma0 (V (.A 0 0 (37))) + Maj (V (.A 0 0 (37))) (V (.A 0 0 (36))) (V (.A 0 0 (35))))) :
    E.eval env (.add (.add (.add (.var (.n 14)) (.add (.add (.xor (.and (.xor (.var (.n 0)) (.var (.n 6))) (.var (.n 24))) (.var (.n 6))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 18) (.shr (.var (.n 24)) 14)) (.var (.n 24))) 27) (.shr (.xor (.or (.shl (.var (.n 24)) 18) (.shr (.var (.n 24)) 14)) (.var (.n 24))) 5)) (.var (.n 24))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 18) (.shr (.var (.n 24)) 14)) (.var (.n 24))) 27) (.shr (.xor (.or (.shl (.var (.n 24)) 18) (.shr (.var (.n 24)) 14)) (.var (.n 24))) 5)) (.var (.n 24))) 6))) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 23) (.shr (.var (.n 10)) 9)) (.var (.n 10))) 21) (.shr (.xor (.or (.shl (.var (.n 10)) 23) (.shr (.var (.n 10)) 9)) (.var (.n 10))) 11)) (.var (.n 10))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 23) (.shr (.var (.n 10)) 9)) (.var (.n 10))) 21) (.shr (.xor (.or (.shl (.var (.n 10)) 23) (.shr (.var (.n 10)) 9)) (.var (.n 10))) 11)) (.var (.n 10))) 2))) (.or (.and (.or (.var (.n 10)) (.var (.n 20))) (.var (.n 18))) (.and (.var (.n 10)) (.var (.n 20))))) = V (.A 0 0 (38)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (36)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (36)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (35)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (35)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (34))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (34))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (36))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (35))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (37))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 37)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 37)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 37)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 37)))
    (_ : V (.E 0 0 (38)) = V (.A 0 0 (34)) + (V (.E 0 0 (34)) + Sigma1 (V (.E 0 0 (37))) + Ch (V (.E 0 0 (37))) (V (.E 0 0 (36))) (V (.E 0 0 (35))) + V (.KW 0 0 37))) :
    E.eval env (.add (.var (.n 22)) (.add (.var (.n 14)) (.add (.add (.xor (.and (.xor (.var (.n 0)) (.var (.n 6))) (.var (.n 24))) (.var (.n 6))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 18) (.shr (.var (.n 24)) 14)) (.var (.n 24))) 27) (.shr (.xor (.or (.shl (.var (.n 24)) 18) (.shr (.var (.n 24)) 14)) (.var (.n 24))) 5)) (.var (.n 24))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 18) (.shr (.var (.n 24)) 14)) (.var (.n 24))) 27) (.shr (.xor (.or (.shl (.var (.n 24)) 18) (.shr (.var (.n 24)) 14)) (.var (.n 24))) 5)) (.var (.n 24))) 6))) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))))) = V (.E 0 0 (38)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (37)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (37)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.add (.q (.W 0 0 45)) (.q (.W 0 0 36))))
    (_ : env (.n 148) = QE.eval V inp (.or (.shl (.q (.W 0 0 37)) 25) (.shr (.q (.W 0 0 37)) 7)))
    (_ : env (.n 116) = QE.eval V inp (.q (.W 0 0 37)))
    (_ : V (.M2 0 0 36) = V (.M1 0 0 36) + V (.W 0 0 45))
    (_ : V (.M1 0 0 36) = V (.W 0 0 36) + sigma0 (V (.W 0 0 37))) :
    E.eval env (.add (.var (.n 100)) (.xor (.xor (.xor (.var (.n 148)) (.shl (.var (.n 116)) 14)) (.shr (.var (.n 116)) 18)) (.shr (.var (.n 116)) 3))) = V (.M2 0 0 36) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.add (.q (.W 0 0 46)) (.q (.W 0 0 37))))
    (_ : env (.n 149) = QE.eval V inp (.or (.shl (.q (.W 0 0 38)) 25) (.shr (.q (.W 0 0 38)) 7)))
    (_ : env (.n 117) = QE.eval V inp (.q (.W 0 0 38)))
    (_ : V (.M2 0 0 37) = V (.M1 0 0 37) + V (.W 0 0 46))
    (_ : V (.M1 0 0 37) = V (.W 0 0 37) + sigma0 (V (.W 0 0 38))) :
    E.eval env (.add (.var (.n 101)) (.xor (.xor (.xor (.var (.n 149)) (.shl (.var (.n 117)) 14)) (.shr (.var (.n 117)) 18)) (.shr (.var (.n 117)) 3))) = V (.M2 0 0 37) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.add (.q (.W 0 0 47)) (.q (.W 0 0 38))))
    (_ : env (.n 150) = QE.eval V inp (.or (.shl (.q (.W 0 0 39)) 25) (.shr (.q (.W 0 0 39)) 7)))
    (_ : env (.n 118) = QE.eval V inp (.q (.W 0 0 39)))
    (_ : V (.M2 0 0 38) = V (.M1 0 0 38) + V (.W 0 0 47))
    (_ : V (.M1 0 0 38) = V (.W 0 0 38) + sigma0 (V (.W 0 0 39))) :
    E.eval env (.add (.var (.n 102)) (.xor (.xor (.xor (.var (.n 150)) (.shl (.var (.n 118)) 14)) (.shr (.var (.n 118)) 18)) (.shr (.var (.n 118)) 3))) = V (.M2 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.add (.q (.W 0 0 48)) (.q (.W 0 0 39))))
    (_ : env (.n 151) = QE.eval V inp (.or (.shl (.q (.W 0 0 40)) 25) (.shr (.q (.W 0 0 40)) 7)))
    (_ : env (.n 119) = QE.eval V inp (.q (.W 0 0 40)))
    (_ : V (.M2 0 0 39) = V (.M1 0 0 39) + V (.W 0 0 48))
    (_ : V (.M1 0 0 39) = V (.W 0 0 39) + sigma0 (V (.W 0 0 40))) :
    E.eval env (.add (.var (.n 103)) (.xor (.xor (.xor (.var (.n 151)) (.shl (.var (.n 119)) 14)) (.shr (.var (.n 119)) 18)) (.shr (.var (.n 119)) 3))) = V (.M2 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 48) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 40) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 39))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 39))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 39))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 39))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 38))) :
    E.eval env (.var (.n 1004)) = V (.KW 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 38))) :
    E.eval env (.var (.n 1005)) = V (.KW 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 38))) :
    E.eval env (.var (.n 1006)) = V (.KW 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core37_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 38))) :
    E.eval env (.var (.n 1007)) = V (.KW 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step37 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L37 inp env) (hm : HMem 128 inp env) :
    Inv1 L38 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 36 K37)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 0 (by decide)).trans (core37_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 1 (by decide)).trans (core37_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 2 (by decide)).trans (core37_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 3 (by decide)).trans (core37_14 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 4 (by decide)) (qA_succI inp 0 0 (37) (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 4 (by decide)).trans (core37_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 5 (by decide)).trans (core37_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 6 (by decide)).trans (core37_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (qE_succI inp 0 0 (37) (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 7 (by decide)).trans (core37_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 8 (by decide)).trans (core37_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 16 (by decide)) (inv1_get hI 12 (by decide)) (qM2 inp 0 0 36) (qM1 inp 0 0 36))
  | 9, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 9 (by decide)).trans (core37_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 13 (by decide)) (qM2 inp 0 0 37) (qM1 inp 0 0 37))
  | 10, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 10 (by decide)).trans (core37_102 (qv inp) inp env (inv1_get hI 10 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 14 (by decide)) (qM2 inp 0 0 38) (qM1 inp 0 0 38))
  | 11, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 11 (by decide)).trans (core37_103 (qv inp) inp env (inv1_get hI 11 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 15 (by decide)) (qM2 inp 0 0 39) (qM1 inp 0 0 39))
  | 12, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 12 (by decide)).trans (core37_132 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 13 (by decide)).trans (core37_133 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 14 (by decide)).trans (core37_134 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 15 (by decide)).trans (core37_135 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 16 (by decide)).trans (core37_164 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 17 (by decide)).trans (core37_165 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 18 (by decide)).trans (core37_166 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 19 (by decide)).trans (core37_167 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 20 (by decide)).trans (core37_196 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 21 (by decide)).trans (core37_197 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 22 (by decide)).trans (core37_198 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 23 (by decide)).trans (core37_199 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 24 (by decide)).trans (core37_212 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 25 (by decide)).trans (core37_213 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 26 (by decide)).trans (core37_214 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 27 (by decide)).trans (core37_215 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 28 (by decide)).trans (core37_1000 (qv inp) inp env (inv1_get hI 32 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 29 (by decide)).trans (core37_1001 (qv inp) inp env (inv1_get hI 33 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 30 (by decide)).trans (core37_1002 (qv inp) inp env (inv1_get hI 34 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 31 (by decide)).trans (core37_1003 (qv inp) inp env (inv1_get hI 35 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 32 (by decide)).trans (core37_1004 (qv inp) inp env (inv1_get hI 36 (by decide)))
  | 33, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 33 (by decide)).trans (core37_1005 (qv inp) inp env (inv1_get hI 37 (by decide)))
  | 34, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 34 (by decide)).trans (core37_1006 (qv inp) inp env (inv1_get hI 38 (by decide)))
  | 35, _ => exact (slice_trees prog 4 _ _ 36 K37 K38 T37 slice37 env 35 (by decide)).trans (core37_1007 (qv inp) inp env (inv1_get hI 39 (by decide)))
  | _ + 36, hk => simp only [L38, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It
