import Hashtree.Gen.WinAvxX1LW.It.D17
import Hashtree.Gen.WinAvxX1LW.It.D16
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It
open Hashtree.Gen.WinAvxX1LW

theorem slice17 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 36 K17 K18 T17 = true := by
  decide +kernel

theorem core17_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (16)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (16)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (15)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (15)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (17)))) :
    E.eval env (.var (.n 10)) = V (.E 0 0 (17)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (14))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (14))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (16))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (15))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (17))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 17)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 17)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 17)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 17)))
    (_ : V (.E 0 0 (18)) = V (.A 0 0 (14)) + (V (.E 0 0 (14)) + Sigma1 (V (.E 0 0 (17))) + Ch (V (.E 0 0 (17))) (V (.E 0 0 (16))) (V (.E 0 0 (15))) + V (.KW 0 0 17))) :
    E.eval env (.add (.var (.n 14)) (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 10))) (.var (.n 20))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 6))) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))))) = V (.E 0 0 (18)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (16)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (16)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (15)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (15)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (14))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (16))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (15))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (17))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 17)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 17)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 17)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 17)))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (17))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (15))))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (16))))
    (_ : V (.A 0 0 (18)) = (V (.E 0 0 (14)) + Sigma1 (V (.E 0 0 (17))) + Ch (V (.E 0 0 (17))) (V (.E 0 0 (16))) (V (.E 0 0 (15))) + V (.KW 0 0 17)) + (Sigma0 (V (.A 0 0 (17))) + Maj (V (.A 0 0 (17))) (V (.A 0 0 (16))) (V (.A 0 0 (15))))) :
    E.eval env (.add (.add (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 10))) (.var (.n 20))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 6))) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 21) (.shr (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 11)) (.var (.n 24))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 21) (.shr (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 11)) (.var (.n 24))) 2))) (.or (.and (.or (.var (.n 24)) (.var (.n 6))) (.var (.n 0))) (.and (.var (.n 24)) (.var (.n 6))))) = V (.A 0 0 (18)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (17)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (17)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.add (.q (.W 0 0 25)) (.q (.W 0 0 16))))
    (_ : env (.n 148) = QE.eval V inp (.or (.shl (.q (.W 0 0 17)) 25) (.shr (.q (.W 0 0 17)) 7)))
    (_ : env (.n 116) = QE.eval V inp (.q (.W 0 0 17)))
    (_ : V (.M2 0 0 16) = V (.M1 0 0 16) + V (.W 0 0 25))
    (_ : V (.M1 0 0 16) = V (.W 0 0 16) + sigma0 (V (.W 0 0 17))) :
    E.eval env (.add (.var (.n 100)) (.xor (.xor (.xor (.var (.n 148)) (.shl (.var (.n 116)) 14)) (.shr (.var (.n 116)) 18)) (.shr (.var (.n 116)) 3))) = V (.M2 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.add (.q (.W 0 0 26)) (.q (.W 0 0 17))))
    (_ : env (.n 149) = QE.eval V inp (.or (.shl (.q (.W 0 0 18)) 25) (.shr (.q (.W 0 0 18)) 7)))
    (_ : env (.n 117) = QE.eval V inp (.q (.W 0 0 18)))
    (_ : V (.M2 0 0 17) = V (.M1 0 0 17) + V (.W 0 0 26))
    (_ : V (.M1 0 0 17) = V (.W 0 0 17) + sigma0 (V (.W 0 0 18))) :
    E.eval env (.add (.var (.n 101)) (.xor (.xor (.xor (.var (.n 149)) (.shl (.var (.n 117)) 14)) (.shr (.var (.n 117)) 18)) (.shr (.var (.n 117)) 3))) = V (.M2 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.add (.q (.W 0 0 27)) (.q (.W 0 0 18))))
    (_ : env (.n 150) = QE.eval V inp (.or (.shl (.q (.W 0 0 19)) 25) (.shr (.q (.W 0 0 19)) 7)))
    (_ : env (.n 118) = QE.eval V inp (.q (.W 0 0 19)))
    (_ : V (.M2 0 0 18) = V (.M1 0 0 18) + V (.W 0 0 27))
    (_ : V (.M1 0 0 18) = V (.W 0 0 18) + sigma0 (V (.W 0 0 19))) :
    E.eval env (.add (.var (.n 102)) (.xor (.xor (.xor (.var (.n 150)) (.shl (.var (.n 118)) 14)) (.shr (.var (.n 118)) 18)) (.shr (.var (.n 118)) 3))) = V (.M2 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.add (.q (.W 0 0 28)) (.q (.W 0 0 19))))
    (_ : env (.n 151) = QE.eval V inp (.or (.shl (.q (.W 0 0 20)) 25) (.shr (.q (.W 0 0 20)) 7)))
    (_ : env (.n 119) = QE.eval V inp (.q (.W 0 0 20)))
    (_ : V (.M2 0 0 19) = V (.M1 0 0 19) + V (.W 0 0 28))
    (_ : V (.M1 0 0 19) = V (.W 0 0 19) + sigma0 (V (.W 0 0 20))) :
    E.eval env (.add (.var (.n 103)) (.xor (.xor (.xor (.var (.n 151)) (.shl (.var (.n 119)) 14)) (.shr (.var (.n 119)) 18)) (.shr (.var (.n 119)) 3))) = V (.M2 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 30))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 30))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 31))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 31))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 20) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 24))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 24) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 25))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 25) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 26))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 26) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 27))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 27) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 28))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 28) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 29))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 29) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 30))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 31))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 19))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 19))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 19))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 19))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 18))) :
    E.eval env (.var (.n 1004)) = V (.KW 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 18))) :
    E.eval env (.var (.n 1005)) = V (.KW 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 18))) :
    E.eval env (.var (.n 1006)) = V (.KW 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core17_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 18))) :
    E.eval env (.var (.n 1007)) = V (.KW 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step17 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L17 inp env) (hm : HMem 128 inp env) :
    Inv1 L18 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 36 K17)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 0 (by decide)).trans (core17_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 1 (by decide)).trans (core17_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 2 (by decide)).trans (core17_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 3 (by decide)).trans (core17_14 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (qE_succI inp 0 0 (17) (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 4 (by decide)).trans (core17_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 5 (by decide)).trans (core17_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 6 (by decide)).trans (core17_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (qA_succI inp 0 0 (17) (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 7 (by decide)).trans (core17_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 8 (by decide)).trans (core17_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 16 (by decide)) (inv1_get hI 12 (by decide)) (qM2 inp 0 0 16) (qM1 inp 0 0 16))
  | 9, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 9 (by decide)).trans (core17_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 13 (by decide)) (qM2 inp 0 0 17) (qM1 inp 0 0 17))
  | 10, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 10 (by decide)).trans (core17_102 (qv inp) inp env (inv1_get hI 10 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 14 (by decide)) (qM2 inp 0 0 18) (qM1 inp 0 0 18))
  | 11, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 11 (by decide)).trans (core17_103 (qv inp) inp env (inv1_get hI 11 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 15 (by decide)) (qM2 inp 0 0 19) (qM1 inp 0 0 19))
  | 12, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 12 (by decide)).trans (core17_132 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 13 (by decide)).trans (core17_133 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 14 (by decide)).trans (core17_134 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 15 (by decide)).trans (core17_135 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 16 (by decide)).trans (core17_180 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 17 (by decide)).trans (core17_181 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 18 (by decide)).trans (core17_182 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 19 (by decide)).trans (core17_183 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 20 (by decide)).trans (core17_196 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 21 (by decide)).trans (core17_197 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 22 (by decide)).trans (core17_198 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 23 (by decide)).trans (core17_199 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 24 (by decide)).trans (core17_212 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 25 (by decide)).trans (core17_213 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 26 (by decide)).trans (core17_214 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 27 (by decide)).trans (core17_215 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 28 (by decide)).trans (core17_1000 (qv inp) inp env (inv1_get hI 32 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 29 (by decide)).trans (core17_1001 (qv inp) inp env (inv1_get hI 33 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 30 (by decide)).trans (core17_1002 (qv inp) inp env (inv1_get hI 34 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 31 (by decide)).trans (core17_1003 (qv inp) inp env (inv1_get hI 35 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 32 (by decide)).trans (core17_1004 (qv inp) inp env (inv1_get hI 36 (by decide)))
  | 33, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 33 (by decide)).trans (core17_1005 (qv inp) inp env (inv1_get hI 37 (by decide)))
  | 34, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 34 (by decide)).trans (core17_1006 (qv inp) inp env (inv1_get hI 38 (by decide)))
  | 35, _ => exact (slice_trees prog 4 _ _ 36 K17 K18 T17 slice17 env 35 (by decide)).trans (core17_1007 (qv inp) inp env (inv1_get hI 39 (by decide)))
  | _ + 36, hk => simp only [L18, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It
