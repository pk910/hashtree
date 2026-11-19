import Hashtree.Gen.WinAvxX1LW.It.D33
import Hashtree.Gen.WinAvxX1LW.It.D32
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It
open Hashtree.Gen.WinAvxX1LW

theorem slice33 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 36 K33 K34 T33 = true := by
  decide +kernel

theorem core33_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (32)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (32)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (31)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (31)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (33)))) :
    E.eval env (.var (.n 10)) = V (.E 0 0 (33)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (30))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (30))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (32))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (31))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (33))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 33)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 33)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 33)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 33)))
    (_ : V (.E 0 0 (34)) = V (.A 0 0 (30)) + (V (.E 0 0 (30)) + Sigma1 (V (.E 0 0 (33))) + Ch (V (.E 0 0 (33))) (V (.E 0 0 (32))) (V (.E 0 0 (31))) + V (.KW 0 0 33))) :
    E.eval env (.add (.var (.n 14)) (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 10))) (.var (.n 20))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 6))) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))))) = V (.E 0 0 (34)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (32)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (32)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (31)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (31)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (30))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (32))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (31))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (33))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 33)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 33)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 33)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 33)))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (33))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (31))))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (32))))
    (_ : V (.A 0 0 (34)) = (V (.E 0 0 (30)) + Sigma1 (V (.E 0 0 (33))) + Ch (V (.E 0 0 (33))) (V (.E 0 0 (32))) (V (.E 0 0 (31))) + V (.KW 0 0 33)) + (Sigma0 (V (.A 0 0 (33))) + Maj (V (.A 0 0 (33))) (V (.A 0 0 (32))) (V (.A 0 0 (31))))) :
    E.eval env (.add (.add (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 10))) (.var (.n 20))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 6))) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 21) (.shr (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 11)) (.var (.n 24))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 21) (.shr (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 11)) (.var (.n 24))) 2))) (.or (.and (.or (.var (.n 24)) (.var (.n 6))) (.var (.n 0))) (.and (.var (.n 24)) (.var (.n 6))))) = V (.A 0 0 (34)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (33)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (33)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.add (.q (.W 0 0 41)) (.q (.W 0 0 32))))
    (_ : env (.n 148) = QE.eval V inp (.or (.shl (.q (.W 0 0 33)) 25) (.shr (.q (.W 0 0 33)) 7)))
    (_ : env (.n 116) = QE.eval V inp (.q (.W 0 0 33)))
    (_ : V (.M2 0 0 32) = V (.M1 0 0 32) + V (.W 0 0 41))
    (_ : V (.M1 0 0 32) = V (.W 0 0 32) + sigma0 (V (.W 0 0 33))) :
    E.eval env (.add (.var (.n 100)) (.xor (.xor (.xor (.var (.n 148)) (.shl (.var (.n 116)) 14)) (.shr (.var (.n 116)) 18)) (.shr (.var (.n 116)) 3))) = V (.M2 0 0 32) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.add (.q (.W 0 0 42)) (.q (.W 0 0 33))))
    (_ : env (.n 149) = QE.eval V inp (.or (.shl (.q (.W 0 0 34)) 25) (.shr (.q (.W 0 0 34)) 7)))
    (_ : env (.n 117) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : V (.M2 0 0 33) = V (.M1 0 0 33) + V (.W 0 0 42))
    (_ : V (.M1 0 0 33) = V (.W 0 0 33) + sigma0 (V (.W 0 0 34))) :
    E.eval env (.add (.var (.n 101)) (.xor (.xor (.xor (.var (.n 149)) (.shl (.var (.n 117)) 14)) (.shr (.var (.n 117)) 18)) (.shr (.var (.n 117)) 3))) = V (.M2 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.add (.q (.W 0 0 43)) (.q (.W 0 0 34))))
    (_ : env (.n 150) = QE.eval V inp (.or (.shl (.q (.W 0 0 35)) 25) (.shr (.q (.W 0 0 35)) 7)))
    (_ : env (.n 118) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : V (.M2 0 0 34) = V (.M1 0 0 34) + V (.W 0 0 43))
    (_ : V (.M1 0 0 34) = V (.W 0 0 34) + sigma0 (V (.W 0 0 35))) :
    E.eval env (.add (.var (.n 102)) (.xor (.xor (.xor (.var (.n 150)) (.shl (.var (.n 118)) 14)) (.shr (.var (.n 118)) 18)) (.shr (.var (.n 118)) 3))) = V (.M2 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.add (.q (.W 0 0 44)) (.q (.W 0 0 35))))
    (_ : env (.n 151) = QE.eval V inp (.or (.shl (.q (.W 0 0 36)) 25) (.shr (.q (.W 0 0 36)) 7)))
    (_ : env (.n 119) = QE.eval V inp (.q (.W 0 0 36)))
    (_ : V (.M2 0 0 35) = V (.M1 0 0 35) + V (.W 0 0 44))
    (_ : V (.M1 0 0 35) = V (.W 0 0 35) + sigma0 (V (.W 0 0 36))) :
    E.eval env (.add (.var (.n 103)) (.xor (.xor (.xor (.var (.n 151)) (.shl (.var (.n 119)) 14)) (.shr (.var (.n 119)) 18)) (.shr (.var (.n 119)) 3))) = V (.M2 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 36))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 36) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 37))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 37) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 38))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 39))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 40) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 35))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 35))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 35))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 35))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 34))) :
    E.eval env (.var (.n 1004)) = V (.KW 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 34))) :
    E.eval env (.var (.n 1005)) = V (.KW 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 34))) :
    E.eval env (.var (.n 1006)) = V (.KW 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core33_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 34))) :
    E.eval env (.var (.n 1007)) = V (.KW 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step33 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L33 inp env) (hm : HMem 128 inp env) :
    Inv1 L34 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 36 K33)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 0 (by decide)).trans (core33_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 1 (by decide)).trans (core33_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 2 (by decide)).trans (core33_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 3 (by decide)).trans (core33_14 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (qE_succI inp 0 0 (33) (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 4 (by decide)).trans (core33_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 5 (by decide)).trans (core33_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 6 (by decide)).trans (core33_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (qA_succI inp 0 0 (33) (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 7 (by decide)).trans (core33_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 8 (by decide)).trans (core33_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 16 (by decide)) (inv1_get hI 12 (by decide)) (qM2 inp 0 0 32) (qM1 inp 0 0 32))
  | 9, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 9 (by decide)).trans (core33_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 13 (by decide)) (qM2 inp 0 0 33) (qM1 inp 0 0 33))
  | 10, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 10 (by decide)).trans (core33_102 (qv inp) inp env (inv1_get hI 10 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 14 (by decide)) (qM2 inp 0 0 34) (qM1 inp 0 0 34))
  | 11, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 11 (by decide)).trans (core33_103 (qv inp) inp env (inv1_get hI 11 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 15 (by decide)) (qM2 inp 0 0 35) (qM1 inp 0 0 35))
  | 12, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 12 (by decide)).trans (core33_132 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 13 (by decide)).trans (core33_133 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 14 (by decide)).trans (core33_134 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 15 (by decide)).trans (core33_135 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 16 (by decide)).trans (core33_180 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 17 (by decide)).trans (core33_181 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 18 (by decide)).trans (core33_182 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 19 (by decide)).trans (core33_183 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 20 (by decide)).trans (core33_196 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 21 (by decide)).trans (core33_197 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 22 (by decide)).trans (core33_198 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 23 (by decide)).trans (core33_199 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 24 (by decide)).trans (core33_212 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 25 (by decide)).trans (core33_213 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 26 (by decide)).trans (core33_214 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 27 (by decide)).trans (core33_215 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 28 (by decide)).trans (core33_1000 (qv inp) inp env (inv1_get hI 32 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 29 (by decide)).trans (core33_1001 (qv inp) inp env (inv1_get hI 33 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 30 (by decide)).trans (core33_1002 (qv inp) inp env (inv1_get hI 34 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 31 (by decide)).trans (core33_1003 (qv inp) inp env (inv1_get hI 35 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 32 (by decide)).trans (core33_1004 (qv inp) inp env (inv1_get hI 36 (by decide)))
  | 33, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 33 (by decide)).trans (core33_1005 (qv inp) inp env (inv1_get hI 37 (by decide)))
  | 34, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 34 (by decide)).trans (core33_1006 (qv inp) inp env (inv1_get hI 38 (by decide)))
  | 35, _ => exact (slice_trees prog 4 _ _ 36 K33 K34 T33 slice33 env 35 (by decide)).trans (core33_1007 (qv inp) inp env (inv1_get hI 39 (by decide)))
  | _ + 36, hk => simp only [L34, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It
