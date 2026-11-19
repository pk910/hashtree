import Hashtree.Gen.WinSseX1LW.It.D40
import Hashtree.Gen.WinSseX1LW.It.D39
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice40 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 41 K40 K41 T40 = true := by
  decide +kernel

theorem core40_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (40)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (40)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (39)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (39)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (37))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (37))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (39))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (38))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (40))))
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40)))
    (_ : V (.E 0 0 (41)) = V (.A 0 0 (37)) + (V (.E 0 0 (37)) + Sigma1 (V (.E 0 0 (40))) + Ch (V (.E 0 0 (40))) (V (.E 0 0 (39))) (V (.E 0 0 (38))) + V (.KW 0 0 40)))
    (_ : V (.KW 0 0 40) = 2730485921#32 + V (.W 0 0 40)) :
    E.eval env (.add (.var (.n 12)) (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.const 2730485921) (.var (.n 196)))))) = V (.E 0 0 (41)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (38)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (38)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (39)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (39)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (38)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (38)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (37))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (39))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (38))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (40))))
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40)))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (40))))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (38))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (39))))
    (_ : V (.A 0 0 (41)) = (V (.E 0 0 (37)) + Sigma1 (V (.E 0 0 (40))) + Ch (V (.E 0 0 (40))) (V (.E 0 0 (39))) (V (.E 0 0 (38))) + V (.KW 0 0 40)) + (Sigma0 (V (.A 0 0 (40))) + Maj (V (.A 0 0 (40))) (V (.A 0 0 (39))) (V (.A 0 0 (38)))))
    (_ : V (.KW 0 0 40) = 2730485921#32 + V (.W 0 0 40)) :
    E.eval env (.add (.add (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.const 2730485921) (.var (.n 196))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 9) (.var (.n 0))) 11) (.var (.n 0))) 2)) (.or (.and (.or (.var (.n 0)) (.var (.n 14))) (.var (.n 6))) (.and (.var (.n 0)) (.var (.n 14))))) = V (.A 0 0 (41)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (40)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (40)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49)))
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40))) :
    E.eval env (.add (.var (.n 165)) (.var (.n 196))) = QE.eval V inp (.add (.q (.W 0 0 49)) (.q (.W 0 0 40))) := by
  simp_all only [E.eval, QE.eval]

theorem core40_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.add (.var (.n 166)) (.var (.n 197))) = QE.eval V inp (.add (.q (.W 0 0 50)) (.q (.W 0 0 41))) := by
  simp_all only [E.eval, QE.eval]

theorem core40_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.add (.var (.n 167)) (.var (.n 198))) = QE.eval V inp (.add (.q (.W 0 0 51)) (.q (.W 0 0 42))) := by
  simp_all only [E.eval, QE.eval]

theorem core40_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52)))
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.add (.var (.n 180)) (.var (.n 199))) = QE.eval V inp (.add (.q (.W 0 0 52)) (.q (.W 0 0 43))) := by
  simp_all only [E.eval, QE.eval]

theorem core40_116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.or (.shl (.var (.n 197)) 25) (.shr (.var (.n 197)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 41)) 25) (.shr (.q (.W 0 0 41)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core40_117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.or (.shl (.var (.n 198)) 25) (.shr (.var (.n 198)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 42)) 25) (.shr (.q (.W 0 0 42)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core40_118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.or (.shl (.var (.n 199)) 25) (.shr (.var (.n 199)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 43)) 25) (.shr (.q (.W 0 0 43)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core40_119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.or (.shl (.var (.n 212)) 25) (.shr (.var (.n 212)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 44)) 25) (.shr (.q (.W 0 0 44)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core40_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 48) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : V (.KW 0 0 43) = 3345764771#32 + V (.W 0 0 43)) :
    E.eval env (.add (.const 3345764771) (.var (.n 199))) = V (.KW 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : V (.KW 0 0 43) = 3345764771#32 + V (.W 0 0 43)) :
    E.eval env (.add (.const 3345764771) (.var (.n 199))) = V (.KW 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : V (.KW 0 0 43) = 3345764771#32 + V (.W 0 0 43)) :
    E.eval env (.add (.const 3345764771) (.var (.n 199))) = V (.KW 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : V (.KW 0 0 43) = 3345764771#32 + V (.W 0 0 43)) :
    E.eval env (.add (.const 3345764771) (.var (.n 199))) = V (.KW 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : V (.KW 0 0 42) = 3259730800#32 + V (.W 0 0 42)) :
    E.eval env (.add (.const 3259730800) (.var (.n 198))) = V (.KW 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : V (.KW 0 0 42) = 3259730800#32 + V (.W 0 0 42)) :
    E.eval env (.add (.const 3259730800) (.var (.n 198))) = V (.KW 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : V (.KW 0 0 42) = 3259730800#32 + V (.W 0 0 42)) :
    E.eval env (.add (.const 3259730800) (.var (.n 198))) = V (.KW 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : V (.KW 0 0 42) = 3259730800#32 + V (.W 0 0 42)) :
    E.eval env (.add (.const 3259730800) (.var (.n 198))) = V (.KW 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41)))
    (_ : V (.KW 0 0 41) = 2820302411#32 + V (.W 0 0 41)) :
    E.eval env (.add (.const 2820302411) (.var (.n 197))) = V (.KW 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41)))
    (_ : V (.KW 0 0 41) = 2820302411#32 + V (.W 0 0 41)) :
    E.eval env (.add (.const 2820302411) (.var (.n 197))) = V (.KW 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41)))
    (_ : V (.KW 0 0 41) = 2820302411#32 + V (.W 0 0 41)) :
    E.eval env (.add (.const 2820302411) (.var (.n 197))) = V (.KW 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core40_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41)))
    (_ : V (.KW 0 0 41) = 2820302411#32 + V (.W 0 0 41)) :
    E.eval env (.add (.const 2820302411) (.var (.n 197))) = V (.KW 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step40 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L40 inp env) (hm : HMem 128 inp env) :
    Inv1 L41 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 41 K40)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 0 (by decide)).trans (core40_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 1 (by decide)).trans (core40_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 2 (by decide)).trans (core40_12 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 16 (by decide)) (qE_succI inp 0 0 (40) (by decide)) ((qKW inp 0 0 40).trans (by rw [show Spec.K 40 = 2730485921#32 from by decide])))
  | 3, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 3 (by decide)).trans (core40_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 4 (by decide)).trans (core40_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 5 (by decide)).trans (core40_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 6 (by decide)).trans (core40_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 16 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 1 (by decide)) (qA_succI inp 0 0 (40) (by decide)) ((qKW inp 0 0 40).trans (by rw [show Spec.K 40 = 2730485921#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 7 (by decide)).trans (core40_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 8 (by decide)).trans (core40_100 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 16 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 9 (by decide)).trans (core40_101 (qv inp) inp env (inv1_get hI 10 (by decide)) (inv1_get hI 17 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 10 (by decide)).trans (core40_102 (qv inp) inp env (inv1_get hI 11 (by decide)) (inv1_get hI 18 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 11 (by decide)).trans (core40_103 (qv inp) inp env (inv1_get hI 12 (by decide)) (inv1_get hI 19 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 12 (by decide)).trans (core40_116 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 13 (by decide)).trans (core40_117 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 14 (by decide)).trans (core40_118 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 15 (by decide)).trans (core40_119 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 16 (by decide)).trans (core40_148 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 17 (by decide)).trans (core40_149 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 18 (by decide)).trans (core40_150 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 19 (by decide)).trans (core40_151 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 20 (by decide)).trans (core40_164 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 21 (by decide)).trans (core40_165 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 22 (by decide)).trans (core40_166 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 23 (by decide)).trans (core40_167 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 24 (by decide)).trans (core40_180 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 25 (by decide)).trans (core40_181 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 26 (by decide)).trans (core40_182 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 27 (by decide)).trans (core40_183 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 28 (by decide)).trans (core40_212 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 29 (by decide)).trans (core40_213 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 30 (by decide)).trans (core40_214 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 31 (by decide)).trans (core40_215 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 32 (by decide)).trans (core40_1000 (qv inp) inp env (inv1_get hI 19 (by decide)) ((qKW inp 0 0 43).trans (by rw [show Spec.K 43 = 3345764771#32 from by decide])))
  | 33, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 33 (by decide)).trans (core40_1001 (qv inp) inp env (inv1_get hI 19 (by decide)) ((qKW inp 0 0 43).trans (by rw [show Spec.K 43 = 3345764771#32 from by decide])))
  | 34, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 34 (by decide)).trans (core40_1002 (qv inp) inp env (inv1_get hI 19 (by decide)) ((qKW inp 0 0 43).trans (by rw [show Spec.K 43 = 3345764771#32 from by decide])))
  | 35, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 35 (by decide)).trans (core40_1003 (qv inp) inp env (inv1_get hI 19 (by decide)) ((qKW inp 0 0 43).trans (by rw [show Spec.K 43 = 3345764771#32 from by decide])))
  | 36, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 36 (by decide)).trans (core40_1004 (qv inp) inp env (inv1_get hI 18 (by decide)) ((qKW inp 0 0 42).trans (by rw [show Spec.K 42 = 3259730800#32 from by decide])))
  | 37, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 37 (by decide)).trans (core40_1005 (qv inp) inp env (inv1_get hI 18 (by decide)) ((qKW inp 0 0 42).trans (by rw [show Spec.K 42 = 3259730800#32 from by decide])))
  | 38, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 38 (by decide)).trans (core40_1006 (qv inp) inp env (inv1_get hI 18 (by decide)) ((qKW inp 0 0 42).trans (by rw [show Spec.K 42 = 3259730800#32 from by decide])))
  | 39, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 39 (by decide)).trans (core40_1007 (qv inp) inp env (inv1_get hI 18 (by decide)) ((qKW inp 0 0 42).trans (by rw [show Spec.K 42 = 3259730800#32 from by decide])))
  | 40, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 40 (by decide)).trans (core40_1008 (qv inp) inp env (inv1_get hI 17 (by decide)) ((qKW inp 0 0 41).trans (by rw [show Spec.K 41 = 2820302411#32 from by decide])))
  | 41, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 41 (by decide)).trans (core40_1009 (qv inp) inp env (inv1_get hI 17 (by decide)) ((qKW inp 0 0 41).trans (by rw [show Spec.K 41 = 2820302411#32 from by decide])))
  | 42, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 42 (by decide)).trans (core40_1010 (qv inp) inp env (inv1_get hI 17 (by decide)) ((qKW inp 0 0 41).trans (by rw [show Spec.K 41 = 2820302411#32 from by decide])))
  | 43, _ => exact (slice_trees prog 4 _ _ 41 K40 K41 T40 slice40 env 43 (by decide)).trans (core40_1011 (qv inp) inp env (inv1_get hI 17 (by decide)) ((qKW inp 0 0 41).trans (by rw [show Spec.K 41 = 2820302411#32 from by decide])))
  | _ + 44, hk => simp only [L41, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
