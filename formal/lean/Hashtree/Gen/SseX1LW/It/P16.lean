import Hashtree.Gen.SseX1LW.It.D16
import Hashtree.Gen.SseX1LW.It.D15
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It
open Hashtree.Gen.SseX1LW

theorem slice16 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 43 K16 K17 T16 = true := by
  decide +kernel

theorem core16_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (16)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (16)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 0 (14)))) :
    E.eval env (.var (.n 2)) = V (.A 0 0 (14)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (15)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (15)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 0 (13))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (13))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (15))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (14))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (16))))
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16)))
    (_ : V (.E 0 0 (17)) = V (.A 0 0 (13)) + (V (.E 0 0 (13)) + Sigma1 (V (.E 0 0 (16))) + Ch (V (.E 0 0 (16))) (V (.E 0 0 (15))) (V (.E 0 0 (14))) + V (.KW 0 0 16)))
    (_ : V (.KW 0 0 16) = 3835390401#32 + V (.W 0 0 16)) :
    E.eval env (.add (.var (.n 16)) (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.const 3835390401) (.var (.n 164)))))) = V (.E 0 0 (17)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (15)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (15)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (14)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (14)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (13))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (15))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (14))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (16))))
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16)))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (16))))
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 0 (14))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (15))))
    (_ : V (.A 0 0 (17)) = (V (.E 0 0 (13)) + Sigma1 (V (.E 0 0 (16))) + Ch (V (.E 0 0 (16))) (V (.E 0 0 (15))) (V (.E 0 0 (14))) + V (.KW 0 0 16)) + (Sigma0 (V (.A 0 0 (16))) + Maj (V (.A 0 0 (16))) (V (.A 0 0 (15))) (V (.A 0 0 (14)))))
    (_ : V (.KW 0 0 16) = 3835390401#32 + V (.W 0 0 16)) :
    E.eval env (.add (.add (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.const 3835390401) (.var (.n 164))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 9) (.var (.n 0))) 11) (.var (.n 0))) 2)) (.or (.and (.or (.var (.n 0)) (.var (.n 2))) (.var (.n 6))) (.and (.var (.n 0)) (.var (.n 2))))) = V (.A 0 0 (17)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (16)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (16)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 25)))
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16))) :
    E.eval env (.add (.var (.n 197)) (.var (.n 164))) = QE.eval V inp (.add (.q (.W 0 0 25)) (.q (.W 0 0 16))) := by
  simp_all only [E.eval, QE.eval]

theorem core16_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 26)))
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.add (.var (.n 198)) (.var (.n 165))) = QE.eval V inp (.add (.q (.W 0 0 26)) (.q (.W 0 0 17))) := by
  simp_all only [E.eval, QE.eval]

theorem core16_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 27)))
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.add (.var (.n 199)) (.var (.n 166))) = QE.eval V inp (.add (.q (.W 0 0 27)) (.q (.W 0 0 18))) := by
  simp_all only [E.eval, QE.eval]

theorem core16_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 28)))
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.add (.var (.n 212)) (.var (.n 167))) = QE.eval V inp (.add (.q (.W 0 0 28)) (.q (.W 0 0 19))) := by
  simp_all only [E.eval, QE.eval]

theorem core16_116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.or (.shl (.var (.n 165)) 25) (.shr (.var (.n 165)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 17)) 25) (.shr (.q (.W 0 0 17)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core16_117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.or (.shl (.var (.n 166)) 25) (.shr (.var (.n 166)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 18)) 25) (.shr (.q (.W 0 0 18)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core16_118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.or (.shl (.var (.n 167)) 25) (.shr (.var (.n 167)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 19)) 25) (.shr (.q (.W 0 0 19)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core16_119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.or (.shl (.var (.n 180)) 25) (.shr (.var (.n 180)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 20)) 25) (.shr (.q (.W 0 0 20)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core16_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 20) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 20) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 24))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 24) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 25))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 25) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 26))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 26) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 27))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 27) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 28))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 28) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 29))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 29) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 30))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 31))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19)))
    (_ : V (.KW 0 0 19) = 604807628#32 + V (.W 0 0 19)) :
    E.eval env (.add (.const 604807628) (.var (.n 167))) = V (.KW 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19)))
    (_ : V (.KW 0 0 19) = 604807628#32 + V (.W 0 0 19)) :
    E.eval env (.add (.const 604807628) (.var (.n 167))) = V (.KW 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19)))
    (_ : V (.KW 0 0 19) = 604807628#32 + V (.W 0 0 19)) :
    E.eval env (.add (.const 604807628) (.var (.n 167))) = V (.KW 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19)))
    (_ : V (.KW 0 0 19) = 604807628#32 + V (.W 0 0 19)) :
    E.eval env (.add (.const 604807628) (.var (.n 167))) = V (.KW 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18)))
    (_ : V (.KW 0 0 18) = 264347078#32 + V (.W 0 0 18)) :
    E.eval env (.add (.const 264347078) (.var (.n 166))) = V (.KW 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18)))
    (_ : V (.KW 0 0 18) = 264347078#32 + V (.W 0 0 18)) :
    E.eval env (.add (.const 264347078) (.var (.n 166))) = V (.KW 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18)))
    (_ : V (.KW 0 0 18) = 264347078#32 + V (.W 0 0 18)) :
    E.eval env (.add (.const 264347078) (.var (.n 166))) = V (.KW 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18)))
    (_ : V (.KW 0 0 18) = 264347078#32 + V (.W 0 0 18)) :
    E.eval env (.add (.const 264347078) (.var (.n 166))) = V (.KW 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17)))
    (_ : V (.KW 0 0 17) = 4022224774#32 + V (.W 0 0 17)) :
    E.eval env (.add (.const 4022224774) (.var (.n 165))) = V (.KW 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17)))
    (_ : V (.KW 0 0 17) = 4022224774#32 + V (.W 0 0 17)) :
    E.eval env (.add (.const 4022224774) (.var (.n 165))) = V (.KW 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17)))
    (_ : V (.KW 0 0 17) = 4022224774#32 + V (.W 0 0 17)) :
    E.eval env (.add (.const 4022224774) (.var (.n 165))) = V (.KW 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core16_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17)))
    (_ : V (.KW 0 0 17) = 4022224774#32 + V (.W 0 0 17)) :
    E.eval env (.add (.const 4022224774) (.var (.n 165))) = V (.KW 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step16 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L16 inp env) (hm : HMem 128 inp env) :
    Inv1 L17 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 43 K16)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 0 (by decide)).trans (core16_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 1 (by decide)).trans (core16_2 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 2 (by decide)).trans (core16_6 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 3 (by decide)).trans (core16_16 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 8 (by decide)) (qE_succI inp 0 0 (16) (by decide)) ((qKW inp 0 0 16).trans (by rw [show Spec.K 16 = 3835390401#32 from by decide])))
  | 4, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 4 (by decide)).trans (core16_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 5 (by decide)).trans (core16_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 6 (by decide)).trans (core16_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 2 (by decide)) (qA_succI inp 0 0 (16) (by decide)) ((qKW inp 0 0 16).trans (by rw [show Spec.K 16 = 3835390401#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 7 (by decide)).trans (core16_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 8 (by decide)).trans (core16_100 (qv inp) inp env (inv1_get hI 17 (by decide)) (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 9 (by decide)).trans (core16_101 (qv inp) inp env (inv1_get hI 18 (by decide)) (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 10 (by decide)).trans (core16_102 (qv inp) inp env (inv1_get hI 19 (by decide)) (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 11 (by decide)).trans (core16_103 (qv inp) inp env (inv1_get hI 20 (by decide)) (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 12 (by decide)).trans (core16_116 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 13 (by decide)).trans (core16_117 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 14 (by decide)).trans (core16_118 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 15 (by decide)).trans (core16_119 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 16 (by decide)).trans (core16_148 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 17 (by decide)).trans (core16_149 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 18 (by decide)).trans (core16_150 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 19 (by decide)).trans (core16_151 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 20 (by decide)).trans (core16_180 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 21 (by decide)).trans (core16_181 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 22 (by decide)).trans (core16_182 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 23 (by decide)).trans (core16_183 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 24 (by decide)).trans (core16_196 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 25 (by decide)).trans (core16_197 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 26 (by decide)).trans (core16_198 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 27 (by decide)).trans (core16_199 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 28 (by decide)).trans (core16_212 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 29 (by decide)).trans (core16_213 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 30 (by decide)).trans (core16_214 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 31 (by decide)).trans (core16_215 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 32 (by decide)).trans (core16_1000 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 19).trans (by rw [show Spec.K 19 = 604807628#32 from by decide])))
  | 33, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 33 (by decide)).trans (core16_1001 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 19).trans (by rw [show Spec.K 19 = 604807628#32 from by decide])))
  | 34, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 34 (by decide)).trans (core16_1002 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 19).trans (by rw [show Spec.K 19 = 604807628#32 from by decide])))
  | 35, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 35 (by decide)).trans (core16_1003 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 19).trans (by rw [show Spec.K 19 = 604807628#32 from by decide])))
  | 36, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 36 (by decide)).trans (core16_1004 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 18).trans (by rw [show Spec.K 18 = 264347078#32 from by decide])))
  | 37, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 37 (by decide)).trans (core16_1005 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 18).trans (by rw [show Spec.K 18 = 264347078#32 from by decide])))
  | 38, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 38 (by decide)).trans (core16_1006 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 18).trans (by rw [show Spec.K 18 = 264347078#32 from by decide])))
  | 39, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 39 (by decide)).trans (core16_1007 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 18).trans (by rw [show Spec.K 18 = 264347078#32 from by decide])))
  | 40, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 40 (by decide)).trans (core16_1008 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 17).trans (by rw [show Spec.K 17 = 4022224774#32 from by decide])))
  | 41, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 41 (by decide)).trans (core16_1009 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 17).trans (by rw [show Spec.K 17 = 4022224774#32 from by decide])))
  | 42, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 42 (by decide)).trans (core16_1010 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 17).trans (by rw [show Spec.K 17 = 4022224774#32 from by decide])))
  | 43, _ => exact (slice_trees prog 4 _ _ 43 K16 K17 T16 slice16 env 43 (by decide)).trans (core16_1011 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 17).trans (by rw [show Spec.K 17 = 4022224774#32 from by decide])))
  | _ + 44, hk => simp only [L17, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It
