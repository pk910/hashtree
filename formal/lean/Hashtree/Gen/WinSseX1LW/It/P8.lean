import Hashtree.Gen.WinSseX1LW.It.D8
import Hashtree.Gen.WinSseX1LW.It.D7
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice8 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 41 K8 K9 T8 = true := by
  decide +kernel

theorem core8_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (8)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (8)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (7)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (7)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (5))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (5))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (7))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (6))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (8))))
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8)))
    (_ : V (.E 0 0 (9)) = V (.A 0 0 (5)) + (V (.E 0 0 (5)) + Sigma1 (V (.E 0 0 (8))) + Ch (V (.E 0 0 (8))) (V (.E 0 0 (7))) (V (.E 0 0 (6))) + V (.KW 0 0 8)))
    (_ : V (.KW 0 0 8) = 3624381080#32 + V (.W 0 0 8)) :
    E.eval env (.add (.var (.n 12)) (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.const 3624381080) (.var (.n 196)))))) = V (.E 0 0 (9)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (6)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (6)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (7)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (7)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (6)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (6)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (5))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (7))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (6))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (8))))
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8)))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (8))))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (6))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (7))))
    (_ : V (.A 0 0 (9)) = (V (.E 0 0 (5)) + Sigma1 (V (.E 0 0 (8))) + Ch (V (.E 0 0 (8))) (V (.E 0 0 (7))) (V (.E 0 0 (6))) + V (.KW 0 0 8)) + (Sigma0 (V (.A 0 0 (8))) + Maj (V (.A 0 0 (8))) (V (.A 0 0 (7))) (V (.A 0 0 (6)))))
    (_ : V (.KW 0 0 8) = 3624381080#32 + V (.W 0 0 8)) :
    E.eval env (.add (.add (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.const 3624381080) (.var (.n 196))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 9) (.var (.n 0))) 11) (.var (.n 0))) 2)) (.or (.and (.or (.var (.n 0)) (.var (.n 14))) (.var (.n 6))) (.and (.var (.n 0)) (.var (.n 14))))) = V (.A 0 0 (9)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (8)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (8)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17)))
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8))) :
    E.eval env (.add (.var (.n 165)) (.var (.n 196))) = QE.eval V inp (.add (.q (.W 0 0 17)) (.q (.W 0 0 8))) := by
  simp_all only [E.eval, QE.eval]

theorem core8_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18)))
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9))) :
    E.eval env (.add (.var (.n 166)) (.var (.n 197))) = QE.eval V inp (.add (.q (.W 0 0 18)) (.q (.W 0 0 9))) := by
  simp_all only [E.eval, QE.eval]

theorem core8_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19)))
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10))) :
    E.eval env (.add (.var (.n 167)) (.var (.n 198))) = QE.eval V inp (.add (.q (.W 0 0 19)) (.q (.W 0 0 10))) := by
  simp_all only [E.eval, QE.eval]

theorem core8_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20)))
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11))) :
    E.eval env (.add (.var (.n 180)) (.var (.n 199))) = QE.eval V inp (.add (.q (.W 0 0 20)) (.q (.W 0 0 11))) := by
  simp_all only [E.eval, QE.eval]

theorem core8_116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9))) :
    E.eval env (.or (.shl (.var (.n 197)) 25) (.shr (.var (.n 197)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 9)) 25) (.shr (.q (.W 0 0 9)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core8_117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10))) :
    E.eval env (.or (.shl (.var (.n 198)) 25) (.shr (.var (.n 198)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 10)) 25) (.shr (.q (.W 0 0 10)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core8_118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11))) :
    E.eval env (.or (.shl (.var (.n 199)) 25) (.shr (.var (.n 199)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 11)) 25) (.shr (.q (.W 0 0 11)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core8_119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.or (.shl (.var (.n 212)) 25) (.shr (.var (.n 212)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 12)) 25) (.shr (.q (.W 0 0 12)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core8_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 12) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 20) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 12) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 13))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 13) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11)))
    (_ : V (.KW 0 0 11) = 1426881987#32 + V (.W 0 0 11)) :
    E.eval env (.add (.const 1426881987) (.var (.n 199))) = V (.KW 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11)))
    (_ : V (.KW 0 0 11) = 1426881987#32 + V (.W 0 0 11)) :
    E.eval env (.add (.const 1426881987) (.var (.n 199))) = V (.KW 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11)))
    (_ : V (.KW 0 0 11) = 1426881987#32 + V (.W 0 0 11)) :
    E.eval env (.add (.const 1426881987) (.var (.n 199))) = V (.KW 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11)))
    (_ : V (.KW 0 0 11) = 1426881987#32 + V (.W 0 0 11)) :
    E.eval env (.add (.const 1426881987) (.var (.n 199))) = V (.KW 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10)))
    (_ : V (.KW 0 0 10) = 607225278#32 + V (.W 0 0 10)) :
    E.eval env (.add (.const 607225278) (.var (.n 198))) = V (.KW 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10)))
    (_ : V (.KW 0 0 10) = 607225278#32 + V (.W 0 0 10)) :
    E.eval env (.add (.const 607225278) (.var (.n 198))) = V (.KW 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10)))
    (_ : V (.KW 0 0 10) = 607225278#32 + V (.W 0 0 10)) :
    E.eval env (.add (.const 607225278) (.var (.n 198))) = V (.KW 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10)))
    (_ : V (.KW 0 0 10) = 607225278#32 + V (.W 0 0 10)) :
    E.eval env (.add (.const 607225278) (.var (.n 198))) = V (.KW 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9)))
    (_ : V (.KW 0 0 9) = 310598401#32 + V (.W 0 0 9)) :
    E.eval env (.add (.const 310598401) (.var (.n 197))) = V (.KW 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9)))
    (_ : V (.KW 0 0 9) = 310598401#32 + V (.W 0 0 9)) :
    E.eval env (.add (.const 310598401) (.var (.n 197))) = V (.KW 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9)))
    (_ : V (.KW 0 0 9) = 310598401#32 + V (.W 0 0 9)) :
    E.eval env (.add (.const 310598401) (.var (.n 197))) = V (.KW 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core8_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9)))
    (_ : V (.KW 0 0 9) = 310598401#32 + V (.W 0 0 9)) :
    E.eval env (.add (.const 310598401) (.var (.n 197))) = V (.KW 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step8 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L8 inp env) (hm : HMem 128 inp env) :
    Inv1 L9 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 41 K8)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 0 (by decide)).trans (core8_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 1 (by decide)).trans (core8_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 2 (by decide)).trans (core8_12 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 16 (by decide)) (qE_succI inp 0 0 (8) (by decide)) ((qKW inp 0 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])))
  | 3, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 3 (by decide)).trans (core8_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 4 (by decide)).trans (core8_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 5 (by decide)).trans (core8_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 6 (by decide)).trans (core8_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 16 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 1 (by decide)) (qA_succI inp 0 0 (8) (by decide)) ((qKW inp 0 0 8).trans (by rw [show Spec.K 8 = 3624381080#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 7 (by decide)).trans (core8_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 8 (by decide)).trans (core8_100 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 16 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 9 (by decide)).trans (core8_101 (qv inp) inp env (inv1_get hI 10 (by decide)) (inv1_get hI 17 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 10 (by decide)).trans (core8_102 (qv inp) inp env (inv1_get hI 11 (by decide)) (inv1_get hI 18 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 11 (by decide)).trans (core8_103 (qv inp) inp env (inv1_get hI 12 (by decide)) (inv1_get hI 19 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 12 (by decide)).trans (core8_116 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 13 (by decide)).trans (core8_117 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 14 (by decide)).trans (core8_118 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 15 (by decide)).trans (core8_119 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 16 (by decide)).trans (core8_148 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 17 (by decide)).trans (core8_149 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 18 (by decide)).trans (core8_150 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 19 (by decide)).trans (core8_151 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 20 (by decide)).trans (core8_164 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 21 (by decide)).trans (core8_165 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 22 (by decide)).trans (core8_166 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 23 (by decide)).trans (core8_167 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 24 (by decide)).trans (core8_180 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 25 (by decide)).trans (core8_181 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 26 (by decide)).trans (core8_182 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 27 (by decide)).trans (core8_183 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 28 (by decide)).trans (core8_212 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 29 (by decide)).trans (core8_213 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 30 (by decide)).trans (core8_214 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 31 (by decide)).trans (core8_215 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 32 (by decide)).trans (core8_1000 (qv inp) inp env (inv1_get hI 19 (by decide)) ((qKW inp 0 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide])))
  | 33, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 33 (by decide)).trans (core8_1001 (qv inp) inp env (inv1_get hI 19 (by decide)) ((qKW inp 0 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide])))
  | 34, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 34 (by decide)).trans (core8_1002 (qv inp) inp env (inv1_get hI 19 (by decide)) ((qKW inp 0 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide])))
  | 35, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 35 (by decide)).trans (core8_1003 (qv inp) inp env (inv1_get hI 19 (by decide)) ((qKW inp 0 0 11).trans (by rw [show Spec.K 11 = 1426881987#32 from by decide])))
  | 36, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 36 (by decide)).trans (core8_1004 (qv inp) inp env (inv1_get hI 18 (by decide)) ((qKW inp 0 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide])))
  | 37, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 37 (by decide)).trans (core8_1005 (qv inp) inp env (inv1_get hI 18 (by decide)) ((qKW inp 0 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide])))
  | 38, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 38 (by decide)).trans (core8_1006 (qv inp) inp env (inv1_get hI 18 (by decide)) ((qKW inp 0 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide])))
  | 39, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 39 (by decide)).trans (core8_1007 (qv inp) inp env (inv1_get hI 18 (by decide)) ((qKW inp 0 0 10).trans (by rw [show Spec.K 10 = 607225278#32 from by decide])))
  | 40, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 40 (by decide)).trans (core8_1008 (qv inp) inp env (inv1_get hI 17 (by decide)) ((qKW inp 0 0 9).trans (by rw [show Spec.K 9 = 310598401#32 from by decide])))
  | 41, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 41 (by decide)).trans (core8_1009 (qv inp) inp env (inv1_get hI 17 (by decide)) ((qKW inp 0 0 9).trans (by rw [show Spec.K 9 = 310598401#32 from by decide])))
  | 42, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 42 (by decide)).trans (core8_1010 (qv inp) inp env (inv1_get hI 17 (by decide)) ((qKW inp 0 0 9).trans (by rw [show Spec.K 9 = 310598401#32 from by decide])))
  | 43, _ => exact (slice_trees prog 4 _ _ 41 K8 K9 T8 slice8 env 43 (by decide)).trans (core8_1011 (qv inp) inp env (inv1_get hI 17 (by decide)) ((qKW inp 0 0 9).trans (by rw [show Spec.K 9 = 310598401#32 from by decide])))
  | _ + 44, hk => simp only [L9, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
