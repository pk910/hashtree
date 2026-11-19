import Hashtree.Gen.WinSseX1LW.It0.D32
import Hashtree.Gen.WinSseX1LW.It0.D31
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It0
open Hashtree.Gen.WinSseX1LW

theorem slice32 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 43 K32 K33 T32 = true := by
  decide +kernel

theorem core32_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (32)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (32)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (31)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (31)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (29))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (29))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (31))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (30))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (32))))
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 32)))
    (_ : V (.E 0 0 (33)) = V (.A 0 0 (29)) + (V (.E 0 0 (29)) + Sigma1 (V (.E 0 0 (32))) + Ch (V (.E 0 0 (32))) (V (.E 0 0 (31))) (V (.E 0 0 (30))) + V (.KW 0 0 32)))
    (_ : V (.KW 0 0 32) = 666307205#32 + V (.W 0 0 32)) :
    E.eval env (.add (.var (.n 12)) (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.const 666307205) (.var (.n 164)))))) = V (.E 0 0 (33)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (30)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (30)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (31)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (31)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (30)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (30)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (29))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (31))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (30))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (32))))
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 32)))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (32))))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (30))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (31))))
    (_ : V (.A 0 0 (33)) = (V (.E 0 0 (29)) + Sigma1 (V (.E 0 0 (32))) + Ch (V (.E 0 0 (32))) (V (.E 0 0 (31))) (V (.E 0 0 (30))) + V (.KW 0 0 32)) + (Sigma0 (V (.A 0 0 (32))) + Maj (V (.A 0 0 (32))) (V (.A 0 0 (31))) (V (.A 0 0 (30)))))
    (_ : V (.KW 0 0 32) = 666307205#32 + V (.W 0 0 32)) :
    E.eval env (.add (.add (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.const 666307205) (.var (.n 164))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 9) (.var (.n 0))) 11) (.var (.n 0))) 2)) (.or (.and (.or (.var (.n 0)) (.var (.n 14))) (.var (.n 6))) (.and (.var (.n 0)) (.var (.n 14))))) = V (.A 0 0 (33)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (32)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (32)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41)))
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 32))) :
    E.eval env (.add (.var (.n 197)) (.var (.n 164))) = QE.eval V inp (.add (.q (.W 0 0 41)) (.q (.W 0 0 32))) := by
  simp_all only [E.eval, QE.eval]

theorem core32_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42)))
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33))) :
    E.eval env (.add (.var (.n 198)) (.var (.n 165))) = QE.eval V inp (.add (.q (.W 0 0 42)) (.q (.W 0 0 33))) := by
  simp_all only [E.eval, QE.eval]

theorem core32_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43)))
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34))) :
    E.eval env (.add (.var (.n 199)) (.var (.n 166))) = QE.eval V inp (.add (.q (.W 0 0 43)) (.q (.W 0 0 34))) := by
  simp_all only [E.eval, QE.eval]

theorem core32_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44)))
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35))) :
    E.eval env (.add (.var (.n 212)) (.var (.n 167))) = QE.eval V inp (.add (.q (.W 0 0 44)) (.q (.W 0 0 35))) := by
  simp_all only [E.eval, QE.eval]

theorem core32_116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33))) :
    E.eval env (.or (.shl (.var (.n 165)) 25) (.shr (.var (.n 165)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 33)) 25) (.shr (.q (.W 0 0 33)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core32_117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34))) :
    E.eval env (.or (.shl (.var (.n 166)) 25) (.shr (.var (.n 166)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 34)) 25) (.shr (.q (.W 0 0 34)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core32_118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35))) :
    E.eval env (.or (.shl (.var (.n 167)) 25) (.shr (.var (.n 167)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 35)) 25) (.shr (.q (.W 0 0 35)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core32_119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 36))) :
    E.eval env (.or (.shl (.var (.n 180)) 25) (.shr (.var (.n 180)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 36)) 25) (.shr (.q (.W 0 0 36)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core32_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 36))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 36) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 36))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 36) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 37))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 37) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 38))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 39))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 40) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : V (.KW 0 0 35) = 1396182291#32 + V (.W 0 0 35)) :
    E.eval env (.add (.const 1396182291) (.var (.n 167))) = V (.KW 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : V (.KW 0 0 35) = 1396182291#32 + V (.W 0 0 35)) :
    E.eval env (.add (.const 1396182291) (.var (.n 167))) = V (.KW 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : V (.KW 0 0 35) = 1396182291#32 + V (.W 0 0 35)) :
    E.eval env (.add (.const 1396182291) (.var (.n 167))) = V (.KW 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35)))
    (_ : V (.KW 0 0 35) = 1396182291#32 + V (.W 0 0 35)) :
    E.eval env (.add (.const 1396182291) (.var (.n 167))) = V (.KW 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : V (.KW 0 0 34) = 1294757372#32 + V (.W 0 0 34)) :
    E.eval env (.add (.const 1294757372) (.var (.n 166))) = V (.KW 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : V (.KW 0 0 34) = 1294757372#32 + V (.W 0 0 34)) :
    E.eval env (.add (.const 1294757372) (.var (.n 166))) = V (.KW 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : V (.KW 0 0 34) = 1294757372#32 + V (.W 0 0 34)) :
    E.eval env (.add (.const 1294757372) (.var (.n 166))) = V (.KW 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34)))
    (_ : V (.KW 0 0 34) = 1294757372#32 + V (.W 0 0 34)) :
    E.eval env (.add (.const 1294757372) (.var (.n 166))) = V (.KW 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33)))
    (_ : V (.KW 0 0 33) = 773529912#32 + V (.W 0 0 33)) :
    E.eval env (.add (.const 773529912) (.var (.n 165))) = V (.KW 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33)))
    (_ : V (.KW 0 0 33) = 773529912#32 + V (.W 0 0 33)) :
    E.eval env (.add (.const 773529912) (.var (.n 165))) = V (.KW 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33)))
    (_ : V (.KW 0 0 33) = 773529912#32 + V (.W 0 0 33)) :
    E.eval env (.add (.const 773529912) (.var (.n 165))) = V (.KW 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core32_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33)))
    (_ : V (.KW 0 0 33) = 773529912#32 + V (.W 0 0 33)) :
    E.eval env (.add (.const 773529912) (.var (.n 165))) = V (.KW 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step32 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L32 inp env) (hm : HMem 128 inp env) :
    Inv1 L33 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 43 K32)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 0 (by decide)).trans (core32_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 1 (by decide)).trans (core32_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 2 (by decide)).trans (core32_12 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 8 (by decide)) (qE_succI inp 0 0 (32) (by decide)) ((qKW inp 0 0 32).trans (by rw [show Spec.K 32 = 666307205#32 from by decide])))
  | 3, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 3 (by decide)).trans (core32_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 4 (by decide)).trans (core32_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 5 (by decide)).trans (core32_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 6 (by decide)).trans (core32_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 1 (by decide)) (qA_succI inp 0 0 (32) (by decide)) ((qKW inp 0 0 32).trans (by rw [show Spec.K 32 = 666307205#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 7 (by decide)).trans (core32_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 8 (by decide)).trans (core32_100 (qv inp) inp env (inv1_get hI 17 (by decide)) (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 9 (by decide)).trans (core32_101 (qv inp) inp env (inv1_get hI 18 (by decide)) (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 10 (by decide)).trans (core32_102 (qv inp) inp env (inv1_get hI 19 (by decide)) (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 11 (by decide)).trans (core32_103 (qv inp) inp env (inv1_get hI 20 (by decide)) (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 12 (by decide)).trans (core32_116 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 13 (by decide)).trans (core32_117 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 14 (by decide)).trans (core32_118 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 15 (by decide)).trans (core32_119 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 16 (by decide)).trans (core32_148 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 17 (by decide)).trans (core32_149 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 18 (by decide)).trans (core32_150 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 19 (by decide)).trans (core32_151 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 20 (by decide)).trans (core32_180 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 21 (by decide)).trans (core32_181 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 22 (by decide)).trans (core32_182 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 23 (by decide)).trans (core32_183 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 24 (by decide)).trans (core32_196 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 25 (by decide)).trans (core32_197 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 26 (by decide)).trans (core32_198 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 27 (by decide)).trans (core32_199 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 28 (by decide)).trans (core32_212 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 29 (by decide)).trans (core32_213 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 30 (by decide)).trans (core32_214 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 31 (by decide)).trans (core32_215 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 32 (by decide)).trans (core32_1000 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 35).trans (by rw [show Spec.K 35 = 1396182291#32 from by decide])))
  | 33, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 33 (by decide)).trans (core32_1001 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 35).trans (by rw [show Spec.K 35 = 1396182291#32 from by decide])))
  | 34, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 34 (by decide)).trans (core32_1002 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 35).trans (by rw [show Spec.K 35 = 1396182291#32 from by decide])))
  | 35, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 35 (by decide)).trans (core32_1003 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 35).trans (by rw [show Spec.K 35 = 1396182291#32 from by decide])))
  | 36, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 36 (by decide)).trans (core32_1004 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 34).trans (by rw [show Spec.K 34 = 1294757372#32 from by decide])))
  | 37, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 37 (by decide)).trans (core32_1005 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 34).trans (by rw [show Spec.K 34 = 1294757372#32 from by decide])))
  | 38, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 38 (by decide)).trans (core32_1006 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 34).trans (by rw [show Spec.K 34 = 1294757372#32 from by decide])))
  | 39, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 39 (by decide)).trans (core32_1007 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 34).trans (by rw [show Spec.K 34 = 1294757372#32 from by decide])))
  | 40, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 40 (by decide)).trans (core32_1008 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 33).trans (by rw [show Spec.K 33 = 773529912#32 from by decide])))
  | 41, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 41 (by decide)).trans (core32_1009 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 33).trans (by rw [show Spec.K 33 = 773529912#32 from by decide])))
  | 42, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 42 (by decide)).trans (core32_1010 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 33).trans (by rw [show Spec.K 33 = 773529912#32 from by decide])))
  | 43, _ => exact (slice_trees prog 4 _ _ 43 K32 K33 T32 slice32 env 43 (by decide)).trans (core32_1011 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 33).trans (by rw [show Spec.K 33 = 773529912#32 from by decide])))
  | _ + 44, hk => simp only [L33, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It0
