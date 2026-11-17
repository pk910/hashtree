import Hashtree.Gen.WinSseX1LW.It.D4
import Hashtree.Gen.WinSseX1LW.It.D3
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice4 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 41 K4 K5 T4 = true := by
  decide +kernel

theorem core4_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (4)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (4)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (3)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (1))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (3))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (2))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (4))))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 4)))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (4))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (2))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (3))))
    (_ : V (.A 0 0 (5)) = (V (.E 0 0 (1)) + Sigma1 (V (.E 0 0 (4))) + Ch (V (.E 0 0 (4))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) + V (.KW 0 0 4)) + (Sigma0 (V (.A 0 0 (4))) + Maj (V (.A 0 0 (4))) (V (.A 0 0 (3))) (V (.A 0 0 (2)))))
    (_ : V (.KW 0 0 4) = 961987163#32 + V (.W 0 0 4)) :
    E.eval env (.add (.add (.add (.var (.n 12)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 14))) (.var (.n 0))) (.var (.n 14))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 14) (.var (.n 0))) 5) (.var (.n 0))) 6)) (.add (.const 961987163) (.var (.n 180))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 9) (.var (.n 24))) 11) (.var (.n 24))) 2)) (.or (.and (.or (.var (.n 24)) (.var (.n 20))) (.var (.n 18))) (.and (.var (.n 24)) (.var (.n 20))))) = V (.A 0 0 (5)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (2)))) :
    E.eval env (.var (.n 14)) = V (.E 0 0 (2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (3)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (2)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (1))))
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (1))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (3))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (2))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (4))))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 4)))
    (_ : V (.E 0 0 (5)) = V (.A 0 0 (1)) + (V (.E 0 0 (1)) + Sigma1 (V (.E 0 0 (4))) + Ch (V (.E 0 0 (4))) (V (.E 0 0 (3))) (V (.E 0 0 (2))) + V (.KW 0 0 4)))
    (_ : V (.KW 0 0 4) = 961987163#32 + V (.W 0 0 4)) :
    E.eval env (.add (.var (.n 22)) (.add (.var (.n 12)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 14))) (.var (.n 0))) (.var (.n 14))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 14) (.var (.n 0))) 5) (.var (.n 0))) 6)) (.add (.const 961987163) (.var (.n 180)))))) = V (.E 0 0 (5)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (4)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (4)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 13)))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 4))) :
    E.eval env (.add (.var (.n 213)) (.var (.n 180))) = QE.eval V inp (.add (.q (.W 0 0 13)) (.q (.W 0 0 4))) := by
  simp_all only [E.eval, QE.eval]

theorem core4_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14)))
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5))) :
    E.eval env (.add (.var (.n 214)) (.var (.n 181))) = QE.eval V inp (.add (.q (.W 0 0 14)) (.q (.W 0 0 5))) := by
  simp_all only [E.eval, QE.eval]

theorem core4_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15)))
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6))) :
    E.eval env (.add (.var (.n 215)) (.var (.n 182))) = QE.eval V inp (.add (.q (.W 0 0 15)) (.q (.W 0 0 6))) := by
  simp_all only [E.eval, QE.eval]

theorem core4_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16)))
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7))) :
    E.eval env (.add (.var (.n 164)) (.var (.n 183))) = QE.eval V inp (.add (.q (.W 0 0 16)) (.q (.W 0 0 7))) := by
  simp_all only [E.eval, QE.eval]

theorem core4_116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5))) :
    E.eval env (.or (.shl (.var (.n 181)) 25) (.shr (.var (.n 181)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 5)) 25) (.shr (.q (.W 0 0 5)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core4_117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6))) :
    E.eval env (.or (.shl (.var (.n 182)) 25) (.shr (.var (.n 182)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 6)) 25) (.shr (.q (.W 0 0 6)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core4_118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7))) :
    E.eval env (.or (.shl (.var (.n 183)) 25) (.shr (.var (.n 183)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 7)) 25) (.shr (.q (.W 0 0 7)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core4_119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8))) :
    E.eval env (.or (.shl (.var (.n 196)) 25) (.shr (.var (.n 196)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 8)) 25) (.shr (.q (.W 0 0 8)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core4_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 8) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 8) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 12) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 13))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 13) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7)))
    (_ : V (.KW 0 0 7) = 2870763221#32 + V (.W 0 0 7)) :
    E.eval env (.add (.const 2870763221) (.var (.n 183))) = V (.KW 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7)))
    (_ : V (.KW 0 0 7) = 2870763221#32 + V (.W 0 0 7)) :
    E.eval env (.add (.const 2870763221) (.var (.n 183))) = V (.KW 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7)))
    (_ : V (.KW 0 0 7) = 2870763221#32 + V (.W 0 0 7)) :
    E.eval env (.add (.const 2870763221) (.var (.n 183))) = V (.KW 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7)))
    (_ : V (.KW 0 0 7) = 2870763221#32 + V (.W 0 0 7)) :
    E.eval env (.add (.const 2870763221) (.var (.n 183))) = V (.KW 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6)))
    (_ : V (.KW 0 0 6) = 2453635748#32 + V (.W 0 0 6)) :
    E.eval env (.add (.const 2453635748) (.var (.n 182))) = V (.KW 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6)))
    (_ : V (.KW 0 0 6) = 2453635748#32 + V (.W 0 0 6)) :
    E.eval env (.add (.const 2453635748) (.var (.n 182))) = V (.KW 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6)))
    (_ : V (.KW 0 0 6) = 2453635748#32 + V (.W 0 0 6)) :
    E.eval env (.add (.const 2453635748) (.var (.n 182))) = V (.KW 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6)))
    (_ : V (.KW 0 0 6) = 2453635748#32 + V (.W 0 0 6)) :
    E.eval env (.add (.const 2453635748) (.var (.n 182))) = V (.KW 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5)))
    (_ : V (.KW 0 0 5) = 1508970993#32 + V (.W 0 0 5)) :
    E.eval env (.add (.const 1508970993) (.var (.n 181))) = V (.KW 0 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5)))
    (_ : V (.KW 0 0 5) = 1508970993#32 + V (.W 0 0 5)) :
    E.eval env (.add (.const 1508970993) (.var (.n 181))) = V (.KW 0 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5)))
    (_ : V (.KW 0 0 5) = 1508970993#32 + V (.W 0 0 5)) :
    E.eval env (.add (.const 1508970993) (.var (.n 181))) = V (.KW 0 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core4_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5)))
    (_ : V (.KW 0 0 5) = 1508970993#32 + V (.W 0 0 5)) :
    E.eval env (.add (.const 1508970993) (.var (.n 181))) = V (.KW 0 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step4 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L4 inp env) (hm : HMem 128 inp env) :
    Inv1 L5 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 41 K4)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 0 (by decide)).trans (core4_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 1 (by decide)).trans (core4_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 2 (by decide)).trans (core4_12 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 4 (by decide)) (qA_succI inp 0 0 (4) (by decide)) ((qKW inp 0 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])))
  | 3, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 3 (by decide)).trans (core4_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 4 (by decide)).trans (core4_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 5 (by decide)).trans (core4_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 6 (by decide)).trans (core4_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 12 (by decide)) (qE_succI inp 0 0 (4) (by decide)) ((qKW inp 0 0 4).trans (by rw [show Spec.K 4 = 961987163#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 7 (by decide)).trans (core4_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 8 (by decide)).trans (core4_100 (qv inp) inp env (inv1_get hI 21 (by decide)) (inv1_get hI 12 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 9 (by decide)).trans (core4_101 (qv inp) inp env (inv1_get hI 22 (by decide)) (inv1_get hI 13 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 10 (by decide)).trans (core4_102 (qv inp) inp env (inv1_get hI 23 (by decide)) (inv1_get hI 14 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 11 (by decide)).trans (core4_103 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 15 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 12 (by decide)).trans (core4_116 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 13 (by decide)).trans (core4_117 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 14 (by decide)).trans (core4_118 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 15 (by decide)).trans (core4_119 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 16 (by decide)).trans (core4_148 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 17 (by decide)).trans (core4_149 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 18 (by decide)).trans (core4_150 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 19 (by decide)).trans (core4_151 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 20 (by decide)).trans (core4_164 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 21 (by decide)).trans (core4_165 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 22 (by decide)).trans (core4_166 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 23 (by decide)).trans (core4_167 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 24 (by decide)).trans (core4_196 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 25 (by decide)).trans (core4_197 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 26 (by decide)).trans (core4_198 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 27 (by decide)).trans (core4_199 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 28 (by decide)).trans (core4_212 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 29 (by decide)).trans (core4_213 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 30 (by decide)).trans (core4_214 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 31 (by decide)).trans (core4_215 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 32 (by decide)).trans (core4_1000 (qv inp) inp env (inv1_get hI 15 (by decide)) ((qKW inp 0 0 7).trans (by rw [show Spec.K 7 = 2870763221#32 from by decide])))
  | 33, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 33 (by decide)).trans (core4_1001 (qv inp) inp env (inv1_get hI 15 (by decide)) ((qKW inp 0 0 7).trans (by rw [show Spec.K 7 = 2870763221#32 from by decide])))
  | 34, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 34 (by decide)).trans (core4_1002 (qv inp) inp env (inv1_get hI 15 (by decide)) ((qKW inp 0 0 7).trans (by rw [show Spec.K 7 = 2870763221#32 from by decide])))
  | 35, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 35 (by decide)).trans (core4_1003 (qv inp) inp env (inv1_get hI 15 (by decide)) ((qKW inp 0 0 7).trans (by rw [show Spec.K 7 = 2870763221#32 from by decide])))
  | 36, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 36 (by decide)).trans (core4_1004 (qv inp) inp env (inv1_get hI 14 (by decide)) ((qKW inp 0 0 6).trans (by rw [show Spec.K 6 = 2453635748#32 from by decide])))
  | 37, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 37 (by decide)).trans (core4_1005 (qv inp) inp env (inv1_get hI 14 (by decide)) ((qKW inp 0 0 6).trans (by rw [show Spec.K 6 = 2453635748#32 from by decide])))
  | 38, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 38 (by decide)).trans (core4_1006 (qv inp) inp env (inv1_get hI 14 (by decide)) ((qKW inp 0 0 6).trans (by rw [show Spec.K 6 = 2453635748#32 from by decide])))
  | 39, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 39 (by decide)).trans (core4_1007 (qv inp) inp env (inv1_get hI 14 (by decide)) ((qKW inp 0 0 6).trans (by rw [show Spec.K 6 = 2453635748#32 from by decide])))
  | 40, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 40 (by decide)).trans (core4_1008 (qv inp) inp env (inv1_get hI 13 (by decide)) ((qKW inp 0 0 5).trans (by rw [show Spec.K 5 = 1508970993#32 from by decide])))
  | 41, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 41 (by decide)).trans (core4_1009 (qv inp) inp env (inv1_get hI 13 (by decide)) ((qKW inp 0 0 5).trans (by rw [show Spec.K 5 = 1508970993#32 from by decide])))
  | 42, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 42 (by decide)).trans (core4_1010 (qv inp) inp env (inv1_get hI 13 (by decide)) ((qKW inp 0 0 5).trans (by rw [show Spec.K 5 = 1508970993#32 from by decide])))
  | 43, _ => exact (slice_trees prog 4 _ _ 41 K4 K5 T4 slice4 env 43 (by decide)).trans (core4_1011 (qv inp) inp env (inv1_get hI 13 (by decide)) ((qKW inp 0 0 5).trans (by rw [show Spec.K 5 = 1508970993#32 from by decide])))
  | _ + 44, hk => simp only [L5, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
