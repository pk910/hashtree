import Hashtree.Gen.SseX1LW.It.D44
import Hashtree.Gen.SseX1LW.It.D43
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It
open Hashtree.Gen.SseX1LW

theorem slice44 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 42 K44 K45 T44 = true := by
  decide +kernel

theorem core44_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (44)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (44)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (42)))) :
    E.eval env (.var (.n 2)) = V (.E 0 0 (42)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (43)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (43)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (41))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (43))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (42))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (44))))
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44)))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (44))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (42))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (43))))
    (_ : V (.A 0 0 (45)) = (V (.E 0 0 (41)) + Sigma1 (V (.E 0 0 (44))) + Ch (V (.E 0 0 (44))) (V (.E 0 0 (43))) (V (.E 0 0 (42))) + V (.KW 0 0 44)) + (Sigma0 (V (.A 0 0 (44))) + Maj (V (.A 0 0 (44))) (V (.A 0 0 (43))) (V (.A 0 0 (42)))))
    (_ : V (.KW 0 0 44) = 3516065817#32 + V (.W 0 0 44)) :
    E.eval env (.add (.add (.add (.var (.n 16)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 2))) (.var (.n 0))) (.var (.n 2))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 14) (.var (.n 0))) 5) (.var (.n 0))) 6)) (.add (.const 3516065817) (.var (.n 212))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 9) (.var (.n 24))) 11) (.var (.n 24))) 2)) (.or (.and (.or (.var (.n 24)) (.var (.n 20))) (.var (.n 18))) (.and (.var (.n 24)) (.var (.n 20))))) = V (.A 0 0 (45)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (43)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (43)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (42)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (42)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (41))))
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (41))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (43))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (42))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (44))))
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44)))
    (_ : V (.E 0 0 (45)) = V (.A 0 0 (41)) + (V (.E 0 0 (41)) + Sigma1 (V (.E 0 0 (44))) + Ch (V (.E 0 0 (44))) (V (.E 0 0 (43))) (V (.E 0 0 (42))) + V (.KW 0 0 44)))
    (_ : V (.KW 0 0 44) = 3516065817#32 + V (.W 0 0 44)) :
    E.eval env (.add (.var (.n 22)) (.add (.var (.n 16)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 2))) (.var (.n 0))) (.var (.n 2))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 14) (.var (.n 0))) 5) (.var (.n 0))) 6)) (.add (.const 3516065817) (.var (.n 212)))))) = V (.E 0 0 (45)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (44)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (44)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53)))
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.add (.var (.n 181)) (.var (.n 212))) = QE.eval V inp (.add (.q (.W 0 0 53)) (.q (.W 0 0 44))) := by
  simp_all only [E.eval, QE.eval]

theorem core44_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.add (.var (.n 182)) (.var (.n 213))) = QE.eval V inp (.add (.q (.W 0 0 54)) (.q (.W 0 0 45))) := by
  simp_all only [E.eval, QE.eval]

theorem core44_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.add (.var (.n 183)) (.var (.n 214))) = QE.eval V inp (.add (.q (.W 0 0 55)) (.q (.W 0 0 46))) := by
  simp_all only [E.eval, QE.eval]

theorem core44_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56)))
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.add (.var (.n 196)) (.var (.n 215))) = QE.eval V inp (.add (.q (.W 0 0 56)) (.q (.W 0 0 47))) := by
  simp_all only [E.eval, QE.eval]

theorem core44_116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.or (.shl (.var (.n 213)) 25) (.shr (.var (.n 213)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 45)) 25) (.shr (.q (.W 0 0 45)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core44_117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.or (.shl (.var (.n 214)) 25) (.shr (.var (.n 214)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 46)) 25) (.shr (.q (.W 0 0 46)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core44_118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.or (.shl (.var (.n 215)) 25) (.shr (.var (.n 215)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 47)) 25) (.shr (.q (.W 0 0 47)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core44_119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48))) :
    E.eval env (.or (.shl (.var (.n 164)) 25) (.shr (.var (.n 164)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 48)) 25) (.shr (.q (.W 0 0 48)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core44_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 48) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 48) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47)))
    (_ : V (.KW 0 0 47) = 275423344#32 + V (.W 0 0 47)) :
    E.eval env (.add (.const 275423344) (.var (.n 215))) = V (.KW 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47)))
    (_ : V (.KW 0 0 47) = 275423344#32 + V (.W 0 0 47)) :
    E.eval env (.add (.const 275423344) (.var (.n 215))) = V (.KW 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47)))
    (_ : V (.KW 0 0 47) = 275423344#32 + V (.W 0 0 47)) :
    E.eval env (.add (.const 275423344) (.var (.n 215))) = V (.KW 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47)))
    (_ : V (.KW 0 0 47) = 275423344#32 + V (.W 0 0 47)) :
    E.eval env (.add (.const 275423344) (.var (.n 215))) = V (.KW 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46)))
    (_ : V (.KW 0 0 46) = 4094571909#32 + V (.W 0 0 46)) :
    E.eval env (.add (.const 4094571909) (.var (.n 214))) = V (.KW 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46)))
    (_ : V (.KW 0 0 46) = 4094571909#32 + V (.W 0 0 46)) :
    E.eval env (.add (.const 4094571909) (.var (.n 214))) = V (.KW 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46)))
    (_ : V (.KW 0 0 46) = 4094571909#32 + V (.W 0 0 46)) :
    E.eval env (.add (.const 4094571909) (.var (.n 214))) = V (.KW 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46)))
    (_ : V (.KW 0 0 46) = 4094571909#32 + V (.W 0 0 46)) :
    E.eval env (.add (.const 4094571909) (.var (.n 214))) = V (.KW 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45)))
    (_ : V (.KW 0 0 45) = 3600352804#32 + V (.W 0 0 45)) :
    E.eval env (.add (.const 3600352804) (.var (.n 213))) = V (.KW 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45)))
    (_ : V (.KW 0 0 45) = 3600352804#32 + V (.W 0 0 45)) :
    E.eval env (.add (.const 3600352804) (.var (.n 213))) = V (.KW 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45)))
    (_ : V (.KW 0 0 45) = 3600352804#32 + V (.W 0 0 45)) :
    E.eval env (.add (.const 3600352804) (.var (.n 213))) = V (.KW 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core44_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45)))
    (_ : V (.KW 0 0 45) = 3600352804#32 + V (.W 0 0 45)) :
    E.eval env (.add (.const 3600352804) (.var (.n 213))) = V (.KW 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step44 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L44 inp env) (hm : HMem 128 inp env) :
    Inv1 L45 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 42 K44)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 0 (by decide)).trans (core44_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 1 (by decide)).trans (core44_2 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 2 (by decide)).trans (core44_6 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 3 (by decide)).trans (core44_16 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 20 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 4 (by decide)) (qA_succI inp 0 0 (44) (by decide)) ((qKW inp 0 0 44).trans (by rw [show Spec.K 44 = 3516065817#32 from by decide])))
  | 4, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 4 (by decide)).trans (core44_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 5 (by decide)).trans (core44_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 6 (by decide)).trans (core44_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 20 (by decide)) (qE_succI inp 0 0 (44) (by decide)) ((qKW inp 0 0 44).trans (by rw [show Spec.K 44 = 3516065817#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 7 (by decide)).trans (core44_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 8 (by decide)).trans (core44_100 (qv inp) inp env (inv1_get hI 13 (by decide)) (inv1_get hI 20 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 9 (by decide)).trans (core44_101 (qv inp) inp env (inv1_get hI 14 (by decide)) (inv1_get hI 21 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 10 (by decide)).trans (core44_102 (qv inp) inp env (inv1_get hI 15 (by decide)) (inv1_get hI 22 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 11 (by decide)).trans (core44_103 (qv inp) inp env (inv1_get hI 16 (by decide)) (inv1_get hI 23 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 12 (by decide)).trans (core44_116 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 13 (by decide)).trans (core44_117 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 14 (by decide)).trans (core44_118 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 15 (by decide)).trans (core44_119 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 16 (by decide)).trans (core44_148 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 17 (by decide)).trans (core44_149 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 18 (by decide)).trans (core44_150 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 19 (by decide)).trans (core44_151 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 20 (by decide)).trans (core44_164 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 21 (by decide)).trans (core44_165 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 22 (by decide)).trans (core44_166 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 23 (by decide)).trans (core44_167 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 24 (by decide)).trans (core44_180 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 25 (by decide)).trans (core44_181 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 26 (by decide)).trans (core44_182 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 27 (by decide)).trans (core44_183 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 28 (by decide)).trans (core44_196 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 29 (by decide)).trans (core44_197 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 30 (by decide)).trans (core44_198 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 31 (by decide)).trans (core44_199 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 32 (by decide)).trans (core44_1000 (qv inp) inp env (inv1_get hI 23 (by decide)) ((qKW inp 0 0 47).trans (by rw [show Spec.K 47 = 275423344#32 from by decide])))
  | 33, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 33 (by decide)).trans (core44_1001 (qv inp) inp env (inv1_get hI 23 (by decide)) ((qKW inp 0 0 47).trans (by rw [show Spec.K 47 = 275423344#32 from by decide])))
  | 34, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 34 (by decide)).trans (core44_1002 (qv inp) inp env (inv1_get hI 23 (by decide)) ((qKW inp 0 0 47).trans (by rw [show Spec.K 47 = 275423344#32 from by decide])))
  | 35, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 35 (by decide)).trans (core44_1003 (qv inp) inp env (inv1_get hI 23 (by decide)) ((qKW inp 0 0 47).trans (by rw [show Spec.K 47 = 275423344#32 from by decide])))
  | 36, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 36 (by decide)).trans (core44_1004 (qv inp) inp env (inv1_get hI 22 (by decide)) ((qKW inp 0 0 46).trans (by rw [show Spec.K 46 = 4094571909#32 from by decide])))
  | 37, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 37 (by decide)).trans (core44_1005 (qv inp) inp env (inv1_get hI 22 (by decide)) ((qKW inp 0 0 46).trans (by rw [show Spec.K 46 = 4094571909#32 from by decide])))
  | 38, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 38 (by decide)).trans (core44_1006 (qv inp) inp env (inv1_get hI 22 (by decide)) ((qKW inp 0 0 46).trans (by rw [show Spec.K 46 = 4094571909#32 from by decide])))
  | 39, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 39 (by decide)).trans (core44_1007 (qv inp) inp env (inv1_get hI 22 (by decide)) ((qKW inp 0 0 46).trans (by rw [show Spec.K 46 = 4094571909#32 from by decide])))
  | 40, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 40 (by decide)).trans (core44_1008 (qv inp) inp env (inv1_get hI 21 (by decide)) ((qKW inp 0 0 45).trans (by rw [show Spec.K 45 = 3600352804#32 from by decide])))
  | 41, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 41 (by decide)).trans (core44_1009 (qv inp) inp env (inv1_get hI 21 (by decide)) ((qKW inp 0 0 45).trans (by rw [show Spec.K 45 = 3600352804#32 from by decide])))
  | 42, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 42 (by decide)).trans (core44_1010 (qv inp) inp env (inv1_get hI 21 (by decide)) ((qKW inp 0 0 45).trans (by rw [show Spec.K 45 = 3600352804#32 from by decide])))
  | 43, _ => exact (slice_trees prog 4 _ _ 42 K44 K45 T44 slice44 env 43 (by decide)).trans (core44_1011 (qv inp) inp env (inv1_get hI 21 (by decide)) ((qKW inp 0 0 45).trans (by rw [show Spec.K 45 = 3600352804#32 from by decide])))
  | _ + 44, hk => simp only [L45, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It
