import Hashtree.Gen.WinSseX1LW.It.D20
import Hashtree.Gen.WinSseX1LW.It.D19
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice20 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 41 K20 K21 T20 = true := by
  decide +kernel

theorem core20_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (20)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (20)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (19)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (19)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (17))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (19))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (18))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (20))))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20)))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (20))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (18))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (19))))
    (_ : V (.A 0 0 (21)) = (V (.E 0 0 (17)) + Sigma1 (V (.E 0 0 (20))) + Ch (V (.E 0 0 (20))) (V (.E 0 0 (19))) (V (.E 0 0 (18))) + V (.KW 0 0 20)) + (Sigma0 (V (.A 0 0 (20))) + Maj (V (.A 0 0 (20))) (V (.A 0 0 (19))) (V (.A 0 0 (18)))))
    (_ : V (.KW 0 0 20) = 770255983#32 + V (.W 0 0 20)) :
    E.eval env (.add (.add (.add (.var (.n 12)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 14))) (.var (.n 0))) (.var (.n 14))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 14) (.var (.n 0))) 5) (.var (.n 0))) 6)) (.add (.const 770255983) (.var (.n 180))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 9) (.var (.n 24))) 11) (.var (.n 24))) 2)) (.or (.and (.or (.var (.n 24)) (.var (.n 20))) (.var (.n 18))) (.and (.var (.n 24)) (.var (.n 20))))) = V (.A 0 0 (21)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (18)))) :
    E.eval env (.var (.n 14)) = V (.E 0 0 (18)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (19)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (19)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (18)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (18)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (17))))
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (17))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (19))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (18))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (20))))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20)))
    (_ : V (.E 0 0 (21)) = V (.A 0 0 (17)) + (V (.E 0 0 (17)) + Sigma1 (V (.E 0 0 (20))) + Ch (V (.E 0 0 (20))) (V (.E 0 0 (19))) (V (.E 0 0 (18))) + V (.KW 0 0 20)))
    (_ : V (.KW 0 0 20) = 770255983#32 + V (.W 0 0 20)) :
    E.eval env (.add (.var (.n 22)) (.add (.var (.n 12)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 14))) (.var (.n 0))) (.var (.n 14))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 14) (.var (.n 0))) 5) (.var (.n 0))) 6)) (.add (.const 770255983) (.var (.n 180)))))) = V (.E 0 0 (21)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (20)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (20)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 29)))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.add (.var (.n 213)) (.var (.n 180))) = QE.eval V inp (.add (.q (.W 0 0 29)) (.q (.W 0 0 20))) := by
  simp_all only [E.eval, QE.eval]

theorem core20_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 30)))
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.add (.var (.n 214)) (.var (.n 181))) = QE.eval V inp (.add (.q (.W 0 0 30)) (.q (.W 0 0 21))) := by
  simp_all only [E.eval, QE.eval]

theorem core20_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 31)))
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22))) :
    E.eval env (.add (.var (.n 215)) (.var (.n 182))) = QE.eval V inp (.add (.q (.W 0 0 31)) (.q (.W 0 0 22))) := by
  simp_all only [E.eval, QE.eval]

theorem core20_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 32)))
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23))) :
    E.eval env (.add (.var (.n 164)) (.var (.n 183))) = QE.eval V inp (.add (.q (.W 0 0 32)) (.q (.W 0 0 23))) := by
  simp_all only [E.eval, QE.eval]

theorem core20_116 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.or (.shl (.var (.n 181)) 25) (.shr (.var (.n 181)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 21)) 25) (.shr (.q (.W 0 0 21)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core20_117 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22))) :
    E.eval env (.or (.shl (.var (.n 182)) 25) (.shr (.var (.n 182)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 22)) 25) (.shr (.q (.W 0 0 22)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core20_118 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23))) :
    E.eval env (.or (.shl (.var (.n 183)) 25) (.shr (.var (.n 183)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 23)) 25) (.shr (.q (.W 0 0 23)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core20_119 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 24))) :
    E.eval env (.or (.shl (.var (.n 196)) 25) (.shr (.var (.n 196)) 7)) = QE.eval V inp (.or (.shl (.q (.W 0 0 24)) 25) (.shr (.q (.W 0 0 24)) 7)) := by
  simp_all only [E.eval, QE.eval]

theorem core20_148 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_149 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_150 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_151 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 24))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 24) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 32))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 32) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 24))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 24) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 25))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 25) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 26))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 26) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 27))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 27) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 28))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 28) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 29))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 29) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 30))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 31))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23)))
    (_ : V (.KW 0 0 23) = 1996064986#32 + V (.W 0 0 23)) :
    E.eval env (.add (.const 1996064986) (.var (.n 183))) = V (.KW 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23)))
    (_ : V (.KW 0 0 23) = 1996064986#32 + V (.W 0 0 23)) :
    E.eval env (.add (.const 1996064986) (.var (.n 183))) = V (.KW 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23)))
    (_ : V (.KW 0 0 23) = 1996064986#32 + V (.W 0 0 23)) :
    E.eval env (.add (.const 1996064986) (.var (.n 183))) = V (.KW 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23)))
    (_ : V (.KW 0 0 23) = 1996064986#32 + V (.W 0 0 23)) :
    E.eval env (.add (.const 1996064986) (.var (.n 183))) = V (.KW 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22)))
    (_ : V (.KW 0 0 22) = 1555081692#32 + V (.W 0 0 22)) :
    E.eval env (.add (.const 1555081692) (.var (.n 182))) = V (.KW 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22)))
    (_ : V (.KW 0 0 22) = 1555081692#32 + V (.W 0 0 22)) :
    E.eval env (.add (.const 1555081692) (.var (.n 182))) = V (.KW 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22)))
    (_ : V (.KW 0 0 22) = 1555081692#32 + V (.W 0 0 22)) :
    E.eval env (.add (.const 1555081692) (.var (.n 182))) = V (.KW 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22)))
    (_ : V (.KW 0 0 22) = 1555081692#32 + V (.W 0 0 22)) :
    E.eval env (.add (.const 1555081692) (.var (.n 182))) = V (.KW 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21)))
    (_ : V (.KW 0 0 21) = 1249150122#32 + V (.W 0 0 21)) :
    E.eval env (.add (.const 1249150122) (.var (.n 181))) = V (.KW 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21)))
    (_ : V (.KW 0 0 21) = 1249150122#32 + V (.W 0 0 21)) :
    E.eval env (.add (.const 1249150122) (.var (.n 181))) = V (.KW 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21)))
    (_ : V (.KW 0 0 21) = 1249150122#32 + V (.W 0 0 21)) :
    E.eval env (.add (.const 1249150122) (.var (.n 181))) = V (.KW 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core20_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21)))
    (_ : V (.KW 0 0 21) = 1249150122#32 + V (.W 0 0 21)) :
    E.eval env (.add (.const 1249150122) (.var (.n 181))) = V (.KW 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step20 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L20 inp env) (hm : HMem 128 inp env) :
    Inv1 L21 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 41 K20)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 0 (by decide)).trans (core20_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 1 (by decide)).trans (core20_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 2 (by decide)).trans (core20_12 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 4 (by decide)) (qA_succI inp 0 0 (20) (by decide)) ((qKW inp 0 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide])))
  | 3, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 3 (by decide)).trans (core20_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 4 (by decide)).trans (core20_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 5 (by decide)).trans (core20_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 6 (by decide)).trans (core20_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 12 (by decide)) (qE_succI inp 0 0 (20) (by decide)) ((qKW inp 0 0 20).trans (by rw [show Spec.K 20 = 770255983#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 7 (by decide)).trans (core20_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 8 (by decide)).trans (core20_100 (qv inp) inp env (inv1_get hI 21 (by decide)) (inv1_get hI 12 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 9 (by decide)).trans (core20_101 (qv inp) inp env (inv1_get hI 22 (by decide)) (inv1_get hI 13 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 10 (by decide)).trans (core20_102 (qv inp) inp env (inv1_get hI 23 (by decide)) (inv1_get hI 14 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 11 (by decide)).trans (core20_103 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 15 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 12 (by decide)).trans (core20_116 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 13 (by decide)).trans (core20_117 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 14 (by decide)).trans (core20_118 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 15 (by decide)).trans (core20_119 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 16 (by decide)).trans (core20_148 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 17 (by decide)).trans (core20_149 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 18 (by decide)).trans (core20_150 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 19 (by decide)).trans (core20_151 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 20 (by decide)).trans (core20_164 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 21 (by decide)).trans (core20_165 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 22 (by decide)).trans (core20_166 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 23 (by decide)).trans (core20_167 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 24 (by decide)).trans (core20_196 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 25 (by decide)).trans (core20_197 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 26 (by decide)).trans (core20_198 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 27 (by decide)).trans (core20_199 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 28 (by decide)).trans (core20_212 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 29 (by decide)).trans (core20_213 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 30 (by decide)).trans (core20_214 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 31 (by decide)).trans (core20_215 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 32 (by decide)).trans (core20_1000 (qv inp) inp env (inv1_get hI 15 (by decide)) ((qKW inp 0 0 23).trans (by rw [show Spec.K 23 = 1996064986#32 from by decide])))
  | 33, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 33 (by decide)).trans (core20_1001 (qv inp) inp env (inv1_get hI 15 (by decide)) ((qKW inp 0 0 23).trans (by rw [show Spec.K 23 = 1996064986#32 from by decide])))
  | 34, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 34 (by decide)).trans (core20_1002 (qv inp) inp env (inv1_get hI 15 (by decide)) ((qKW inp 0 0 23).trans (by rw [show Spec.K 23 = 1996064986#32 from by decide])))
  | 35, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 35 (by decide)).trans (core20_1003 (qv inp) inp env (inv1_get hI 15 (by decide)) ((qKW inp 0 0 23).trans (by rw [show Spec.K 23 = 1996064986#32 from by decide])))
  | 36, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 36 (by decide)).trans (core20_1004 (qv inp) inp env (inv1_get hI 14 (by decide)) ((qKW inp 0 0 22).trans (by rw [show Spec.K 22 = 1555081692#32 from by decide])))
  | 37, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 37 (by decide)).trans (core20_1005 (qv inp) inp env (inv1_get hI 14 (by decide)) ((qKW inp 0 0 22).trans (by rw [show Spec.K 22 = 1555081692#32 from by decide])))
  | 38, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 38 (by decide)).trans (core20_1006 (qv inp) inp env (inv1_get hI 14 (by decide)) ((qKW inp 0 0 22).trans (by rw [show Spec.K 22 = 1555081692#32 from by decide])))
  | 39, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 39 (by decide)).trans (core20_1007 (qv inp) inp env (inv1_get hI 14 (by decide)) ((qKW inp 0 0 22).trans (by rw [show Spec.K 22 = 1555081692#32 from by decide])))
  | 40, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 40 (by decide)).trans (core20_1008 (qv inp) inp env (inv1_get hI 13 (by decide)) ((qKW inp 0 0 21).trans (by rw [show Spec.K 21 = 1249150122#32 from by decide])))
  | 41, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 41 (by decide)).trans (core20_1009 (qv inp) inp env (inv1_get hI 13 (by decide)) ((qKW inp 0 0 21).trans (by rw [show Spec.K 21 = 1249150122#32 from by decide])))
  | 42, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 42 (by decide)).trans (core20_1010 (qv inp) inp env (inv1_get hI 13 (by decide)) ((qKW inp 0 0 21).trans (by rw [show Spec.K 21 = 1249150122#32 from by decide])))
  | 43, _ => exact (slice_trees prog 4 _ _ 41 K20 K21 T20 slice20 env 43 (by decide)).trans (core20_1011 (qv inp) inp env (inv1_get hI 13 (by decide)) ((qKW inp 0 0 21).trans (by rw [show Spec.K 21 = 1249150122#32 from by decide])))
  | _ + 44, hk => simp only [L21, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
