import Hashtree.Gen.SseX1LW.It.D1
import Hashtree.Gen.SseX1LW.It.D0
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It
open Hashtree.Gen.SseX1LW

theorem slice1 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K1 K2 T1 = true := by
  decide +kernel

theorem core1_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (1))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 1)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 1)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 1)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 1)))
    (_ : V (.E 0 0 (2)) = V (.A 0 0 (-2)) + (V (.E 0 0 (-2)) + Sigma1 (V (.E 0 0 (1))) + Ch (V (.E 0 0 (1))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) + V (.KW 0 0 1)))
    (_ : V (.A 0 0 (-2)) = V (.H 0 0 2))
    (_ : V (.H 0 0 2) = 1013904242#32)
    (_ : V (.E 0 0 (-2)) = V (.H 0 0 6))
    (_ : V (.H 0 0 6) = 528734635#32)
    (_ : V (.E 0 0 (0)) = V (.H 0 0 4))
    (_ : V (.H 0 0 4) = 1359893119#32)
    (_ : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (_ : V (.H 0 0 5) = 2600822924#32) :
    E.eval env (.add (.const 1013904242) (.add (.const 528734635) (.add (.add (.xor (.and (.const 3389733619) (.var (.n 16))) (.const 2600822924)) (.ror (.xor (.ror (.xor (.ror (.var (.n 16)) 14) (.var (.n 16))) 5) (.var (.n 16))) 6)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))))) = V (.E 0 0 (2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (1)))) :
    E.eval env (.var (.n 16)) = V (.E 0 0 (1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (1))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 1)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 1)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 1)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 1)))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (1))))
    (_ : V (.A 0 0 (2)) = (V (.E 0 0 (-2)) + Sigma1 (V (.E 0 0 (1))) + Ch (V (.E 0 0 (1))) (V (.E 0 0 (0))) (V (.E 0 0 (-1))) + V (.KW 0 0 1)) + (Sigma0 (V (.A 0 0 (1))) + Maj (V (.A 0 0 (1))) (V (.A 0 0 (0))) (V (.A 0 0 (-1)))))
    (_ : V (.E 0 0 (-2)) = V (.H 0 0 6))
    (_ : V (.H 0 0 6) = 528734635#32)
    (_ : V (.E 0 0 (0)) = V (.H 0 0 4))
    (_ : V (.H 0 0 4) = 1359893119#32)
    (_ : V (.E 0 0 (-1)) = V (.H 0 0 5))
    (_ : V (.H 0 0 5) = 2600822924#32)
    (_ : V (.A 0 0 (0)) = V (.H 0 0 0))
    (_ : V (.H 0 0 0) = 1779033703#32)
    (_ : V (.A 0 0 (-1)) = V (.H 0 0 1))
    (_ : V (.H 0 0 1) = 3144134277#32) :
    E.eval env (.add (.add (.add (.const 528734635) (.add (.add (.xor (.and (.const 3389733619) (.var (.n 16))) (.const 2600822924)) (.ror (.xor (.ror (.xor (.ror (.var (.n 16)) 14) (.var (.n 16))) 5) (.var (.n 16))) 6)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 22)) 9) (.var (.n 22))) 11) (.var (.n 22))) 2)) (.or (.and (.or (.var (.n 22)) (.const 3144134277)) (.const 1779033703)) (.and (.var (.n 22)) (.const 3144134277)))) = V (.A 0 0 (2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (1)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 36) 0) (.c 255)) (.shl (.and (.shr (.m 37) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 38) 0) (.c 255)) 16) (.shl (.and (.shr (.m 39) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 36) 0) (.c 255)) (.shl (.and (.shr (.m 37) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 38) 0) (.c 255)) 16) (.shl (.and (.shr (.m 39) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 36) 0) (.c 255)) (.shl (.and (.shr (.m 37) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 38) 0) (.c 255)) 16) (.shl (.and (.shr (.m 39) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 36) 0) (.c 255)) (.shl (.and (.shr (.m 37) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 38) 0) (.c 255)) 16) (.shl (.and (.shr (.m 39) 0) (.c 255)) 24))) 0) (.c 255)) 24))) (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 0) 0) (.c 255)) (.shl (.and (.shr (.m 1) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 2) 0) (.c 255)) 16) (.shl (.and (.shr (.m 3) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 0) 0) (.c 255)) (.shl (.and (.shr (.m 1) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 2) 0) (.c 255)) 16) (.shl (.and (.shr (.m 3) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 0) 0) (.c 255)) (.shl (.and (.shr (.m 1) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 2) 0) (.c 255)) 16) (.shl (.and (.shr (.m 3) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 0) 0) (.c 255)) (.shl (.and (.shr (.m 1) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 2) 0) (.c 255)) 16) (.shl (.and (.shr (.m 3) 0) (.c 255)) 24))) 0) (.c 255)) 24)))))
    (_ : env (.n 116) = QE.eval V inp (.or (.shl (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 0) (.c 255)) 24))) 25) (.shr (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 0) (.c 255)) 24))) 7)))
    (_ : env (.n 148) = QE.eval V inp (.q (.W 0 0 1)))
    (_ : V (.M2 0 0 0) = V (.M1 0 0 0) + V (.W 0 0 9))
    (_ : V (.M1 0 0 0) = V (.W 0 0 0) + sigma0 (V (.W 0 0 1)))
    (_ : V (.W 0 0 0) = bswap (V (.R 0 0)))
    (_ : V (.R 0 0) = ((((0 : Word) ||| (inp 0).zeroExtend 32 <<< 0) ||| (inp 1).zeroExtend 32 <<< 8) ||| (inp 2).zeroExtend 32 <<< 16) ||| (inp 3).zeroExtend 32 <<< 24)
    (_ : V (.W 0 0 9) = bswap (V (.R 0 9)))
    (_ : V (.R 0 9) = ((((0 : Word) ||| (inp 36).zeroExtend 32 <<< 0) ||| (inp 37).zeroExtend 32 <<< 8) ||| (inp 38).zeroExtend 32 <<< 16) ||| (inp 39).zeroExtend 32 <<< 24)
    (_ : V (.W 0 0 1) = bswap (V (.R 0 1)))
    (_ : V (.R 0 1) = ((((0 : Word) ||| (inp 4).zeroExtend 32 <<< 0) ||| (inp 5).zeroExtend 32 <<< 8) ||| (inp 6).zeroExtend 32 <<< 16) ||| (inp 7).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 100)) (.xor (.xor (.xor (.var (.n 116)) (.shl (.var (.n 148)) 14)) (.shr (.var (.n 148)) 18)) (.shr (.var (.n 148)) 3))) = V (.M2 0 0 0) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 40) 0) (.c 255)) (.shl (.and (.shr (.m 41) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 42) 0) (.c 255)) 16) (.shl (.and (.shr (.m 43) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 40) 0) (.c 255)) (.shl (.and (.shr (.m 41) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 42) 0) (.c 255)) 16) (.shl (.and (.shr (.m 43) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 40) 0) (.c 255)) (.shl (.and (.shr (.m 41) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 42) 0) (.c 255)) 16) (.shl (.and (.shr (.m 43) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 40) 0) (.c 255)) (.shl (.and (.shr (.m 41) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 42) 0) (.c 255)) 16) (.shl (.and (.shr (.m 43) 0) (.c 255)) 24))) 0) (.c 255)) 24))) (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 4) 0) (.c 255)) (.shl (.and (.shr (.m 5) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 6) 0) (.c 255)) 16) (.shl (.and (.shr (.m 7) 0) (.c 255)) 24))) 0) (.c 255)) 24)))))
    (_ : env (.n 117) = QE.eval V inp (.or (.shl (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 0) (.c 255)) 24))) 25) (.shr (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 0) (.c 255)) 24))) 7)))
    (_ : env (.n 149) = QE.eval V inp (.q (.W 0 0 2)))
    (_ : V (.M2 0 0 1) = V (.M1 0 0 1) + V (.W 0 0 10))
    (_ : V (.M1 0 0 1) = V (.W 0 0 1) + sigma0 (V (.W 0 0 2)))
    (_ : V (.W 0 0 1) = bswap (V (.R 0 1)))
    (_ : V (.R 0 1) = ((((0 : Word) ||| (inp 4).zeroExtend 32 <<< 0) ||| (inp 5).zeroExtend 32 <<< 8) ||| (inp 6).zeroExtend 32 <<< 16) ||| (inp 7).zeroExtend 32 <<< 24)
    (_ : V (.W 0 0 10) = bswap (V (.R 0 10)))
    (_ : V (.R 0 10) = ((((0 : Word) ||| (inp 40).zeroExtend 32 <<< 0) ||| (inp 41).zeroExtend 32 <<< 8) ||| (inp 42).zeroExtend 32 <<< 16) ||| (inp 43).zeroExtend 32 <<< 24)
    (_ : V (.W 0 0 2) = bswap (V (.R 0 2)))
    (_ : V (.R 0 2) = ((((0 : Word) ||| (inp 8).zeroExtend 32 <<< 0) ||| (inp 9).zeroExtend 32 <<< 8) ||| (inp 10).zeroExtend 32 <<< 16) ||| (inp 11).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 101)) (.xor (.xor (.xor (.var (.n 117)) (.shl (.var (.n 149)) 14)) (.shr (.var (.n 149)) 18)) (.shr (.var (.n 149)) 3))) = V (.M2 0 0 1) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 44) 0) (.c 255)) (.shl (.and (.shr (.m 45) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 46) 0) (.c 255)) 16) (.shl (.and (.shr (.m 47) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 44) 0) (.c 255)) (.shl (.and (.shr (.m 45) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 46) 0) (.c 255)) 16) (.shl (.and (.shr (.m 47) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 44) 0) (.c 255)) (.shl (.and (.shr (.m 45) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 46) 0) (.c 255)) 16) (.shl (.and (.shr (.m 47) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 44) 0) (.c 255)) (.shl (.and (.shr (.m 45) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 46) 0) (.c 255)) 16) (.shl (.and (.shr (.m 47) 0) (.c 255)) 24))) 0) (.c 255)) 24))) (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 8) 0) (.c 255)) (.shl (.and (.shr (.m 9) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 10) 0) (.c 255)) 16) (.shl (.and (.shr (.m 11) 0) (.c 255)) 24))) 0) (.c 255)) 24)))))
    (_ : env (.n 118) = QE.eval V inp (.or (.shl (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 0) (.c 255)) 24))) 25) (.shr (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 0) (.c 255)) 24))) 7)))
    (_ : env (.n 150) = QE.eval V inp (.q (.W 0 0 3)))
    (_ : V (.M2 0 0 2) = V (.M1 0 0 2) + V (.W 0 0 11))
    (_ : V (.M1 0 0 2) = V (.W 0 0 2) + sigma0 (V (.W 0 0 3)))
    (_ : V (.W 0 0 2) = bswap (V (.R 0 2)))
    (_ : V (.R 0 2) = ((((0 : Word) ||| (inp 8).zeroExtend 32 <<< 0) ||| (inp 9).zeroExtend 32 <<< 8) ||| (inp 10).zeroExtend 32 <<< 16) ||| (inp 11).zeroExtend 32 <<< 24)
    (_ : V (.W 0 0 11) = bswap (V (.R 0 11)))
    (_ : V (.R 0 11) = ((((0 : Word) ||| (inp 44).zeroExtend 32 <<< 0) ||| (inp 45).zeroExtend 32 <<< 8) ||| (inp 46).zeroExtend 32 <<< 16) ||| (inp 47).zeroExtend 32 <<< 24)
    (_ : V (.W 0 0 3) = bswap (V (.R 0 3)))
    (_ : V (.R 0 3) = ((((0 : Word) ||| (inp 12).zeroExtend 32 <<< 0) ||| (inp 13).zeroExtend 32 <<< 8) ||| (inp 14).zeroExtend 32 <<< 16) ||| (inp 15).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 102)) (.xor (.xor (.xor (.var (.n 118)) (.shl (.var (.n 150)) 14)) (.shr (.var (.n 150)) 18)) (.shr (.var (.n 150)) 3))) = V (.M2 0 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.add (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 48) 0) (.c 255)) (.shl (.and (.shr (.m 49) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 50) 0) (.c 255)) 16) (.shl (.and (.shr (.m 51) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 48) 0) (.c 255)) (.shl (.and (.shr (.m 49) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 50) 0) (.c 255)) 16) (.shl (.and (.shr (.m 51) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 48) 0) (.c 255)) (.shl (.and (.shr (.m 49) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 50) 0) (.c 255)) 16) (.shl (.and (.shr (.m 51) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 48) 0) (.c 255)) (.shl (.and (.shr (.m 49) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 50) 0) (.c 255)) 16) (.shl (.and (.shr (.m 51) 0) (.c 255)) 24))) 0) (.c 255)) 24))) (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 12) 0) (.c 255)) (.shl (.and (.shr (.m 13) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 14) 0) (.c 255)) 16) (.shl (.and (.shr (.m 15) 0) (.c 255)) 24))) 0) (.c 255)) 24)))))
    (_ : env (.n 119) = QE.eval V inp (.or (.shl (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 16) 0) (.c 255)) (.shl (.and (.shr (.m 17) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 18) 0) (.c 255)) 16) (.shl (.and (.shr (.m 19) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 16) 0) (.c 255)) (.shl (.and (.shr (.m 17) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 18) 0) (.c 255)) 16) (.shl (.and (.shr (.m 19) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 16) 0) (.c 255)) (.shl (.and (.shr (.m 17) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 18) 0) (.c 255)) 16) (.shl (.and (.shr (.m 19) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 16) 0) (.c 255)) (.shl (.and (.shr (.m 17) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 18) 0) (.c 255)) 16) (.shl (.and (.shr (.m 19) 0) (.c 255)) 24))) 0) (.c 255)) 24))) 25) (.shr (.or (.or (.and (.shr (.or (.or (.and (.shr (.m 16) 0) (.c 255)) (.shl (.and (.shr (.m 17) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 18) 0) (.c 255)) 16) (.shl (.and (.shr (.m 19) 0) (.c 255)) 24))) 24) (.c 255)) (.shl (.and (.shr (.or (.or (.and (.shr (.m 16) 0) (.c 255)) (.shl (.and (.shr (.m 17) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 18) 0) (.c 255)) 16) (.shl (.and (.shr (.m 19) 0) (.c 255)) 24))) 16) (.c 255)) 8)) (.or (.shl (.and (.shr (.or (.or (.and (.shr (.m 16) 0) (.c 255)) (.shl (.and (.shr (.m 17) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 18) 0) (.c 255)) 16) (.shl (.and (.shr (.m 19) 0) (.c 255)) 24))) 8) (.c 255)) 16) (.shl (.and (.shr (.or (.or (.and (.shr (.m 16) 0) (.c 255)) (.shl (.and (.shr (.m 17) 0) (.c 255)) 8)) (.or (.shl (.and (.shr (.m 18) 0) (.c 255)) 16) (.shl (.and (.shr (.m 19) 0) (.c 255)) 24))) 0) (.c 255)) 24))) 7)))
    (_ : env (.n 151) = QE.eval V inp (.q (.W 0 0 4)))
    (_ : V (.M2 0 0 3) = V (.M1 0 0 3) + V (.W 0 0 12))
    (_ : V (.M1 0 0 3) = V (.W 0 0 3) + sigma0 (V (.W 0 0 4)))
    (_ : V (.W 0 0 3) = bswap (V (.R 0 3)))
    (_ : V (.R 0 3) = ((((0 : Word) ||| (inp 12).zeroExtend 32 <<< 0) ||| (inp 13).zeroExtend 32 <<< 8) ||| (inp 14).zeroExtend 32 <<< 16) ||| (inp 15).zeroExtend 32 <<< 24)
    (_ : V (.W 0 0 12) = bswap (V (.R 0 12)))
    (_ : V (.R 0 12) = ((((0 : Word) ||| (inp 48).zeroExtend 32 <<< 0) ||| (inp 49).zeroExtend 32 <<< 8) ||| (inp 50).zeroExtend 32 <<< 16) ||| (inp 51).zeroExtend 32 <<< 24)
    (_ : V (.W 0 0 4) = bswap (V (.R 0 4)))
    (_ : V (.R 0 4) = ((((0 : Word) ||| (inp 16).zeroExtend 32 <<< 0) ||| (inp 17).zeroExtend 32 <<< 8) ||| (inp 18).zeroExtend 32 <<< 16) ||| (inp 19).zeroExtend 32 <<< 24) :
    E.eval env (.add (.var (.n 103)) (.xor (.xor (.xor (.var (.n 119)) (.shl (.var (.n 151)) 14)) (.shr (.var (.n 151)) 18)) (.shr (.var (.n 151)) 3))) = V (.M2 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 4))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 4) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 8) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 12) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 13))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 13) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 3))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 3))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 3))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 3))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 2))) :
    E.eval env (.var (.n 1004)) = V (.KW 0 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 2))) :
    E.eval env (.var (.n 1005)) = V (.KW 0 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 2))) :
    E.eval env (.var (.n 1006)) = V (.KW 0 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core1_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 2))) :
    E.eval env (.var (.n 1007)) = V (.KW 0 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step1 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L1 inp env) (hm : HMem 128 inp env) :
    Inv1 L2 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K1)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 0 (by decide)).trans (core1_2 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 37 (by decide)) (inv1_get hI 36 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (qE_succI inp 0 0 (1) (by decide)) (qA_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)))
  | 1, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 1 (by decide)).trans (core1_16 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 2 (by decide)).trans (core1_20 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 37 (by decide)) (inv1_get hI 36 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 1 (by decide)) (qA_succI inp 0 0 (1) (by decide)) (qE_initI inp 0 0 2 (-2) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 0 0 1 (-1) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)))
  | 3, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 3 (by decide)).trans (core1_22 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 4 (by decide)).trans (core1_100 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 10 (by decide)) (qM2 inp 0 0 0) (qM1 inp 0 0 0) (qW_R inp 0 0 (by decide)) (qR inp 0 0) (qW_R inp 0 9 (by decide)) (qR inp 0 9) (qW_R inp 0 1 (by decide)) (qR inp 0 1))
  | 5, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 5 (by decide)).trans (core1_101 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 11 (by decide)) (qM2 inp 0 0 1) (qM1 inp 0 0 1) (qW_R inp 0 1 (by decide)) (qR inp 0 1) (qW_R inp 0 10 (by decide)) (qR inp 0 10) (qW_R inp 0 2 (by decide)) (qR inp 0 2))
  | 6, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 6 (by decide)).trans (core1_102 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (qM2 inp 0 0 2) (qM1 inp 0 0 2) (qW_R inp 0 2 (by decide)) (qR inp 0 2) (qW_R inp 0 11 (by decide)) (qR inp 0 11) (qW_R inp 0 3 (by decide)) (qR inp 0 3))
  | 7, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 7 (by decide)).trans (core1_103 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 9 (by decide)) (inv1_get hI 13 (by decide)) (qM2 inp 0 0 3) (qM1 inp 0 0 3) (qW_R inp 0 3 (by decide)) (qR inp 0 3) (qW_R inp 0 12 (by decide)) (qR inp 0 12) (qW_R inp 0 4 (by decide)) (qR inp 0 4))
  | 8, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 8 (by decide)).trans (core1_132 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 9 (by decide)).trans (core1_133 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 10 (by decide)).trans (core1_134 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 11 (by decide)).trans (core1_135 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 12 (by decide)).trans (core1_180 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 13 (by decide)).trans (core1_181 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 14 (by decide)).trans (core1_182 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 15 (by decide)).trans (core1_183 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 16 (by decide)).trans (core1_196 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 17 (by decide)).trans (core1_197 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 18 (by decide)).trans (core1_198 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 19 (by decide)).trans (core1_199 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 20 (by decide)).trans (core1_212 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 21 (by decide)).trans (core1_213 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 22 (by decide)).trans (core1_214 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 23 (by decide)).trans (core1_215 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 24 (by decide)).trans (core1_1000 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 25 (by decide)).trans (core1_1001 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 26 (by decide)).trans (core1_1002 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 27 (by decide)).trans (core1_1003 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 28 (by decide)).trans (core1_1004 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 29 (by decide)).trans (core1_1005 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 30 (by decide)).trans (core1_1006 (qv inp) inp env (inv1_get hI 32 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 38 K1 K2 T1 slice1 env 31 (by decide)).trans (core1_1007 (qv inp) inp env (inv1_get hI 33 (by decide)))
  | _ + 32, hk => simp only [L2, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It
