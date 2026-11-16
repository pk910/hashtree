import Hashtree.Gen.WinAvxX1LW.It.D64
import Hashtree.Gen.WinAvxX1LW.It.D63
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It
open Hashtree.Gen.WinAvxX1LW

theorem slice64 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 48 K64 K65 T64 = true := by
  decide +kernel

theorem core64_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (64))))
    (_ : V (.A 0 1 (0)) = V (.H 0 1 0))
    (_ : V (.H 0 1 0) = V (.H 0 0 0) + V (.A 0 0 (64)))
    (_ : V (.H 0 0 0) = 1779033703#32) :
    E.eval env (.add (.var (.n 0)) (.const 1779033703)) = V (.A 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (63))))
    (_ : V (.A 0 1 (-1)) = V (.H 0 1 1))
    (_ : V (.H 0 1 1) = V (.H 0 0 1) + V (.A 0 0 (63)))
    (_ : V (.H 0 0 1) = 3144134277#32) :
    E.eval env (.add (.var (.n 6)) (.const 3144134277)) = V (.A 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32) (k0 : W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (61))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (63))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (64))))
    (_ : V (.E 0 1 (1)) = V (.A 0 1 (-3)) + (V (.E 0 1 (-3)) + Sigma1 (V (.E 0 1 (0))) + Ch (V (.E 0 1 (0))) (V (.E 0 1 (-1))) (V (.E 0 1 (-2))) + V (.KW 0 1 0)))
    (_ : V (.A 0 1 (-3)) = V (.H 0 1 3))
    (_ : V (.H 0 1 3) = V (.H 0 0 3) + V (.A 0 0 (61)))
    (_ : V (.H 0 0 3) = 2773480762#32)
    (_ : V (.E 0 1 (-3)) = V (.H 0 1 7))
    (_ : V (.H 0 1 7) = V (.H 0 0 7) + V (.E 0 0 (61)))
    (_ : V (.H 0 0 7) = 1541459225#32)
    (_ : V (.E 0 1 (0)) = V (.H 0 1 4))
    (_ : V (.H 0 1 4) = V (.H 0 0 4) + V (.E 0 0 (64)))
    (_ : V (.H 0 0 4) = 1359893119#32)
    (_ : V (.E 0 1 (-1)) = V (.H 0 1 5))
    (_ : V (.H 0 1 5) = V (.H 0 0 5) + V (.E 0 0 (63)))
    (_ : V (.H 0 0 5) = 2600822924#32)
    (_ : V (.E 0 1 (-2)) = V (.H 0 1 6))
    (_ : V (.H 0 1 6) = V (.H 0 0 6) + V (.E 0 0 (62)))
    (_ : V (.H 0 0 6) = 528734635#32)
    (_ : V (.KW 0 1 0) = k0) :
    E.eval env (.add (.add (.var (.n 10)) (.const 2773480762)) (.add (.add (.var (.n 24)) (.const 1541459225)) (.add (.add (.xor (.and (.xor (.add (.var (.n 20)) (.const 2600822924)) (.add (.var (.n 22)) (.const 528734635))) (.add (.var (.n 18)) (.const 1359893119))) (.add (.var (.n 22)) (.const 528734635))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.add (.var (.n 18)) (.const 1359893119)) 18) (.shr (.add (.var (.n 18)) (.const 1359893119)) 14)) (.add (.var (.n 18)) (.const 1359893119))) 27) (.shr (.xor (.or (.shl (.add (.var (.n 18)) (.const 1359893119)) 18) (.shr (.add (.var (.n 18)) (.const 1359893119)) 14)) (.add (.var (.n 18)) (.const 1359893119))) 5)) (.add (.var (.n 18)) (.const 1359893119))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.add (.var (.n 18)) (.const 1359893119)) 18) (.shr (.add (.var (.n 18)) (.const 1359893119)) 14)) (.add (.var (.n 18)) (.const 1359893119))) 27) (.shr (.xor (.or (.shl (.add (.var (.n 18)) (.const 1359893119)) 18) (.shr (.add (.var (.n 18)) (.const 1359893119)) 14)) (.add (.var (.n 18)) (.const 1359893119))) 5)) (.add (.var (.n 18)) (.const 1359893119))) 6))) (.const k0)))) = V (.E 0 1 (1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (62))))
    (_ : V (.A 0 1 (-2)) = V (.H 0 1 2))
    (_ : V (.H 0 1 2) = V (.H 0 0 2) + V (.A 0 0 (62)))
    (_ : V (.H 0 0 2) = 1013904242#32) :
    E.eval env (.add (.var (.n 14)) (.const 1013904242)) = V (.A 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (64))))
    (_ : V (.E 0 1 (0)) = V (.H 0 1 4))
    (_ : V (.H 0 1 4) = V (.H 0 0 4) + V (.E 0 0 (64)))
    (_ : V (.H 0 0 4) = 1359893119#32) :
    E.eval env (.add (.var (.n 18)) (.const 1359893119)) = V (.E 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (63))))
    (_ : V (.E 0 1 (-1)) = V (.H 0 1 5))
    (_ : V (.H 0 1 5) = V (.H 0 0 5) + V (.E 0 0 (63)))
    (_ : V (.H 0 0 5) = 2600822924#32) :
    E.eval env (.add (.var (.n 20)) (.const 2600822924)) = V (.E 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : V (.E 0 1 (-2)) = V (.H 0 1 6))
    (_ : V (.H 0 1 6) = V (.H 0 0 6) + V (.E 0 0 (62)))
    (_ : V (.H 0 0 6) = 528734635#32) :
    E.eval env (.add (.var (.n 22)) (.const 528734635)) = V (.E 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32) (k0 : W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (63))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (64))))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (64))))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (62))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (63))))
    (_ : V (.A 0 1 (1)) = (V (.E 0 1 (-3)) + Sigma1 (V (.E 0 1 (0))) + Ch (V (.E 0 1 (0))) (V (.E 0 1 (-1))) (V (.E 0 1 (-2))) + V (.KW 0 1 0)) + (Sigma0 (V (.A 0 1 (0))) + Maj (V (.A 0 1 (0))) (V (.A 0 1 (-1))) (V (.A 0 1 (-2)))))
    (_ : V (.E 0 1 (-3)) = V (.H 0 1 7))
    (_ : V (.H 0 1 7) = V (.H 0 0 7) + V (.E 0 0 (61)))
    (_ : V (.H 0 0 7) = 1541459225#32)
    (_ : V (.E 0 1 (0)) = V (.H 0 1 4))
    (_ : V (.H 0 1 4) = V (.H 0 0 4) + V (.E 0 0 (64)))
    (_ : V (.H 0 0 4) = 1359893119#32)
    (_ : V (.E 0 1 (-1)) = V (.H 0 1 5))
    (_ : V (.H 0 1 5) = V (.H 0 0 5) + V (.E 0 0 (63)))
    (_ : V (.H 0 0 5) = 2600822924#32)
    (_ : V (.E 0 1 (-2)) = V (.H 0 1 6))
    (_ : V (.H 0 1 6) = V (.H 0 0 6) + V (.E 0 0 (62)))
    (_ : V (.H 0 0 6) = 528734635#32)
    (_ : V (.KW 0 1 0) = k0)
    (_ : V (.A 0 1 (0)) = V (.H 0 1 0))
    (_ : V (.H 0 1 0) = V (.H 0 0 0) + V (.A 0 0 (64)))
    (_ : V (.H 0 0 0) = 1779033703#32)
    (_ : V (.A 0 1 (-1)) = V (.H 0 1 1))
    (_ : V (.H 0 1 1) = V (.H 0 0 1) + V (.A 0 0 (63)))
    (_ : V (.H 0 0 1) = 3144134277#32)
    (_ : V (.A 0 1 (-2)) = V (.H 0 1 2))
    (_ : V (.H 0 1 2) = V (.H 0 0 2) + V (.A 0 0 (62)))
    (_ : V (.H 0 0 2) = 1013904242#32) :
    E.eval env (.add (.add (.add (.add (.var (.n 24)) (.const 1541459225)) (.add (.add (.xor (.and (.xor (.add (.var (.n 20)) (.const 2600822924)) (.add (.var (.n 22)) (.const 528734635))) (.add (.var (.n 18)) (.const 1359893119))) (.add (.var (.n 22)) (.const 528734635))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.add (.var (.n 18)) (.const 1359893119)) 18) (.shr (.add (.var (.n 18)) (.const 1359893119)) 14)) (.add (.var (.n 18)) (.const 1359893119))) 27) (.shr (.xor (.or (.shl (.add (.var (.n 18)) (.const 1359893119)) 18) (.shr (.add (.var (.n 18)) (.const 1359893119)) 14)) (.add (.var (.n 18)) (.const 1359893119))) 5)) (.add (.var (.n 18)) (.const 1359893119))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.add (.var (.n 18)) (.const 1359893119)) 18) (.shr (.add (.var (.n 18)) (.const 1359893119)) 14)) (.add (.var (.n 18)) (.const 1359893119))) 27) (.shr (.xor (.or (.shl (.add (.var (.n 18)) (.const 1359893119)) 18) (.shr (.add (.var (.n 18)) (.const 1359893119)) 14)) (.add (.var (.n 18)) (.const 1359893119))) 5)) (.add (.var (.n 18)) (.const 1359893119))) 6))) (.const k0))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.add (.var (.n 0)) (.const 1779033703)) 23) (.shr (.add (.var (.n 0)) (.const 1779033703)) 9)) (.add (.var (.n 0)) (.const 1779033703))) 21) (.shr (.xor (.or (.shl (.add (.var (.n 0)) (.const 1779033703)) 23) (.shr (.add (.var (.n 0)) (.const 1779033703)) 9)) (.add (.var (.n 0)) (.const 1779033703))) 11)) (.add (.var (.n 0)) (.const 1779033703))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.add (.var (.n 0)) (.const 1779033703)) 23) (.shr (.add (.var (.n 0)) (.const 1779033703)) 9)) (.add (.var (.n 0)) (.const 1779033703))) 21) (.shr (.xor (.or (.shl (.add (.var (.n 0)) (.const 1779033703)) 23) (.shr (.add (.var (.n 0)) (.const 1779033703)) 9)) (.add (.var (.n 0)) (.const 1779033703))) 11)) (.add (.var (.n 0)) (.const 1779033703))) 2))) (.or (.and (.or (.add (.var (.n 0)) (.const 1779033703)) (.add (.var (.n 14)) (.const 1013904242))) (.add (.var (.n 6)) (.const 3144134277))) (.and (.add (.var (.n 0)) (.const 1779033703)) (.add (.var (.n 14)) (.const 1013904242))))) = V (.A 0 1 (1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : V (.E 0 1 (-3)) = V (.H 0 1 7))
    (_ : V (.H 0 1 7) = V (.H 0 0 7) + V (.E 0 0 (61)))
    (_ : V (.H 0 0 7) = 1541459225#32) :
    E.eval env (.add (.var (.n 24)) (.const 1541459225)) = V (.E 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : V (.E 0 1 (-3)) = V (.H 0 1 7))
    (_ : V (.H 0 1 7) = V (.H 0 0 7) + V (.E 0 0 (61)))
    (_ : V (.H 0 0 7) = 1541459225#32) :
    E.eval env (.add (.var (.n 24)) (.const 1541459225)) = V (.E 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : V (.E 0 1 (-3)) = V (.H 0 1 7))
    (_ : V (.H 0 1 7) = V (.H 0 0 7) + V (.E 0 0 (61)))
    (_ : V (.H 0 0 7) = 1541459225#32) :
    E.eval env (.add (.var (.n 24)) (.const 1541459225)) = V (.E 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : V (.E 0 1 (-3)) = V (.H 0 1 7))
    (_ : V (.H 0 1 7) = V (.H 0 0 7) + V (.E 0 0 (61)))
    (_ : V (.H 0 0 7) = 1541459225#32) :
    E.eval env (.add (.var (.n 24)) (.const 1541459225)) = V (.E 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : V (.E 0 1 (-2)) = V (.H 0 1 6))
    (_ : V (.H 0 1 6) = V (.H 0 0 6) + V (.E 0 0 (62)))
    (_ : V (.H 0 0 6) = 528734635#32) :
    E.eval env (.add (.var (.n 22)) (.const 528734635)) = V (.E 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : V (.E 0 1 (-2)) = V (.H 0 1 6))
    (_ : V (.H 0 1 6) = V (.H 0 0 6) + V (.E 0 0 (62)))
    (_ : V (.H 0 0 6) = 528734635#32) :
    E.eval env (.add (.var (.n 22)) (.const 528734635)) = V (.E 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : V (.E 0 1 (-2)) = V (.H 0 1 6))
    (_ : V (.H 0 1 6) = V (.H 0 0 6) + V (.E 0 0 (62)))
    (_ : V (.H 0 0 6) = 528734635#32) :
    E.eval env (.add (.var (.n 22)) (.const 528734635)) = V (.E 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : V (.E 0 1 (-2)) = V (.H 0 1 6))
    (_ : V (.H 0 1 6) = V (.H 0 0 6) + V (.E 0 0 (62)))
    (_ : V (.H 0 0 6) = 528734635#32) :
    E.eval env (.add (.var (.n 22)) (.const 528734635)) = V (.E 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (63))))
    (_ : V (.E 0 1 (-1)) = V (.H 0 1 5))
    (_ : V (.H 0 1 5) = V (.H 0 0 5) + V (.E 0 0 (63)))
    (_ : V (.H 0 0 5) = 2600822924#32) :
    E.eval env (.add (.var (.n 20)) (.const 2600822924)) = V (.E 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (63))))
    (_ : V (.E 0 1 (-1)) = V (.H 0 1 5))
    (_ : V (.H 0 1 5) = V (.H 0 0 5) + V (.E 0 0 (63)))
    (_ : V (.H 0 0 5) = 2600822924#32) :
    E.eval env (.add (.var (.n 20)) (.const 2600822924)) = V (.E 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (63))))
    (_ : V (.E 0 1 (-1)) = V (.H 0 1 5))
    (_ : V (.H 0 1 5) = V (.H 0 0 5) + V (.E 0 0 (63)))
    (_ : V (.H 0 0 5) = 2600822924#32) :
    E.eval env (.add (.var (.n 20)) (.const 2600822924)) = V (.E 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (63))))
    (_ : V (.E 0 1 (-1)) = V (.H 0 1 5))
    (_ : V (.H 0 1 5) = V (.H 0 0 5) + V (.E 0 0 (63)))
    (_ : V (.H 0 0 5) = 2600822924#32) :
    E.eval env (.add (.var (.n 20)) (.const 2600822924)) = V (.E 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1012 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (64))))
    (_ : V (.E 0 1 (0)) = V (.H 0 1 4))
    (_ : V (.H 0 1 4) = V (.H 0 0 4) + V (.E 0 0 (64)))
    (_ : V (.H 0 0 4) = 1359893119#32) :
    E.eval env (.add (.var (.n 18)) (.const 1359893119)) = V (.E 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1013 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (64))))
    (_ : V (.E 0 1 (0)) = V (.H 0 1 4))
    (_ : V (.H 0 1 4) = V (.H 0 0 4) + V (.E 0 0 (64)))
    (_ : V (.H 0 0 4) = 1359893119#32) :
    E.eval env (.add (.var (.n 18)) (.const 1359893119)) = V (.E 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1014 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (64))))
    (_ : V (.E 0 1 (0)) = V (.H 0 1 4))
    (_ : V (.H 0 1 4) = V (.H 0 0 4) + V (.E 0 0 (64)))
    (_ : V (.H 0 0 4) = 1359893119#32) :
    E.eval env (.add (.var (.n 18)) (.const 1359893119)) = V (.E 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1015 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (64))))
    (_ : V (.E 0 1 (0)) = V (.H 0 1 4))
    (_ : V (.H 0 1 4) = V (.H 0 0 4) + V (.E 0 0 (64)))
    (_ : V (.H 0 0 4) = 1359893119#32) :
    E.eval env (.add (.var (.n 18)) (.const 1359893119)) = V (.E 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1016 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (61))))
    (_ : V (.A 0 1 (-3)) = V (.H 0 1 3))
    (_ : V (.H 0 1 3) = V (.H 0 0 3) + V (.A 0 0 (61)))
    (_ : V (.H 0 0 3) = 2773480762#32) :
    E.eval env (.add (.var (.n 10)) (.const 2773480762)) = V (.A 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1017 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (61))))
    (_ : V (.A 0 1 (-3)) = V (.H 0 1 3))
    (_ : V (.H 0 1 3) = V (.H 0 0 3) + V (.A 0 0 (61)))
    (_ : V (.H 0 0 3) = 2773480762#32) :
    E.eval env (.add (.var (.n 10)) (.const 2773480762)) = V (.A 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1018 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (61))))
    (_ : V (.A 0 1 (-3)) = V (.H 0 1 3))
    (_ : V (.H 0 1 3) = V (.H 0 0 3) + V (.A 0 0 (61)))
    (_ : V (.H 0 0 3) = 2773480762#32) :
    E.eval env (.add (.var (.n 10)) (.const 2773480762)) = V (.A 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1019 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (61))))
    (_ : V (.A 0 1 (-3)) = V (.H 0 1 3))
    (_ : V (.H 0 1 3) = V (.H 0 0 3) + V (.A 0 0 (61)))
    (_ : V (.H 0 0 3) = 2773480762#32) :
    E.eval env (.add (.var (.n 10)) (.const 2773480762)) = V (.A 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1020 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (62))))
    (_ : V (.A 0 1 (-2)) = V (.H 0 1 2))
    (_ : V (.H 0 1 2) = V (.H 0 0 2) + V (.A 0 0 (62)))
    (_ : V (.H 0 0 2) = 1013904242#32) :
    E.eval env (.add (.var (.n 14)) (.const 1013904242)) = V (.A 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1021 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (62))))
    (_ : V (.A 0 1 (-2)) = V (.H 0 1 2))
    (_ : V (.H 0 1 2) = V (.H 0 0 2) + V (.A 0 0 (62)))
    (_ : V (.H 0 0 2) = 1013904242#32) :
    E.eval env (.add (.var (.n 14)) (.const 1013904242)) = V (.A 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1022 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (62))))
    (_ : V (.A 0 1 (-2)) = V (.H 0 1 2))
    (_ : V (.H 0 1 2) = V (.H 0 0 2) + V (.A 0 0 (62)))
    (_ : V (.H 0 0 2) = 1013904242#32) :
    E.eval env (.add (.var (.n 14)) (.const 1013904242)) = V (.A 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1023 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (62))))
    (_ : V (.A 0 1 (-2)) = V (.H 0 1 2))
    (_ : V (.H 0 1 2) = V (.H 0 0 2) + V (.A 0 0 (62)))
    (_ : V (.H 0 0 2) = 1013904242#32) :
    E.eval env (.add (.var (.n 14)) (.const 1013904242)) = V (.A 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1024 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (63))))
    (_ : V (.A 0 1 (-1)) = V (.H 0 1 1))
    (_ : V (.H 0 1 1) = V (.H 0 0 1) + V (.A 0 0 (63)))
    (_ : V (.H 0 0 1) = 3144134277#32) :
    E.eval env (.add (.var (.n 6)) (.const 3144134277)) = V (.A 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1025 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (63))))
    (_ : V (.A 0 1 (-1)) = V (.H 0 1 1))
    (_ : V (.H 0 1 1) = V (.H 0 0 1) + V (.A 0 0 (63)))
    (_ : V (.H 0 0 1) = 3144134277#32) :
    E.eval env (.add (.var (.n 6)) (.const 3144134277)) = V (.A 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1026 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (63))))
    (_ : V (.A 0 1 (-1)) = V (.H 0 1 1))
    (_ : V (.H 0 1 1) = V (.H 0 0 1) + V (.A 0 0 (63)))
    (_ : V (.H 0 0 1) = 3144134277#32) :
    E.eval env (.add (.var (.n 6)) (.const 3144134277)) = V (.A 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1027 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (63))))
    (_ : V (.A 0 1 (-1)) = V (.H 0 1 1))
    (_ : V (.H 0 1 1) = V (.H 0 0 1) + V (.A 0 0 (63)))
    (_ : V (.H 0 0 1) = 3144134277#32) :
    E.eval env (.add (.var (.n 6)) (.const 3144134277)) = V (.A 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1028 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (64))))
    (_ : V (.A 0 1 (0)) = V (.H 0 1 0))
    (_ : V (.H 0 1 0) = V (.H 0 0 0) + V (.A 0 0 (64)))
    (_ : V (.H 0 0 0) = 1779033703#32) :
    E.eval env (.add (.var (.n 0)) (.const 1779033703)) = V (.A 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1029 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (64))))
    (_ : V (.A 0 1 (0)) = V (.H 0 1 0))
    (_ : V (.H 0 1 0) = V (.H 0 0 0) + V (.A 0 0 (64)))
    (_ : V (.H 0 0 0) = 1779033703#32) :
    E.eval env (.add (.var (.n 0)) (.const 1779033703)) = V (.A 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1030 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (64))))
    (_ : V (.A 0 1 (0)) = V (.H 0 1 0))
    (_ : V (.H 0 1 0) = V (.H 0 0 0) + V (.A 0 0 (64)))
    (_ : V (.H 0 0 0) = 1779033703#32) :
    E.eval env (.add (.var (.n 0)) (.const 1779033703)) = V (.A 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core64_1031 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (64))))
    (_ : V (.A 0 1 (0)) = V (.H 0 1 0))
    (_ : V (.H 0 1 0) = V (.H 0 0 0) + V (.A 0 0 (64)))
    (_ : V (.H 0 0 0) = 1779033703#32) :
    E.eval env (.add (.var (.n 0)) (.const 1779033703)) = V (.A 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step64 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L64 inp env) (hm : HMem 128 inp env) :
    Inv1 L65 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 48 K64)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 0 (by decide)).trans (core64_0 (qv inp) inp env (inv1_get hI 0 (by decide)) (qA_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succA inp 0 0 0 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)))
  | 1, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 1 (by decide)).trans (core64_6 (qv inp) inp env (inv1_get hI 1 (by decide)) (qA_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succA inp 0 0 1 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)))
  | 2, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 2 (by decide)).trans (core64_10 (qv inp) inp env 3263836056#32 (inv1_get hI 2 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (qE_succI inp 0 1 (0) (by decide)) (qA_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succA inp 0 0 3 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 3).trans (by decide : fld H0 3 = 2773480762#32)) (qE_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succE inp 0 0 7 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succE inp 0 0 4 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succE inp 0 0 5 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succE inp 0 0 6 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW1T inp 0 0 (by decide)).trans rfl))
  | 3, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 3 (by decide)).trans (core64_14 (qv inp) inp env (inv1_get hI 3 (by decide)) (qA_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succA inp 0 0 2 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32)))
  | 4, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 4 (by decide)).trans (core64_18 (qv inp) inp env (inv1_get hI 4 (by decide)) (qE_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succE inp 0 0 4 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)))
  | 5, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 5 (by decide)).trans (core64_20 (qv inp) inp env (inv1_get hI 5 (by decide)) (qE_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succE inp 0 0 5 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)))
  | 6, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 6 (by decide)).trans (core64_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (qE_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succE inp 0 0 6 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)))
  | 7, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 7 (by decide)).trans (core64_24 (qv inp) inp env 3263836056#32 (inv1_get hI 7 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 1 (by decide)) (qA_succI inp 0 1 (0) (by decide)) (qE_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succE inp 0 0 7 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)) (qE_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succE inp 0 0 4 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)) (qE_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succE inp 0 0 5 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)) (qE_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succE inp 0 0 6 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)) ((qKW1T inp 0 0 (by decide)).trans rfl) (qA_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succA inp 0 0 0 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)) (qA_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succA inp 0 0 1 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)) (qA_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succA inp 0 0 2 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32)))
  | 8, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 8 (by decide)).trans (core64_1000 (qv inp) inp env (inv1_get hI 7 (by decide)) (qE_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succE inp 0 0 7 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)))
  | 9, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 9 (by decide)).trans (core64_1001 (qv inp) inp env (inv1_get hI 7 (by decide)) (qE_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succE inp 0 0 7 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)))
  | 10, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 10 (by decide)).trans (core64_1002 (qv inp) inp env (inv1_get hI 7 (by decide)) (qE_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succE inp 0 0 7 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)))
  | 11, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 11 (by decide)).trans (core64_1003 (qv inp) inp env (inv1_get hI 7 (by decide)) (qE_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succE inp 0 0 7 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 7).trans (by decide : fld H0 7 = 1541459225#32)))
  | 12, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 12 (by decide)).trans (core64_1004 (qv inp) inp env (inv1_get hI 6 (by decide)) (qE_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succE inp 0 0 6 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)))
  | 13, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 13 (by decide)).trans (core64_1005 (qv inp) inp env (inv1_get hI 6 (by decide)) (qE_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succE inp 0 0 6 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)))
  | 14, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 14 (by decide)).trans (core64_1006 (qv inp) inp env (inv1_get hI 6 (by decide)) (qE_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succE inp 0 0 6 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)))
  | 15, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 15 (by decide)).trans (core64_1007 (qv inp) inp env (inv1_get hI 6 (by decide)) (qE_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succE inp 0 0 6 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 6).trans (by decide : fld H0 6 = 528734635#32)))
  | 16, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 16 (by decide)).trans (core64_1008 (qv inp) inp env (inv1_get hI 5 (by decide)) (qE_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succE inp 0 0 5 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)))
  | 17, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 17 (by decide)).trans (core64_1009 (qv inp) inp env (inv1_get hI 5 (by decide)) (qE_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succE inp 0 0 5 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)))
  | 18, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 18 (by decide)).trans (core64_1010 (qv inp) inp env (inv1_get hI 5 (by decide)) (qE_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succE inp 0 0 5 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)))
  | 19, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 19 (by decide)).trans (core64_1011 (qv inp) inp env (inv1_get hI 5 (by decide)) (qE_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succE inp 0 0 5 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 5).trans (by decide : fld H0 5 = 2600822924#32)))
  | 20, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 20 (by decide)).trans (core64_1012 (qv inp) inp env (inv1_get hI 4 (by decide)) (qE_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succE inp 0 0 4 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)))
  | 21, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 21 (by decide)).trans (core64_1013 (qv inp) inp env (inv1_get hI 4 (by decide)) (qE_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succE inp 0 0 4 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)))
  | 22, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 22 (by decide)).trans (core64_1014 (qv inp) inp env (inv1_get hI 4 (by decide)) (qE_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succE inp 0 0 4 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)))
  | 23, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 23 (by decide)).trans (core64_1015 (qv inp) inp env (inv1_get hI 4 (by decide)) (qE_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succE inp 0 0 4 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)))
  | 24, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 24 (by decide)).trans (core64_1016 (qv inp) inp env (inv1_get hI 2 (by decide)) (qA_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succA inp 0 0 3 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 3).trans (by decide : fld H0 3 = 2773480762#32)))
  | 25, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 25 (by decide)).trans (core64_1017 (qv inp) inp env (inv1_get hI 2 (by decide)) (qA_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succA inp 0 0 3 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 3).trans (by decide : fld H0 3 = 2773480762#32)))
  | 26, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 26 (by decide)).trans (core64_1018 (qv inp) inp env (inv1_get hI 2 (by decide)) (qA_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succA inp 0 0 3 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 3).trans (by decide : fld H0 3 = 2773480762#32)))
  | 27, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 27 (by decide)).trans (core64_1019 (qv inp) inp env (inv1_get hI 2 (by decide)) (qA_initI inp 0 1 3 (-3) (by decide) (by decide)) (qH_succA inp 0 0 3 (61) (by decide) (by decide) (by decide)) ((qH0 inp 0 3).trans (by decide : fld H0 3 = 2773480762#32)))
  | 28, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 28 (by decide)).trans (core64_1020 (qv inp) inp env (inv1_get hI 3 (by decide)) (qA_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succA inp 0 0 2 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32)))
  | 29, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 29 (by decide)).trans (core64_1021 (qv inp) inp env (inv1_get hI 3 (by decide)) (qA_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succA inp 0 0 2 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32)))
  | 30, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 30 (by decide)).trans (core64_1022 (qv inp) inp env (inv1_get hI 3 (by decide)) (qA_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succA inp 0 0 2 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32)))
  | 31, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 31 (by decide)).trans (core64_1023 (qv inp) inp env (inv1_get hI 3 (by decide)) (qA_initI inp 0 1 2 (-2) (by decide) (by decide)) (qH_succA inp 0 0 2 (62) (by decide) (by decide) (by decide)) ((qH0 inp 0 2).trans (by decide : fld H0 2 = 1013904242#32)))
  | 32, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 32 (by decide)).trans (core64_1024 (qv inp) inp env (inv1_get hI 1 (by decide)) (qA_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succA inp 0 0 1 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)))
  | 33, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 33 (by decide)).trans (core64_1025 (qv inp) inp env (inv1_get hI 1 (by decide)) (qA_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succA inp 0 0 1 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)))
  | 34, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 34 (by decide)).trans (core64_1026 (qv inp) inp env (inv1_get hI 1 (by decide)) (qA_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succA inp 0 0 1 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)))
  | 35, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 35 (by decide)).trans (core64_1027 (qv inp) inp env (inv1_get hI 1 (by decide)) (qA_initI inp 0 1 1 (-1) (by decide) (by decide)) (qH_succA inp 0 0 1 (63) (by decide) (by decide) (by decide)) ((qH0 inp 0 1).trans (by decide : fld H0 1 = 3144134277#32)))
  | 36, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 36 (by decide)).trans (core64_1028 (qv inp) inp env (inv1_get hI 0 (by decide)) (qA_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succA inp 0 0 0 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)))
  | 37, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 37 (by decide)).trans (core64_1029 (qv inp) inp env (inv1_get hI 0 (by decide)) (qA_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succA inp 0 0 0 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)))
  | 38, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 38 (by decide)).trans (core64_1030 (qv inp) inp env (inv1_get hI 0 (by decide)) (qA_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succA inp 0 0 0 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)))
  | 39, _ => exact (slice_trees prog 4 _ _ 48 K64 K65 T64 slice64 env 39 (by decide)).trans (core64_1031 (qv inp) inp env (inv1_get hI 0 (by decide)) (qA_initI inp 0 1 0 (0) (by decide) (by decide)) (qH_succA inp 0 0 0 (64) (by decide) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)))
  | _ + 40, hk => simp only [L65, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It
