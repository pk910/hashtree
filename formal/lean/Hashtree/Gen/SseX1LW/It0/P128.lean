import Hashtree.Gen.SseX1LW.It0.D128
import Hashtree.Gen.SseX1LW.It0.D127
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It0
open Hashtree.Gen.SseX1LW

theorem slice128 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 27 K128 K129 T128 = true := by
  decide +kernel

theorem core128_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 1 (61))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1002) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1001) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1000) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : V (.HB 0 7) = bswap (V (.H 0 2 7)))
    (_ : V (.H 0 2 7) = V (.H 0 1 7) + V (.E 0 1 (61)))
    (_ : V (.H 0 1 7) = V (.E 0 1 (-3))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 1 (61))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1002) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1001) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1000) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : V (.HB 0 7) = bswap (V (.H 0 2 7)))
    (_ : V (.H 0 2 7) = V (.H 0 1 7) + V (.E 0 1 (61)))
    (_ : V (.H 0 1 7) = V (.E 0 1 (-3))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 1 (61))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1002) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1001) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1000) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : V (.HB 0 7) = bswap (V (.H 0 2 7)))
    (_ : V (.H 0 2 7) = V (.H 0 1 7) + V (.E 0 1 (61)))
    (_ : V (.H 0 1 7) = V (.E 0 1 (-3))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 1 (61))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1002) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1001) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : env (.n 1000) = QE.eval V inp (.q (.E 0 1 (-3))))
    (_ : V (.HB 0 7) = bswap (V (.H 0 2 7)))
    (_ : V (.H 0 2 7) = V (.H 0 1 7) + V (.E 0 1 (61)))
    (_ : V (.H 0 1 7) = V (.E 0 1 (-3))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 22)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 1 (62))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1006) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1005) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1004) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : V (.HB 0 6) = bswap (V (.H 0 2 6)))
    (_ : V (.H 0 2 6) = V (.H 0 1 6) + V (.E 0 1 (62)))
    (_ : V (.H 0 1 6) = V (.E 0 1 (-2))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 1 (62))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1006) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1005) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1004) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : V (.HB 0 6) = bswap (V (.H 0 2 6)))
    (_ : V (.H 0 2 6) = V (.H 0 1 6) + V (.E 0 1 (62)))
    (_ : V (.H 0 1 6) = V (.E 0 1 (-2))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 1 (62))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1006) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1005) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1004) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : V (.HB 0 6) = bswap (V (.H 0 2 6)))
    (_ : V (.H 0 2 6) = V (.H 0 1 6) + V (.E 0 1 (62)))
    (_ : V (.H 0 1 6) = V (.E 0 1 (-2))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 1 (62))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1006) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1005) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : env (.n 1004) = QE.eval V inp (.q (.E 0 1 (-2))))
    (_ : V (.HB 0 6) = bswap (V (.H 0 2 6)))
    (_ : V (.H 0 2 6) = V (.H 0 1 6) + V (.E 0 1 (62)))
    (_ : V (.H 0 1 6) = V (.E 0 1 (-2))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 20)) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 1 (63))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1010) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1009) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1008) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : V (.HB 0 5) = bswap (V (.H 0 2 5)))
    (_ : V (.H 0 2 5) = V (.H 0 1 5) + V (.E 0 1 (63)))
    (_ : V (.H 0 1 5) = V (.E 0 1 (-1))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 1 (63))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1010) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1009) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1008) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : V (.HB 0 5) = bswap (V (.H 0 2 5)))
    (_ : V (.H 0 2 5) = V (.H 0 1 5) + V (.E 0 1 (63)))
    (_ : V (.H 0 1 5) = V (.E 0 1 (-1))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 1 (63))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1010) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1009) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1008) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : V (.HB 0 5) = bswap (V (.H 0 2 5)))
    (_ : V (.H 0 2 5) = V (.H 0 1 5) + V (.E 0 1 (63)))
    (_ : V (.H 0 1 5) = V (.E 0 1 (-1))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 1 (63))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1010) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1009) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : env (.n 1008) = QE.eval V inp (.q (.E 0 1 (-1))))
    (_ : V (.HB 0 5) = bswap (V (.H 0 2 5)))
    (_ : V (.H 0 2 5) = V (.H 0 1 5) + V (.E 0 1 (63)))
    (_ : V (.H 0 1 5) = V (.E 0 1 (-1))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 18)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1012 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 1 (64))))
    (_ : env (.n 1015) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1014) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1013) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1012) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : V (.HB 0 4) = bswap (V (.H 0 2 4)))
    (_ : V (.H 0 2 4) = V (.H 0 1 4) + V (.E 0 1 (64)))
    (_ : V (.H 0 1 4) = V (.E 0 1 (0))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 4) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1013 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 1 (64))))
    (_ : env (.n 1015) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1014) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1013) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1012) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : V (.HB 0 4) = bswap (V (.H 0 2 4)))
    (_ : V (.H 0 2 4) = V (.H 0 1 4) + V (.E 0 1 (64)))
    (_ : V (.H 0 1 4) = V (.E 0 1 (0))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 4) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1014 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 1 (64))))
    (_ : env (.n 1015) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1014) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1013) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1012) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : V (.HB 0 4) = bswap (V (.H 0 2 4)))
    (_ : V (.H 0 2 4) = V (.H 0 1 4) + V (.E 0 1 (64)))
    (_ : V (.H 0 1 4) = V (.E 0 1 (0))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 4) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1015 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 1 (64))))
    (_ : env (.n 1015) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1014) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1013) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : env (.n 1012) = QE.eval V inp (.q (.E 0 1 (0))))
    (_ : V (.HB 0 4) = bswap (V (.H 0 2 4)))
    (_ : V (.H 0 2 4) = V (.H 0 1 4) + V (.E 0 1 (64)))
    (_ : V (.H 0 1 4) = V (.E 0 1 (0))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 24)) (.or (.or (.and (.shr (.var (.n 1015)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1014)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1013)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1012)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 4) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1016 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 1 (61))))
    (_ : env (.n 1019) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1018) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1017) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1016) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : V (.HB 0 3) = bswap (V (.H 0 2 3)))
    (_ : V (.H 0 2 3) = V (.H 0 1 3) + V (.A 0 1 (61)))
    (_ : V (.H 0 1 3) = V (.A 0 1 (-3))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1017 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 1 (61))))
    (_ : env (.n 1019) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1018) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1017) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1016) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : V (.HB 0 3) = bswap (V (.H 0 2 3)))
    (_ : V (.H 0 2 3) = V (.H 0 1 3) + V (.A 0 1 (61)))
    (_ : V (.H 0 1 3) = V (.A 0 1 (-3))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1018 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 1 (61))))
    (_ : env (.n 1019) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1018) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1017) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1016) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : V (.HB 0 3) = bswap (V (.H 0 2 3)))
    (_ : V (.H 0 2 3) = V (.H 0 1 3) + V (.A 0 1 (61)))
    (_ : V (.H 0 1 3) = V (.A 0 1 (-3))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1019 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 1 (61))))
    (_ : env (.n 1019) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1018) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1017) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : env (.n 1016) = QE.eval V inp (.q (.A 0 1 (-3))))
    (_ : V (.HB 0 3) = bswap (V (.H 0 2 3)))
    (_ : V (.H 0 2 3) = V (.H 0 1 3) + V (.A 0 1 (61)))
    (_ : V (.H 0 1 3) = V (.A 0 1 (-3))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 16)) (.or (.or (.and (.shr (.var (.n 1019)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1018)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1017)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1016)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 3) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1020 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 1 (62))))
    (_ : env (.n 1023) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1022) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1021) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1020) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : V (.HB 0 2) = bswap (V (.H 0 2 2)))
    (_ : V (.H 0 2 2) = V (.H 0 1 2) + V (.A 0 1 (62)))
    (_ : V (.H 0 1 2) = V (.A 0 1 (-2))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1021 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 1 (62))))
    (_ : env (.n 1023) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1022) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1021) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1020) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : V (.HB 0 2) = bswap (V (.H 0 2 2)))
    (_ : V (.H 0 2 2) = V (.H 0 1 2) + V (.A 0 1 (62)))
    (_ : V (.H 0 1 2) = V (.A 0 1 (-2))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1022 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 1 (62))))
    (_ : env (.n 1023) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1022) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1021) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1020) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : V (.HB 0 2) = bswap (V (.H 0 2 2)))
    (_ : V (.H 0 2 2) = V (.H 0 1 2) + V (.A 0 1 (62)))
    (_ : V (.H 0 1 2) = V (.A 0 1 (-2))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1023 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 1 (62))))
    (_ : env (.n 1023) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1022) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1021) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : env (.n 1020) = QE.eval V inp (.q (.A 0 1 (-2))))
    (_ : V (.HB 0 2) = bswap (V (.H 0 2 2)))
    (_ : V (.H 0 2 2) = V (.H 0 1 2) + V (.A 0 1 (62)))
    (_ : V (.H 0 1 2) = V (.A 0 1 (-2))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 2)) (.or (.or (.and (.shr (.var (.n 1023)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1022)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1021)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1020)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 2) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1024 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 1 (63))))
    (_ : env (.n 1027) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1026) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1025) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1024) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : V (.HB 0 1) = bswap (V (.H 0 2 1)))
    (_ : V (.H 0 2 1) = V (.H 0 1 1) + V (.A 0 1 (63)))
    (_ : V (.H 0 1 1) = V (.A 0 1 (-1))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 1) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1025 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 1 (63))))
    (_ : env (.n 1027) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1026) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1025) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1024) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : V (.HB 0 1) = bswap (V (.H 0 2 1)))
    (_ : V (.H 0 2 1) = V (.H 0 1 1) + V (.A 0 1 (63)))
    (_ : V (.H 0 1 1) = V (.A 0 1 (-1))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 1) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1026 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 1 (63))))
    (_ : env (.n 1027) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1026) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1025) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1024) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : V (.HB 0 1) = bswap (V (.H 0 2 1)))
    (_ : V (.H 0 2 1) = V (.H 0 1 1) + V (.A 0 1 (63)))
    (_ : V (.H 0 1 1) = V (.A 0 1 (-1))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 1) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1027 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 1 (63))))
    (_ : env (.n 1027) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1026) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1025) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : env (.n 1024) = QE.eval V inp (.q (.A 0 1 (-1))))
    (_ : V (.HB 0 1) = bswap (V (.H 0 2 1)))
    (_ : V (.H 0 2 1) = V (.H 0 1 1) + V (.A 0 1 (63)))
    (_ : V (.H 0 1 1) = V (.A 0 1 (-1))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 6)) (.or (.or (.and (.shr (.var (.n 1027)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1026)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1025)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1024)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 1) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1028 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 1 (64))))
    (_ : env (.n 1031) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1030) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1029) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1028) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : V (.HB 0 0) = bswap (V (.H 0 2 0)))
    (_ : V (.H 0 2 0) = V (.H 0 1 0) + V (.A 0 1 (64)))
    (_ : V (.H 0 1 0) = V (.A 0 1 (0))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 0) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1029 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 1 (64))))
    (_ : env (.n 1031) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1030) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1029) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1028) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : V (.HB 0 0) = bswap (V (.H 0 2 0)))
    (_ : V (.H 0 2 0) = V (.H 0 1 0) + V (.A 0 1 (64)))
    (_ : V (.H 0 1 0) = V (.A 0 1 (0))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 0) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1030 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 1 (64))))
    (_ : env (.n 1031) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1030) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1029) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1028) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : V (.HB 0 0) = bswap (V (.H 0 2 0)))
    (_ : V (.H 0 2 0) = V (.H 0 1 0) + V (.A 0 1 (64)))
    (_ : V (.H 0 1 0) = V (.A 0 1 (0))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 0) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core128_1031 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 1 (64))))
    (_ : env (.n 1031) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1030) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1029) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : env (.n 1028) = QE.eval V inp (.q (.A 0 1 (0))))
    (_ : V (.HB 0 0) = bswap (V (.H 0 2 0)))
    (_ : V (.H 0 2 0) = V (.H 0 1 0) + V (.A 0 1 (64)))
    (_ : V (.H 0 1 0) = V (.A 0 1 (0))) :
    E.eval env (.or (.or (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 24) (.const 255)) (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 16) (.const 255)) 8)) (.or (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 8) (.const 255)) 16) (.shl (.and (.shr (.add (.var (.n 0)) (.or (.or (.and (.shr (.var (.n 1031)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1030)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1029)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1028)) 24) (.const 255)) 24)))) 0) (.const 255)) 24))) = V (.HB 0 0) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step128 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L128 inp env) (hm : HMem 128 inp env) :
    Inv1 L129 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 27 K128)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 0 (by decide)).trans (core128_1000 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 11 (by decide)) (inv1_get hI 10 (by decide)) (inv1_get hI 9 (by decide)) (inv1_get hI 8 (by decide)) (qHB inp 0 7) (qH_succE inp 0 1 7 (61) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 3 (-3) (by decide) (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 1 (by decide)).trans (core128_1001 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 11 (by decide)) (inv1_get hI 10 (by decide)) (inv1_get hI 9 (by decide)) (inv1_get hI 8 (by decide)) (qHB inp 0 7) (qH_succE inp 0 1 7 (61) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 3 (-3) (by decide) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 2 (by decide)).trans (core128_1002 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 11 (by decide)) (inv1_get hI 10 (by decide)) (inv1_get hI 9 (by decide)) (inv1_get hI 8 (by decide)) (qHB inp 0 7) (qH_succE inp 0 1 7 (61) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 3 (-3) (by decide) (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 3 (by decide)).trans (core128_1003 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 11 (by decide)) (inv1_get hI 10 (by decide)) (inv1_get hI 9 (by decide)) (inv1_get hI 8 (by decide)) (qHB inp 0 7) (qH_succE inp 0 1 7 (61) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 3 (-3) (by decide) (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 4 (by decide)).trans (core128_1004 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 12 (by decide)) (qHB inp 0 6) (qH_succE inp 0 1 6 (62) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 2 (-2) (by decide) (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 5 (by decide)).trans (core128_1005 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 12 (by decide)) (qHB inp 0 6) (qH_succE inp 0 1 6 (62) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 2 (-2) (by decide) (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 6 (by decide)).trans (core128_1006 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 12 (by decide)) (qHB inp 0 6) (qH_succE inp 0 1 6 (62) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 2 (-2) (by decide) (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 7 (by decide)).trans (core128_1007 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 12 (by decide)) (qHB inp 0 6) (qH_succE inp 0 1 6 (62) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 2 (-2) (by decide) (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 8 (by decide)).trans (core128_1008 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 16 (by decide)) (qHB inp 0 5) (qH_succE inp 0 1 5 (63) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 1 (-1) (by decide) (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 9 (by decide)).trans (core128_1009 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 16 (by decide)) (qHB inp 0 5) (qH_succE inp 0 1 5 (63) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 1 (-1) (by decide) (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 10 (by decide)).trans (core128_1010 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 16 (by decide)) (qHB inp 0 5) (qH_succE inp 0 1 5 (63) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 1 (-1) (by decide) (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 11 (by decide)).trans (core128_1011 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 16 (by decide)) (qHB inp 0 5) (qH_succE inp 0 1 5 (63) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 1 (-1) (by decide) (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 12 (by decide)).trans (core128_1012 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 23 (by decide)) (inv1_get hI 22 (by decide)) (inv1_get hI 21 (by decide)) (inv1_get hI 20 (by decide)) (qHB inp 0 4) (qH_succE inp 0 1 4 (64) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 0 (0) (by decide) (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 13 (by decide)).trans (core128_1013 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 23 (by decide)) (inv1_get hI 22 (by decide)) (inv1_get hI 21 (by decide)) (inv1_get hI 20 (by decide)) (qHB inp 0 4) (qH_succE inp 0 1 4 (64) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 0 (0) (by decide) (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 14 (by decide)).trans (core128_1014 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 23 (by decide)) (inv1_get hI 22 (by decide)) (inv1_get hI 21 (by decide)) (inv1_get hI 20 (by decide)) (qHB inp 0 4) (qH_succE inp 0 1 4 (64) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 0 (0) (by decide) (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 15 (by decide)).trans (core128_1015 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 23 (by decide)) (inv1_get hI 22 (by decide)) (inv1_get hI 21 (by decide)) (inv1_get hI 20 (by decide)) (qHB inp 0 4) (qH_succE inp 0 1 4 (64) (by decide) (by decide) (by decide)) (qH_ofE inp 0 1 0 (0) (by decide) (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 16 (by decide)).trans (core128_1016 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 27 (by decide)) (inv1_get hI 26 (by decide)) (inv1_get hI 25 (by decide)) (inv1_get hI 24 (by decide)) (qHB inp 0 3) (qH_succA inp 0 1 3 (61) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 3 (-3) (by decide) (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 17 (by decide)).trans (core128_1017 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 27 (by decide)) (inv1_get hI 26 (by decide)) (inv1_get hI 25 (by decide)) (inv1_get hI 24 (by decide)) (qHB inp 0 3) (qH_succA inp 0 1 3 (61) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 3 (-3) (by decide) (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 18 (by decide)).trans (core128_1018 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 27 (by decide)) (inv1_get hI 26 (by decide)) (inv1_get hI 25 (by decide)) (inv1_get hI 24 (by decide)) (qHB inp 0 3) (qH_succA inp 0 1 3 (61) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 3 (-3) (by decide) (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 19 (by decide)).trans (core128_1019 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 27 (by decide)) (inv1_get hI 26 (by decide)) (inv1_get hI 25 (by decide)) (inv1_get hI 24 (by decide)) (qHB inp 0 3) (qH_succA inp 0 1 3 (61) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 3 (-3) (by decide) (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 20 (by decide)).trans (core128_1020 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qHB inp 0 2) (qH_succA inp 0 1 2 (62) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 2 (-2) (by decide) (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 21 (by decide)).trans (core128_1021 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qHB inp 0 2) (qH_succA inp 0 1 2 (62) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 2 (-2) (by decide) (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 22 (by decide)).trans (core128_1022 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qHB inp 0 2) (qH_succA inp 0 1 2 (62) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 2 (-2) (by decide) (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 23 (by decide)).trans (core128_1023 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qHB inp 0 2) (qH_succA inp 0 1 2 (62) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 2 (-2) (by decide) (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 24 (by decide)).trans (core128_1024 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (qHB inp 0 1) (qH_succA inp 0 1 1 (63) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 1 (-1) (by decide) (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 25 (by decide)).trans (core128_1025 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (qHB inp 0 1) (qH_succA inp 0 1 1 (63) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 1 (-1) (by decide) (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 26 (by decide)).trans (core128_1026 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (qHB inp 0 1) (qH_succA inp 0 1 1 (63) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 1 (-1) (by decide) (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 27 (by decide)).trans (core128_1027 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 35 (by decide)) (inv1_get hI 34 (by decide)) (inv1_get hI 33 (by decide)) (inv1_get hI 32 (by decide)) (qHB inp 0 1) (qH_succA inp 0 1 1 (63) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 1 (-1) (by decide) (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 28 (by decide)).trans (core128_1028 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 39 (by decide)) (inv1_get hI 38 (by decide)) (inv1_get hI 37 (by decide)) (inv1_get hI 36 (by decide)) (qHB inp 0 0) (qH_succA inp 0 1 0 (64) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 0 (0) (by decide) (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 29 (by decide)).trans (core128_1029 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 39 (by decide)) (inv1_get hI 38 (by decide)) (inv1_get hI 37 (by decide)) (inv1_get hI 36 (by decide)) (qHB inp 0 0) (qH_succA inp 0 1 0 (64) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 0 (0) (by decide) (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 30 (by decide)).trans (core128_1030 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 39 (by decide)) (inv1_get hI 38 (by decide)) (inv1_get hI 37 (by decide)) (inv1_get hI 36 (by decide)) (qHB inp 0 0) (qH_succA inp 0 1 0 (64) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 0 (0) (by decide) (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 27 K128 K129 T128 slice128 env 31 (by decide)).trans (core128_1031 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 39 (by decide)) (inv1_get hI 38 (by decide)) (inv1_get hI 37 (by decide)) (inv1_get hI 36 (by decide)) (qHB inp 0 0) (qH_succA inp 0 1 0 (64) (by decide) (by decide) (by decide)) (qH_ofA inp 0 1 0 (0) (by decide) (by decide)))
  | _ + 32, hk => simp only [L129, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It0
