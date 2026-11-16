import Hashtree.Gen.WinSseX1LW.It0.D106
import Hashtree.Gen.WinSseX1LW.It0.D105
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It0
open Hashtree.Gen.WinSseX1LW

theorem slice106 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K106 K107 T106 = true := by
  decide +kernel

theorem core106_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 1 (40)))) :
    E.eval env (.var (.n 0)) = V (.A 0 1 (40)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32) (k0 : W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 1 (39))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 1 (39))))
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 1 (41))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 1 (40))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 1 (42))))
    (_ : V (.E 0 1 (43)) = V (.A 0 1 (39)) + (V (.E 0 1 (39)) + Sigma1 (V (.E 0 1 (42))) + Ch (V (.E 0 1 (42))) (V (.E 0 1 (41))) (V (.E 0 1 (40))) + V (.KW 0 1 42)))
    (_ : V (.KW 0 1 42) = k0) :
    E.eval env (.add (.var (.n 6)) (.add (.var (.n 18)) (.add (.add (.xor (.and (.xor (.var (.n 12)) (.var (.n 24))) (.var (.n 14))) (.var (.n 24))) (.ror (.xor (.ror (.xor (.ror (.var (.n 14)) 14) (.var (.n 14))) 5) (.var (.n 14))) 6)) (.const k0)))) = V (.E 0 1 (43)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 1 (41)))) :
    E.eval env (.var (.n 12)) = V (.E 0 1 (41)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 1 (42)))) :
    E.eval env (.var (.n 14)) = V (.E 0 1 (42)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32) (k0 : W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 1 (39))))
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 1 (41))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 1 (40))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 1 (42))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 1 (42))))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 1 (40))))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 1 (41))))
    (_ : V (.A 0 1 (43)) = (V (.E 0 1 (39)) + Sigma1 (V (.E 0 1 (42))) + Ch (V (.E 0 1 (42))) (V (.E 0 1 (41))) (V (.E 0 1 (40))) + V (.KW 0 1 42)) + (Sigma0 (V (.A 0 1 (42))) + Maj (V (.A 0 1 (42))) (V (.A 0 1 (41))) (V (.A 0 1 (40)))))
    (_ : V (.KW 0 1 42) = k0) :
    E.eval env (.add (.add (.add (.var (.n 18)) (.add (.add (.xor (.and (.xor (.var (.n 12)) (.var (.n 24))) (.var (.n 14))) (.var (.n 24))) (.ror (.xor (.ror (.xor (.ror (.var (.n 14)) 14) (.var (.n 14))) 5) (.var (.n 14))) 6)) (.const k0))) (.ror (.xor (.ror (.xor (.ror (.var (.n 20)) 9) (.var (.n 20))) 11) (.var (.n 20))) 2)) (.or (.and (.or (.var (.n 20)) (.var (.n 0))) (.var (.n 22))) (.and (.var (.n 20)) (.var (.n 0))))) = V (.A 0 1 (43)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 1 (42)))) :
    E.eval env (.var (.n 20)) = V (.A 0 1 (42)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 1 (41)))) :
    E.eval env (.var (.n 22)) = V (.A 0 1 (41)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 1 (40)))) :
    E.eval env (.var (.n 24)) = V (.E 0 1 (40)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.E 0 1 (-3)))) :
    E.eval env (.var (.n 1000)) = V (.E 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.E 0 1 (-3)))) :
    E.eval env (.var (.n 1001)) = V (.E 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.E 0 1 (-3)))) :
    E.eval env (.var (.n 1002)) = V (.E 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.E 0 1 (-3)))) :
    E.eval env (.var (.n 1003)) = V (.E 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1004) = QE.eval V inp (.q (.E 0 1 (-2)))) :
    E.eval env (.var (.n 1004)) = V (.E 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1005) = QE.eval V inp (.q (.E 0 1 (-2)))) :
    E.eval env (.var (.n 1005)) = V (.E 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1006) = QE.eval V inp (.q (.E 0 1 (-2)))) :
    E.eval env (.var (.n 1006)) = V (.E 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1007) = QE.eval V inp (.q (.E 0 1 (-2)))) :
    E.eval env (.var (.n 1007)) = V (.E 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1008) = QE.eval V inp (.q (.E 0 1 (-1)))) :
    E.eval env (.var (.n 1008)) = V (.E 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1009) = QE.eval V inp (.q (.E 0 1 (-1)))) :
    E.eval env (.var (.n 1009)) = V (.E 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1010) = QE.eval V inp (.q (.E 0 1 (-1)))) :
    E.eval env (.var (.n 1010)) = V (.E 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1011) = QE.eval V inp (.q (.E 0 1 (-1)))) :
    E.eval env (.var (.n 1011)) = V (.E 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1012 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1012) = QE.eval V inp (.q (.E 0 1 (0)))) :
    E.eval env (.var (.n 1012)) = V (.E 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1013 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1013) = QE.eval V inp (.q (.E 0 1 (0)))) :
    E.eval env (.var (.n 1013)) = V (.E 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1014 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1014) = QE.eval V inp (.q (.E 0 1 (0)))) :
    E.eval env (.var (.n 1014)) = V (.E 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1015 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1015) = QE.eval V inp (.q (.E 0 1 (0)))) :
    E.eval env (.var (.n 1015)) = V (.E 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1016 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1016) = QE.eval V inp (.q (.A 0 1 (-3)))) :
    E.eval env (.var (.n 1016)) = V (.A 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1017 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1017) = QE.eval V inp (.q (.A 0 1 (-3)))) :
    E.eval env (.var (.n 1017)) = V (.A 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1018 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1018) = QE.eval V inp (.q (.A 0 1 (-3)))) :
    E.eval env (.var (.n 1018)) = V (.A 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1019 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1019) = QE.eval V inp (.q (.A 0 1 (-3)))) :
    E.eval env (.var (.n 1019)) = V (.A 0 1 (-3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1020 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1020) = QE.eval V inp (.q (.A 0 1 (-2)))) :
    E.eval env (.var (.n 1020)) = V (.A 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1021 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1021) = QE.eval V inp (.q (.A 0 1 (-2)))) :
    E.eval env (.var (.n 1021)) = V (.A 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1022 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1022) = QE.eval V inp (.q (.A 0 1 (-2)))) :
    E.eval env (.var (.n 1022)) = V (.A 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1023 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1023) = QE.eval V inp (.q (.A 0 1 (-2)))) :
    E.eval env (.var (.n 1023)) = V (.A 0 1 (-2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1024 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1024) = QE.eval V inp (.q (.A 0 1 (-1)))) :
    E.eval env (.var (.n 1024)) = V (.A 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1025 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1025) = QE.eval V inp (.q (.A 0 1 (-1)))) :
    E.eval env (.var (.n 1025)) = V (.A 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1026 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1026) = QE.eval V inp (.q (.A 0 1 (-1)))) :
    E.eval env (.var (.n 1026)) = V (.A 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1027 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1027) = QE.eval V inp (.q (.A 0 1 (-1)))) :
    E.eval env (.var (.n 1027)) = V (.A 0 1 (-1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1028 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1028) = QE.eval V inp (.q (.A 0 1 (0)))) :
    E.eval env (.var (.n 1028)) = V (.A 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1029 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1029) = QE.eval V inp (.q (.A 0 1 (0)))) :
    E.eval env (.var (.n 1029)) = V (.A 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1030 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1030) = QE.eval V inp (.q (.A 0 1 (0)))) :
    E.eval env (.var (.n 1030)) = V (.A 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core106_1031 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1031) = QE.eval V inp (.q (.A 0 1 (0)))) :
    E.eval env (.var (.n 1031)) = V (.A 0 1 (0)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step106 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L106 inp env) (hm : HMem 128 inp env) :
    Inv1 L107 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K106)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 0 (by decide)).trans (core106_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 1 (by decide)).trans (core106_6 (qv inp) inp env 2768759346#32 (inv1_get hI 1 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 3 (by decide)) (qE_succI inp 0 1 (42) (by decide)) ((qKW1T inp 0 42 (by decide)).trans rfl))
  | 2, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 2 (by decide)).trans (core106_12 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 3 (by decide)).trans (core106_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 4 (by decide)).trans (core106_18 (qv inp) inp env 2768759346#32 (inv1_get hI 4 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 6 (by decide)) (qA_succI inp 0 1 (42) (by decide)) ((qKW1T inp 0 42 (by decide)).trans rfl))
  | 5, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 5 (by decide)).trans (core106_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 6 (by decide)).trans (core106_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 7 (by decide)).trans (core106_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 8 (by decide)).trans (core106_1000 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 9 (by decide)).trans (core106_1001 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 10 (by decide)).trans (core106_1002 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 11 (by decide)).trans (core106_1003 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 12 (by decide)).trans (core106_1004 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 13 (by decide)).trans (core106_1005 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 14 (by decide)).trans (core106_1006 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 15 (by decide)).trans (core106_1007 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 16 (by decide)).trans (core106_1008 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 17 (by decide)).trans (core106_1009 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 18 (by decide)).trans (core106_1010 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 19 (by decide)).trans (core106_1011 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 20 (by decide)).trans (core106_1012 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 21 (by decide)).trans (core106_1013 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 22 (by decide)).trans (core106_1014 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 23 (by decide)).trans (core106_1015 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 24 (by decide)).trans (core106_1016 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 25 (by decide)).trans (core106_1017 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 26 (by decide)).trans (core106_1018 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 27 (by decide)).trans (core106_1019 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 28 (by decide)).trans (core106_1020 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 29 (by decide)).trans (core106_1021 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 30 (by decide)).trans (core106_1022 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 31 (by decide)).trans (core106_1023 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 32 (by decide)).trans (core106_1024 (qv inp) inp env (inv1_get hI 32 (by decide)))
  | 33, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 33 (by decide)).trans (core106_1025 (qv inp) inp env (inv1_get hI 33 (by decide)))
  | 34, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 34 (by decide)).trans (core106_1026 (qv inp) inp env (inv1_get hI 34 (by decide)))
  | 35, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 35 (by decide)).trans (core106_1027 (qv inp) inp env (inv1_get hI 35 (by decide)))
  | 36, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 36 (by decide)).trans (core106_1028 (qv inp) inp env (inv1_get hI 36 (by decide)))
  | 37, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 37 (by decide)).trans (core106_1029 (qv inp) inp env (inv1_get hI 37 (by decide)))
  | 38, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 38 (by decide)).trans (core106_1030 (qv inp) inp env (inv1_get hI 38 (by decide)))
  | 39, _ => exact (slice_trees prog 4 _ _ 28 K106 K107 T106 slice106 env 39 (by decide)).trans (core106_1031 (qv inp) inp env (inv1_get hI 39 (by decide)))
  | _ + 40, hk => simp only [L107, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It0
