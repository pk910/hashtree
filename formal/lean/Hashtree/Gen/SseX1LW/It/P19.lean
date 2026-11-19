import Hashtree.Gen.SseX1LW.It.D19
import Hashtree.Gen.SseX1LW.It.D18
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It
open Hashtree.Gen.SseX1LW

theorem slice19 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 37 K19 K20 T19 = true := by
  decide +kernel

theorem core19_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (16))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (16))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (18))))
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (17))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (19))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 19)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 19)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 19)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 19)))
    (_ : V (.E 0 0 (20)) = V (.A 0 0 (16)) + (V (.E 0 0 (16)) + Sigma1 (V (.E 0 0 (19))) + Ch (V (.E 0 0 (19))) (V (.E 0 0 (18))) (V (.E 0 0 (17))) + V (.KW 0 0 19))) :
    E.eval env (.add (.var (.n 0)) (.add (.var (.n 24)) (.add (.add (.xor (.and (.xor (.var (.n 2)) (.var (.n 16))) (.var (.n 6))) (.var (.n 16))) (.ror (.xor (.ror (.xor (.ror (.var (.n 6)) 14) (.var (.n 6))) 5) (.var (.n 6))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))))) = V (.E 0 0 (20)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (18)))) :
    E.eval env (.var (.n 2)) = V (.E 0 0 (18)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (19)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (19)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (17)))) :
    E.eval env (.var (.n 16)) = V (.E 0 0 (17)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (19)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (19)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (18)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (18)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (17)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (17)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (16))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (18))))
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (17))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (19))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 19)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 19)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 19)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 19)))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (19))))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (17))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (18))))
    (_ : V (.A 0 0 (20)) = (V (.E 0 0 (16)) + Sigma1 (V (.E 0 0 (19))) + Ch (V (.E 0 0 (19))) (V (.E 0 0 (18))) (V (.E 0 0 (17))) + V (.KW 0 0 19)) + (Sigma0 (V (.A 0 0 (19))) + Maj (V (.A 0 0 (19))) (V (.A 0 0 (18))) (V (.A 0 0 (17))))) :
    E.eval env (.add (.add (.add (.var (.n 24)) (.add (.add (.xor (.and (.xor (.var (.n 2)) (.var (.n 16))) (.var (.n 6))) (.var (.n 16))) (.ror (.xor (.ror (.xor (.ror (.var (.n 6)) 14) (.var (.n 6))) 5) (.var (.n 6))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 18)) 9) (.var (.n 18))) 11) (.var (.n 18))) 2)) (.or (.and (.or (.var (.n 18)) (.var (.n 22))) (.var (.n 20))) (.and (.var (.n 18)) (.var (.n 22))))) = V (.A 0 0 (20)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.W 0 0 32))) :
    E.eval env (.add (.const 0) (.var (.n 100))) = V (.W 0 0 32) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.W 0 0 33))) :
    E.eval env (.add (.const 0) (.var (.n 101))) = V (.W 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 32)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 32)))
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 18)))
    (_ : V (.W 0 0 34) = sigma1 (V (.W 0 0 32)) + V (.M2 0 0 18)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24))) (.var (.n 102))) = V (.W 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 33)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 33)))
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 19)))
    (_ : V (.W 0 0 35) = sigma1 (V (.W 0 0 33)) + V (.M2 0 0 19)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24))) (.var (.n 103))) = V (.W 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 20) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 24))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 24) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 25))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 25) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 26))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 26) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 27))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 27) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 28))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 28) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 29))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 29) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 30))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core19_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 31))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step19 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L19 inp env) (hm : HMem 128 inp env) :
    Inv1 L20 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 37 K19)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 0 (by decide)).trans (core19_0 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qE_succI inp 0 0 (19) (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 1 (by decide)).trans (core19_2 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 2 (by decide)).trans (core19_6 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 3 (by decide)).trans (core19_16 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 4 (by decide)).trans (core19_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 5 (by decide)).trans (core19_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 6 (by decide)).trans (core19_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 7 (by decide)).trans (core19_24 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 5 (by decide)) (qA_succI inp 0 0 (19) (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 8 (by decide)).trans (core19_164 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 9 (by decide)).trans (core19_165 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 10 (by decide)).trans (core19_166 (qv inp) inp env (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 10 (by decide)) (qW_recM2 inp 0 0 34 (by decide) (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 11 (by decide)).trans (core19_167 (qv inp) inp env (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 11 (by decide)) (qW_recM2 inp 0 0 35 (by decide) (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 12 (by decide)).trans (core19_180 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 13 (by decide)).trans (core19_181 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 14 (by decide)).trans (core19_182 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 15 (by decide)).trans (core19_183 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 16 (by decide)).trans (core19_196 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 17 (by decide)).trans (core19_197 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 18 (by decide)).trans (core19_198 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 19 (by decide)).trans (core19_199 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 20 (by decide)).trans (core19_212 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 21 (by decide)).trans (core19_213 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 22 (by decide)).trans (core19_214 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 37 K19 K20 T19 slice19 env 23 (by decide)).trans (core19_215 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | _ + 24, hk => simp only [L20, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It
