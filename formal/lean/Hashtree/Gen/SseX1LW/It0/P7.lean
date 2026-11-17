import Hashtree.Gen.SseX1LW.It0.D7
import Hashtree.Gen.SseX1LW.It0.D6
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It0
open Hashtree.Gen.SseX1LW

theorem slice7 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 37 K7 K8 T7 = true := by
  decide +kernel

theorem core7_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (4))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (6))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (5))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (7))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 7)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 7)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 7)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 7)))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (7))))
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 0 (5))))
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 0 (6))))
    (_ : V (.A 0 0 (8)) = (V (.E 0 0 (4)) + Sigma1 (V (.E 0 0 (7))) + Ch (V (.E 0 0 (7))) (V (.E 0 0 (6))) (V (.E 0 0 (5))) + V (.KW 0 0 7)) + (Sigma0 (V (.A 0 0 (7))) + Maj (V (.A 0 0 (7))) (V (.A 0 0 (6))) (V (.A 0 0 (5))))) :
    E.eval env (.add (.add (.add (.var (.n 0)) (.add (.add (.xor (.and (.xor (.var (.n 20)) (.var (.n 22))) (.var (.n 18))) (.var (.n 22))) (.ror (.xor (.ror (.xor (.ror (.var (.n 18)) 14) (.var (.n 18))) 5) (.var (.n 18))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 6)) 9) (.var (.n 6))) 11) (.var (.n 6))) 2)) (.or (.and (.or (.var (.n 6)) (.var (.n 16))) (.var (.n 2))) (.and (.var (.n 6)) (.var (.n 16))))) = V (.A 0 0 (8)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 0 (6)))) :
    E.eval env (.var (.n 2)) = V (.A 0 0 (6)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (7)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (7)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 0 (5)))) :
    E.eval env (.var (.n 16)) = V (.A 0 0 (5)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (7)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (7)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (6)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (6)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (5)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (5)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (4))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (4))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (6))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (5))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (7))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 7)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 7)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 7)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 7)))
    (_ : V (.E 0 0 (8)) = V (.A 0 0 (4)) + (V (.E 0 0 (4)) + Sigma1 (V (.E 0 0 (7))) + Ch (V (.E 0 0 (7))) (V (.E 0 0 (6))) (V (.E 0 0 (5))) + V (.KW 0 0 7))) :
    E.eval env (.add (.var (.n 24)) (.add (.var (.n 0)) (.add (.add (.xor (.and (.xor (.var (.n 20)) (.var (.n 22))) (.var (.n 18))) (.var (.n 22))) (.ror (.xor (.ror (.xor (.ror (.var (.n 18)) 14) (.var (.n 18))) 5) (.var (.n 18))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))))) = V (.E 0 0 (8)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.add (.const 0) (.var (.n 100))) = V (.W 0 0 20) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.add (.const 0) (.var (.n 101))) = V (.W 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 20)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 20)))
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 6)))
    (_ : V (.W 0 0 22) = sigma1 (V (.W 0 0 20)) + V (.M2 0 0 6)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24))) (.var (.n 102))) = V (.W 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 21)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 21)))
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 7)))
    (_ : V (.W 0 0 23) = sigma1 (V (.W 0 0 21)) + V (.M2 0 0 7)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24))) (.var (.n 103))) = V (.W 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 8) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 12) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 13))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 13) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core7_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step7 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L7 inp env) (hm : HMem 128 inp env) :
    Inv1 L8 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 37 K7)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 0 (by decide)).trans (core7_0 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 1 (by decide)) (qA_succI inp 0 0 (7) (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 1 (by decide)).trans (core7_2 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 2 (by decide)).trans (core7_6 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 3 (by decide)).trans (core7_16 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 4 (by decide)).trans (core7_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 5 (by decide)).trans (core7_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 6 (by decide)).trans (core7_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 7 (by decide)).trans (core7_24 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qE_succI inp 0 0 (7) (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 8 (by decide)).trans (core7_164 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 9 (by decide)).trans (core7_165 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 10 (by decide)).trans (core7_166 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 11 (by decide)).trans (core7_167 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 12 (by decide)).trans (core7_180 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 13 (by decide)).trans (core7_181 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 14 (by decide)).trans (core7_182 (qv inp) inp env (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 10 (by decide)) (qW_recM2 inp 0 0 22 (by decide) (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 15 (by decide)).trans (core7_183 (qv inp) inp env (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 11 (by decide)) (qW_recM2 inp 0 0 23 (by decide) (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 16 (by decide)).trans (core7_196 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 17 (by decide)).trans (core7_197 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 18 (by decide)).trans (core7_198 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 19 (by decide)).trans (core7_199 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 20 (by decide)).trans (core7_212 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 21 (by decide)).trans (core7_213 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 22 (by decide)).trans (core7_214 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 37 K7 K8 T7 slice7 env 23 (by decide)).trans (core7_215 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | _ + 24, hk => simp only [L8, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It0
