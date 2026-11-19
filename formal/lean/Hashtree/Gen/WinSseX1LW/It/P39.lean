import Hashtree.Gen.WinSseX1LW.It.D39
import Hashtree.Gen.WinSseX1LW.It.D38
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice39 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 37 K39 K40 T39 = true := by
  decide +kernel

theorem core39_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (36))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (38))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (37))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (39))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 39)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 39)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 39)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 39)))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (39))))
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (37))))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (38))))
    (_ : V (.A 0 0 (40)) = (V (.E 0 0 (36)) + Sigma1 (V (.E 0 0 (39))) + Ch (V (.E 0 0 (39))) (V (.E 0 0 (38))) (V (.E 0 0 (37))) + V (.KW 0 0 39)) + (Sigma0 (V (.A 0 0 (39))) + Maj (V (.A 0 0 (39))) (V (.A 0 0 (38))) (V (.A 0 0 (37))))) :
    E.eval env (.add (.add (.add (.var (.n 0)) (.add (.add (.xor (.and (.xor (.var (.n 20)) (.var (.n 22))) (.var (.n 18))) (.var (.n 22))) (.ror (.xor (.ror (.xor (.ror (.var (.n 18)) 14) (.var (.n 18))) 5) (.var (.n 18))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 6)) 9) (.var (.n 6))) 11) (.var (.n 6))) 2)) (.or (.and (.or (.var (.n 6)) (.var (.n 12))) (.var (.n 14))) (.and (.var (.n 6)) (.var (.n 12))))) = V (.A 0 0 (40)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (39)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (39)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (37)))) :
    E.eval env (.var (.n 12)) = V (.A 0 0 (37)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (38)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (38)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (39)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (39)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (38)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (38)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (37)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (37)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (36))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (36))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (38))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (37))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (39))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 39)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 39)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 39)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 39)))
    (_ : V (.E 0 0 (40)) = V (.A 0 0 (36)) + (V (.E 0 0 (36)) + Sigma1 (V (.E 0 0 (39))) + Ch (V (.E 0 0 (39))) (V (.E 0 0 (38))) (V (.E 0 0 (37))) + V (.KW 0 0 39))) :
    E.eval env (.add (.var (.n 24)) (.add (.var (.n 0)) (.add (.add (.xor (.and (.xor (.var (.n 20)) (.var (.n 22))) (.var (.n 18))) (.var (.n 22))) (.ror (.xor (.ror (.xor (.ror (.var (.n 18)) 14) (.var (.n 18))) 5) (.var (.n 18))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))))) = V (.E 0 0 (40)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 48) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.W 0 0 52))) :
    E.eval env (.add (.const 0) (.var (.n 100))) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.W 0 0 53))) :
    E.eval env (.add (.const 0) (.var (.n 101))) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 52)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 52)))
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 38)))
    (_ : V (.W 0 0 54) = sigma1 (V (.W 0 0 52)) + V (.M2 0 0 38)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24))) (.var (.n 102))) = V (.W 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 53)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 53)))
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 39)))
    (_ : V (.W 0 0 55) = sigma1 (V (.W 0 0 53)) + V (.M2 0 0 39)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24))) (.var (.n 103))) = V (.W 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 40) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 44))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 45))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 46))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core39_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 47))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step39 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L39 inp env) (hm : HMem 128 inp env) :
    Inv1 L40 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 37 K39)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 0 (by decide)).trans (core39_0 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 3 (by decide)) (qA_succI inp 0 0 (39) (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 1 (by decide)).trans (core39_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 2 (by decide)).trans (core39_12 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 3 (by decide)).trans (core39_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 4 (by decide)).trans (core39_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 5 (by decide)).trans (core39_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 6 (by decide)).trans (core39_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 7 (by decide)).trans (core39_24 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qE_succI inp 0 0 (39) (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 8 (by decide)).trans (core39_164 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 9 (by decide)).trans (core39_165 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 10 (by decide)).trans (core39_166 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 11 (by decide)).trans (core39_167 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 12 (by decide)).trans (core39_180 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 13 (by decide)).trans (core39_181 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 14 (by decide)).trans (core39_182 (qv inp) inp env (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 10 (by decide)) (qW_recM2 inp 0 0 54 (by decide) (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 15 (by decide)).trans (core39_183 (qv inp) inp env (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 11 (by decide)) (qW_recM2 inp 0 0 55 (by decide) (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 16 (by decide)).trans (core39_196 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 17 (by decide)).trans (core39_197 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 18 (by decide)).trans (core39_198 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 19 (by decide)).trans (core39_199 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 20 (by decide)).trans (core39_212 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 21 (by decide)).trans (core39_213 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 22 (by decide)).trans (core39_214 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 37 K39 K40 T39 slice39 env 23 (by decide)).trans (core39_215 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | _ + 24, hk => simp only [L40, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
