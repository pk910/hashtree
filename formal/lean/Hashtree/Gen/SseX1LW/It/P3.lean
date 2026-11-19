import Hashtree.Gen.SseX1LW.It.D3
import Hashtree.Gen.SseX1LW.It.D2
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It
open Hashtree.Gen.SseX1LW

theorem slice3 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 37 K3 K4 T3 = true := by
  decide +kernel

theorem core3_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (2))))
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (1))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (3))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 3)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 3)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 3)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 3)))
    (_ : V (.E 0 0 (4)) = V (.A 0 0 (0)) + (V (.E 0 0 (0)) + Sigma1 (V (.E 0 0 (3))) + Ch (V (.E 0 0 (3))) (V (.E 0 0 (2))) (V (.E 0 0 (1))) + V (.KW 0 0 3)))
    (_ : V (.A 0 0 (0)) = V (.H 0 0 0))
    (_ : V (.H 0 0 0) = 1779033703#32)
    (_ : V (.E 0 0 (0)) = V (.H 0 0 4))
    (_ : V (.H 0 0 4) = 1359893119#32) :
    E.eval env (.add (.const 1779033703) (.add (.const 1359893119) (.add (.add (.xor (.and (.xor (.var (.n 2)) (.var (.n 16))) (.var (.n 6))) (.var (.n 16))) (.ror (.xor (.ror (.xor (.ror (.var (.n 6)) 14) (.var (.n 6))) 5) (.var (.n 6))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))))) = V (.E 0 0 (4)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (2)))) :
    E.eval env (.var (.n 2)) = V (.E 0 0 (2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (3)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (1)))) :
    E.eval env (.var (.n 16)) = V (.E 0 0 (1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (3)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (2)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (2)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (1)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (1)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (2))))
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (1))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (3))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 3)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 3)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 3)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 3)))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (3))))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (1))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (2))))
    (_ : V (.A 0 0 (4)) = (V (.E 0 0 (0)) + Sigma1 (V (.E 0 0 (3))) + Ch (V (.E 0 0 (3))) (V (.E 0 0 (2))) (V (.E 0 0 (1))) + V (.KW 0 0 3)) + (Sigma0 (V (.A 0 0 (3))) + Maj (V (.A 0 0 (3))) (V (.A 0 0 (2))) (V (.A 0 0 (1)))))
    (_ : V (.E 0 0 (0)) = V (.H 0 0 4))
    (_ : V (.H 0 0 4) = 1359893119#32) :
    E.eval env (.add (.add (.add (.const 1359893119) (.add (.add (.xor (.and (.xor (.var (.n 2)) (.var (.n 16))) (.var (.n 6))) (.var (.n 16))) (.ror (.xor (.ror (.xor (.ror (.var (.n 6)) 14) (.var (.n 6))) 5) (.var (.n 6))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 18)) 9) (.var (.n 18))) 11) (.var (.n 18))) 2)) (.or (.and (.or (.var (.n 18)) (.var (.n 22))) (.var (.n 20))) (.and (.var (.n 18)) (.var (.n 22))))) = V (.A 0 0 (4)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.W 0 0 16))) :
    E.eval env (.add (.const 0) (.var (.n 100))) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.add (.const 0) (.var (.n 101))) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 16)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 16)))
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 2)))
    (_ : V (.W 0 0 18) = sigma1 (V (.W 0 0 16)) + V (.M2 0 0 2)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24))) (.var (.n 102))) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 17)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 17)))
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 3)))
    (_ : V (.W 0 0 19) = sigma1 (V (.W 0 0 17)) + V (.M2 0 0 3)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24))) (.var (.n 103))) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 4))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 4) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 5))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 6))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 7))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 8) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 12) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 13))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 13) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core3_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step3 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L3 inp env) (hm : HMem 128 inp env) :
    Inv1 L4 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 37 K3)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 0 (by decide)).trans (core3_0 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (inv1_get hI 27 (by decide)) (inv1_get hI 26 (by decide)) (qE_succI inp 0 0 (3) (by decide)) (qA_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 0).trans (by decide : fld H0 0 = 1779033703#32)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)))
  | 1, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 1 (by decide)).trans (core3_2 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 2 (by decide)).trans (core3_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 3 (by decide)).trans (core3_16 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 4 (by decide)).trans (core3_18 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 5 (by decide)).trans (core3_20 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 6 (by decide)).trans (core3_22 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 7 (by decide)).trans (core3_24 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (inv1_get hI 27 (by decide)) (inv1_get hI 26 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 4 (by decide)) (qA_succI inp 0 0 (3) (by decide)) (qE_initI inp 0 0 0 (0) (by decide) (by decide)) ((qH0 inp 0 4).trans (by decide : fld H0 4 = 1359893119#32)))
  | 8, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 8 (by decide)).trans (core3_164 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 9 (by decide)).trans (core3_165 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 10 (by decide)).trans (core3_166 (qv inp) inp env (inv1_get hI 10 (by decide)) (inv1_get hI 11 (by decide)) (inv1_get hI 8 (by decide)) (qW_recM2 inp 0 0 18 (by decide) (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 11 (by decide)).trans (core3_167 (qv inp) inp env (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 9 (by decide)) (qW_recM2 inp 0 0 19 (by decide) (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 12 (by decide)).trans (core3_180 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 13 (by decide)).trans (core3_181 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 14 (by decide)).trans (core3_182 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 15 (by decide)).trans (core3_183 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 16 (by decide)).trans (core3_196 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 17 (by decide)).trans (core3_197 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 18 (by decide)).trans (core3_198 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 19 (by decide)).trans (core3_199 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 20 (by decide)).trans (core3_212 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 21 (by decide)).trans (core3_213 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 22 (by decide)).trans (core3_214 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 37 K3 K4 T3 slice3 env 23 (by decide)).trans (core3_215 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | _ + 24, hk => simp only [L4, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It
