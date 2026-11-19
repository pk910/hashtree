import Hashtree.Gen.SseX1LW.It0.D52
import Hashtree.Gen.SseX1LW.It0.D51
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It0
open Hashtree.Gen.SseX1LW

theorem slice52 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 31 K52 K53 T52 = true := by
  decide +kernel

theorem core52_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (52)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (52)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (50)))) :
    E.eval env (.var (.n 2)) = V (.E 0 0 (50)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (51)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (51)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (49))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (51))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (50))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (52))))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52)))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (52))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (50))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (51))))
    (_ : V (.A 0 0 (53)) = (V (.E 0 0 (49)) + Sigma1 (V (.E 0 0 (52))) + Ch (V (.E 0 0 (52))) (V (.E 0 0 (51))) (V (.E 0 0 (50))) + V (.KW 0 0 52)) + (Sigma0 (V (.A 0 0 (52))) + Maj (V (.A 0 0 (52))) (V (.A 0 0 (51))) (V (.A 0 0 (50)))))
    (_ : V (.KW 0 0 52) = 958139571#32 + V (.W 0 0 52)) :
    E.eval env (.add (.add (.add (.var (.n 16)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 2))) (.var (.n 0))) (.var (.n 2))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 14) (.var (.n 0))) 5) (.var (.n 0))) 6)) (.add (.var (.n 180)) (.const 958139571)))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 9) (.var (.n 24))) 11) (.var (.n 24))) 2)) (.or (.and (.or (.var (.n 24)) (.var (.n 20))) (.var (.n 18))) (.and (.var (.n 24)) (.var (.n 20))))) = V (.A 0 0 (53)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (51)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (51)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (50)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (50)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (49))))
    (_ : env (.n 16) = QE.eval V inp (.q (.E 0 0 (49))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (51))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (50))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (52))))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52)))
    (_ : V (.E 0 0 (53)) = V (.A 0 0 (49)) + (V (.E 0 0 (49)) + Sigma1 (V (.E 0 0 (52))) + Ch (V (.E 0 0 (52))) (V (.E 0 0 (51))) (V (.E 0 0 (50))) + V (.KW 0 0 52)))
    (_ : V (.KW 0 0 52) = 958139571#32 + V (.W 0 0 52)) :
    E.eval env (.add (.var (.n 22)) (.add (.var (.n 16)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 2))) (.var (.n 0))) (.var (.n 2))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 14) (.var (.n 0))) 5) (.var (.n 0))) 6)) (.add (.var (.n 180)) (.const 958139571))))) = V (.E 0 0 (53)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (52)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (52)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 60))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 60) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 61))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 62))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 63))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : V (.KW 0 0 55) = 1747873779#32 + V (.W 0 0 55)) :
    E.eval env (.add (.var (.n 183)) (.const 1747873779)) = V (.KW 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : V (.KW 0 0 55) = 1747873779#32 + V (.W 0 0 55)) :
    E.eval env (.add (.var (.n 183)) (.const 1747873779)) = V (.KW 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : V (.KW 0 0 55) = 1747873779#32 + V (.W 0 0 55)) :
    E.eval env (.add (.var (.n 183)) (.const 1747873779)) = V (.KW 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55)))
    (_ : V (.KW 0 0 55) = 1747873779#32 + V (.W 0 0 55)) :
    E.eval env (.add (.var (.n 183)) (.const 1747873779)) = V (.KW 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : V (.KW 0 0 54) = 1537002063#32 + V (.W 0 0 54)) :
    E.eval env (.add (.var (.n 182)) (.const 1537002063)) = V (.KW 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : V (.KW 0 0 54) = 1537002063#32 + V (.W 0 0 54)) :
    E.eval env (.add (.var (.n 182)) (.const 1537002063)) = V (.KW 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : V (.KW 0 0 54) = 1537002063#32 + V (.W 0 0 54)) :
    E.eval env (.add (.var (.n 182)) (.const 1537002063)) = V (.KW 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54)))
    (_ : V (.KW 0 0 54) = 1537002063#32 + V (.W 0 0 54)) :
    E.eval env (.add (.var (.n 182)) (.const 1537002063)) = V (.KW 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53)))
    (_ : V (.KW 0 0 53) = 1322822218#32 + V (.W 0 0 53)) :
    E.eval env (.add (.var (.n 181)) (.const 1322822218)) = V (.KW 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53)))
    (_ : V (.KW 0 0 53) = 1322822218#32 + V (.W 0 0 53)) :
    E.eval env (.add (.var (.n 181)) (.const 1322822218)) = V (.KW 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53)))
    (_ : V (.KW 0 0 53) = 1322822218#32 + V (.W 0 0 53)) :
    E.eval env (.add (.var (.n 181)) (.const 1322822218)) = V (.KW 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core52_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53)))
    (_ : V (.KW 0 0 53) = 1322822218#32 + V (.W 0 0 53)) :
    E.eval env (.add (.var (.n 181)) (.const 1322822218)) = V (.KW 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step52 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L52 inp env) (hm : HMem 128 inp env) :
    Inv1 L53 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 31 K52)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 0 (by decide)).trans (core52_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 1 (by decide)).trans (core52_2 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 2 (by decide)).trans (core52_6 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 3 (by decide)).trans (core52_16 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 4 (by decide)) (qA_succI inp 0 0 (52) (by decide)) ((qKW inp 0 0 52).trans (by rw [show Spec.K 52 = 958139571#32 from by decide])))
  | 4, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 4 (by decide)).trans (core52_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 5 (by decide)).trans (core52_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 6 (by decide)).trans (core52_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 8 (by decide)) (qE_succI inp 0 0 (52) (by decide)) ((qKW inp 0 0 52).trans (by rw [show Spec.K 52 = 958139571#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 7 (by decide)).trans (core52_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 8 (by decide)).trans (core52_196 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 9 (by decide)).trans (core52_197 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 10 (by decide)).trans (core52_198 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 11 (by decide)).trans (core52_199 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 12 (by decide)).trans (core52_212 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 13 (by decide)).trans (core52_213 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 14 (by decide)).trans (core52_214 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 15 (by decide)).trans (core52_215 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 16 (by decide)).trans (core52_1000 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 55).trans (by rw [show Spec.K 55 = 1747873779#32 from by decide])))
  | 17, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 17 (by decide)).trans (core52_1001 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 55).trans (by rw [show Spec.K 55 = 1747873779#32 from by decide])))
  | 18, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 18 (by decide)).trans (core52_1002 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 55).trans (by rw [show Spec.K 55 = 1747873779#32 from by decide])))
  | 19, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 19 (by decide)).trans (core52_1003 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 55).trans (by rw [show Spec.K 55 = 1747873779#32 from by decide])))
  | 20, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 20 (by decide)).trans (core52_1004 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 54).trans (by rw [show Spec.K 54 = 1537002063#32 from by decide])))
  | 21, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 21 (by decide)).trans (core52_1005 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 54).trans (by rw [show Spec.K 54 = 1537002063#32 from by decide])))
  | 22, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 22 (by decide)).trans (core52_1006 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 54).trans (by rw [show Spec.K 54 = 1537002063#32 from by decide])))
  | 23, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 23 (by decide)).trans (core52_1007 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 54).trans (by rw [show Spec.K 54 = 1537002063#32 from by decide])))
  | 24, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 24 (by decide)).trans (core52_1008 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 53).trans (by rw [show Spec.K 53 = 1322822218#32 from by decide])))
  | 25, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 25 (by decide)).trans (core52_1009 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 53).trans (by rw [show Spec.K 53 = 1322822218#32 from by decide])))
  | 26, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 26 (by decide)).trans (core52_1010 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 53).trans (by rw [show Spec.K 53 = 1322822218#32 from by decide])))
  | 27, _ => exact (slice_trees prog 4 _ _ 31 K52 K53 T52 slice52 env 27 (by decide)).trans (core52_1011 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 53).trans (by rw [show Spec.K 53 = 1322822218#32 from by decide])))
  | _ + 28, hk => simp only [L53, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It0
