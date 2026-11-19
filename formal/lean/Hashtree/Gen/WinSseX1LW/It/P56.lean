import Hashtree.Gen.WinSseX1LW.It.D56
import Hashtree.Gen.WinSseX1LW.It.D55
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice56 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 32 K56 K57 T56 = true := by
  decide +kernel

theorem core56_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (56)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (56)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (55)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (55)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (53))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (53))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (55))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (54))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (56))))
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56)))
    (_ : V (.E 0 0 (57)) = V (.A 0 0 (53)) + (V (.E 0 0 (53)) + Sigma1 (V (.E 0 0 (56))) + Ch (V (.E 0 0 (56))) (V (.E 0 0 (55))) (V (.E 0 0 (54))) + V (.KW 0 0 56)))
    (_ : V (.KW 0 0 56) = 1955562222#32 + V (.W 0 0 56)) :
    E.eval env (.add (.var (.n 12)) (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.var (.n 196)) (.const 1955562222))))) = V (.E 0 0 (57)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (54)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (54)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (55)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (55)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (54)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (54)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (53))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (55))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (54))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (56))))
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56)))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (56))))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (54))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (55))))
    (_ : V (.A 0 0 (57)) = (V (.E 0 0 (53)) + Sigma1 (V (.E 0 0 (56))) + Ch (V (.E 0 0 (56))) (V (.E 0 0 (55))) (V (.E 0 0 (54))) + V (.KW 0 0 56)) + (Sigma0 (V (.A 0 0 (56))) + Maj (V (.A 0 0 (56))) (V (.A 0 0 (55))) (V (.A 0 0 (54)))))
    (_ : V (.KW 0 0 56) = 1955562222#32 + V (.W 0 0 56)) :
    E.eval env (.add (.add (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.var (.n 196)) (.const 1955562222)))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 9) (.var (.n 0))) 11) (.var (.n 0))) 2)) (.or (.and (.or (.var (.n 0)) (.var (.n 14))) (.var (.n 6))) (.and (.var (.n 0)) (.var (.n 14))))) = V (.A 0 0 (57)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (56)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (56)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 60))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 60) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 61))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 62))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 63))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59)))
    (_ : V (.KW 0 0 59) = 2361852424#32 + V (.W 0 0 59)) :
    E.eval env (.add (.var (.n 199)) (.const 2361852424)) = V (.KW 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59)))
    (_ : V (.KW 0 0 59) = 2361852424#32 + V (.W 0 0 59)) :
    E.eval env (.add (.var (.n 199)) (.const 2361852424)) = V (.KW 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59)))
    (_ : V (.KW 0 0 59) = 2361852424#32 + V (.W 0 0 59)) :
    E.eval env (.add (.var (.n 199)) (.const 2361852424)) = V (.KW 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59)))
    (_ : V (.KW 0 0 59) = 2361852424#32 + V (.W 0 0 59)) :
    E.eval env (.add (.var (.n 199)) (.const 2361852424)) = V (.KW 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58)))
    (_ : V (.KW 0 0 58) = 2227730452#32 + V (.W 0 0 58)) :
    E.eval env (.add (.var (.n 198)) (.const 2227730452)) = V (.KW 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58)))
    (_ : V (.KW 0 0 58) = 2227730452#32 + V (.W 0 0 58)) :
    E.eval env (.add (.var (.n 198)) (.const 2227730452)) = V (.KW 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58)))
    (_ : V (.KW 0 0 58) = 2227730452#32 + V (.W 0 0 58)) :
    E.eval env (.add (.var (.n 198)) (.const 2227730452)) = V (.KW 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58)))
    (_ : V (.KW 0 0 58) = 2227730452#32 + V (.W 0 0 58)) :
    E.eval env (.add (.var (.n 198)) (.const 2227730452)) = V (.KW 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57)))
    (_ : V (.KW 0 0 57) = 2024104815#32 + V (.W 0 0 57)) :
    E.eval env (.add (.var (.n 197)) (.const 2024104815)) = V (.KW 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57)))
    (_ : V (.KW 0 0 57) = 2024104815#32 + V (.W 0 0 57)) :
    E.eval env (.add (.var (.n 197)) (.const 2024104815)) = V (.KW 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57)))
    (_ : V (.KW 0 0 57) = 2024104815#32 + V (.W 0 0 57)) :
    E.eval env (.add (.var (.n 197)) (.const 2024104815)) = V (.KW 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core56_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57)))
    (_ : V (.KW 0 0 57) = 2024104815#32 + V (.W 0 0 57)) :
    E.eval env (.add (.var (.n 197)) (.const 2024104815)) = V (.KW 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step56 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L56 inp env) (hm : HMem 128 inp env) :
    Inv1 L57 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 32 K56)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 0 (by decide)).trans (core56_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 1 (by decide)).trans (core56_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 2 (by decide)).trans (core56_12 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 8 (by decide)) (qE_succI inp 0 0 (56) (by decide)) ((qKW inp 0 0 56).trans (by rw [show Spec.K 56 = 1955562222#32 from by decide])))
  | 3, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 3 (by decide)).trans (core56_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 4 (by decide)).trans (core56_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 5 (by decide)).trans (core56_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 6 (by decide)).trans (core56_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 1 (by decide)) (qA_succI inp 0 0 (56) (by decide)) ((qKW inp 0 0 56).trans (by rw [show Spec.K 56 = 1955562222#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 7 (by decide)).trans (core56_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 8 (by decide)).trans (core56_180 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 9 (by decide)).trans (core56_181 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 10 (by decide)).trans (core56_182 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 11 (by decide)).trans (core56_183 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 12 (by decide)).trans (core56_1000 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 59).trans (by rw [show Spec.K 59 = 2361852424#32 from by decide])))
  | 13, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 13 (by decide)).trans (core56_1001 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 59).trans (by rw [show Spec.K 59 = 2361852424#32 from by decide])))
  | 14, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 14 (by decide)).trans (core56_1002 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 59).trans (by rw [show Spec.K 59 = 2361852424#32 from by decide])))
  | 15, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 15 (by decide)).trans (core56_1003 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 59).trans (by rw [show Spec.K 59 = 2361852424#32 from by decide])))
  | 16, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 16 (by decide)).trans (core56_1004 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 58).trans (by rw [show Spec.K 58 = 2227730452#32 from by decide])))
  | 17, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 17 (by decide)).trans (core56_1005 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 58).trans (by rw [show Spec.K 58 = 2227730452#32 from by decide])))
  | 18, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 18 (by decide)).trans (core56_1006 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 58).trans (by rw [show Spec.K 58 = 2227730452#32 from by decide])))
  | 19, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 19 (by decide)).trans (core56_1007 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 58).trans (by rw [show Spec.K 58 = 2227730452#32 from by decide])))
  | 20, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 20 (by decide)).trans (core56_1008 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 57).trans (by rw [show Spec.K 57 = 2024104815#32 from by decide])))
  | 21, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 21 (by decide)).trans (core56_1009 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 57).trans (by rw [show Spec.K 57 = 2024104815#32 from by decide])))
  | 22, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 22 (by decide)).trans (core56_1010 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 57).trans (by rw [show Spec.K 57 = 2024104815#32 from by decide])))
  | 23, _ => exact (slice_trees prog 4 _ _ 32 K56 K57 T56 slice56 env 23 (by decide)).trans (core56_1011 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 57).trans (by rw [show Spec.K 57 = 2024104815#32 from by decide])))
  | _ + 24, hk => simp only [L57, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
