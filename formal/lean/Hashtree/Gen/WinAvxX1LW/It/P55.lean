import Hashtree.Gen.WinAvxX1LW.It.D55
import Hashtree.Gen.WinAvxX1LW.It.D54
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It
open Hashtree.Gen.WinAvxX1LW

theorem slice55 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K55 K56 T55 = true := by
  decide +kernel

theorem core55_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (52))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (54))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (53))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (55))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 55)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 55)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 55)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 55)))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (55))))
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (53))))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (54))))
    (_ : V (.A 0 0 (56)) = (V (.E 0 0 (52)) + Sigma1 (V (.E 0 0 (55))) + Ch (V (.E 0 0 (55))) (V (.E 0 0 (54))) (V (.E 0 0 (53))) + V (.KW 0 0 55)) + (Sigma0 (V (.A 0 0 (55))) + Maj (V (.A 0 0 (55))) (V (.A 0 0 (54))) (V (.A 0 0 (53))))) :
    E.eval env (.add (.add (.add (.var (.n 0)) (.add (.add (.xor (.and (.xor (.var (.n 22)) (.var (.n 24))) (.var (.n 20))) (.var (.n 24))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 20)) 18) (.shr (.var (.n 20)) 14)) (.var (.n 20))) 27) (.shr (.xor (.or (.shl (.var (.n 20)) 18) (.shr (.var (.n 20)) 14)) (.var (.n 20))) 5)) (.var (.n 20))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 20)) 18) (.shr (.var (.n 20)) 14)) (.var (.n 20))) 27) (.shr (.xor (.or (.shl (.var (.n 20)) 18) (.shr (.var (.n 20)) 14)) (.var (.n 20))) 5)) (.var (.n 20))) 6))) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 6)) 23) (.shr (.var (.n 6)) 9)) (.var (.n 6))) 21) (.shr (.xor (.or (.shl (.var (.n 6)) 23) (.shr (.var (.n 6)) 9)) (.var (.n 6))) 11)) (.var (.n 6))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 6)) 23) (.shr (.var (.n 6)) 9)) (.var (.n 6))) 21) (.shr (.xor (.or (.shl (.var (.n 6)) 23) (.shr (.var (.n 6)) 9)) (.var (.n 6))) 11)) (.var (.n 6))) 2))) (.or (.and (.or (.var (.n 6)) (.var (.n 10))) (.var (.n 14))) (.and (.var (.n 6)) (.var (.n 10))))) = V (.A 0 0 (56)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (55)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (55)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (53)))) :
    E.eval env (.var (.n 10)) = V (.A 0 0 (53)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (54)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (54)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (52))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (52))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (54))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (53))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (55))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 55)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 55)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 55)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 55)))
    (_ : V (.E 0 0 (56)) = V (.A 0 0 (52)) + (V (.E 0 0 (52)) + Sigma1 (V (.E 0 0 (55))) + Ch (V (.E 0 0 (55))) (V (.E 0 0 (54))) (V (.E 0 0 (53))) + V (.KW 0 0 55))) :
    E.eval env (.add (.var (.n 18)) (.add (.var (.n 0)) (.add (.add (.xor (.and (.xor (.var (.n 22)) (.var (.n 24))) (.var (.n 20))) (.var (.n 24))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 20)) 18) (.shr (.var (.n 20)) 14)) (.var (.n 20))) 27) (.shr (.xor (.or (.shl (.var (.n 20)) 18) (.shr (.var (.n 20)) 14)) (.var (.n 20))) 5)) (.var (.n 20))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 20)) 18) (.shr (.var (.n 20)) 14)) (.var (.n 20))) 27) (.shr (.xor (.or (.shl (.var (.n 20)) 18) (.shr (.var (.n 20)) 14)) (.var (.n 20))) 5)) (.var (.n 20))) 6))) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))))) = V (.E 0 0 (56)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (55)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (55)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (54)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (54)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (53)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (53)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 60))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 60) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 61))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 62))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core55_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 63))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step55 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L55 inp env) (hm : HMem 128 inp env) :
    Inv1 L56 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K55)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 0 (by decide)).trans (core55_0 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 16 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 3 (by decide)) (qA_succI inp 0 0 (55) (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 1 (by decide)).trans (core55_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 2 (by decide)).trans (core55_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 3 (by decide)).trans (core55_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 4 (by decide)).trans (core55_18 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 16 (by decide)) (qE_succI inp 0 0 (55) (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 5 (by decide)).trans (core55_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 6 (by decide)).trans (core55_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 7 (by decide)).trans (core55_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 8 (by decide)).trans (core55_196 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 9 (by decide)).trans (core55_197 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 10 (by decide)).trans (core55_198 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 11 (by decide)).trans (core55_199 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 12 (by decide)).trans (core55_212 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 13 (by decide)).trans (core55_213 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 14 (by decide)).trans (core55_214 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 28 K55 K56 T55 slice55 env 15 (by decide)).trans (core55_215 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | _ + 16, hk => simp only [L56, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It
