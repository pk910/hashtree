import Hashtree.Gen.WinAvxX1LW.It.D50
import Hashtree.Gen.WinAvxX1LW.It.D49
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It
open Hashtree.Gen.WinAvxX1LW

theorem slice50 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K50 K51 T50 = true := by
  decide +kernel

theorem core50_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (48)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (48)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (47))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (47))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (49))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (48))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (50))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 50)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 50)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 50)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 50)))
    (_ : V (.E 0 0 (51)) = V (.A 0 0 (47)) + (V (.E 0 0 (47)) + Sigma1 (V (.E 0 0 (50))) + Ch (V (.E 0 0 (50))) (V (.E 0 0 (49))) (V (.E 0 0 (48))) + V (.KW 0 0 50))) :
    E.eval env (.add (.var (.n 6)) (.add (.var (.n 20)) (.add (.add (.xor (.and (.xor (.var (.n 10)) (.var (.n 18))) (.var (.n 14))) (.var (.n 18))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 27) (.shr (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 5)) (.var (.n 14))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 27) (.shr (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 5)) (.var (.n 14))) 6))) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))))) = V (.E 0 0 (51)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (49)))) :
    E.eval env (.var (.n 10)) = V (.E 0 0 (49)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (50)))) :
    E.eval env (.var (.n 14)) = V (.E 0 0 (50)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (48)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (48)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (47))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (49))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (48))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (50))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 50)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 50)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 50)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 50)))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (50))))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (48))))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (49))))
    (_ : V (.A 0 0 (51)) = (V (.E 0 0 (47)) + Sigma1 (V (.E 0 0 (50))) + Ch (V (.E 0 0 (50))) (V (.E 0 0 (49))) (V (.E 0 0 (48))) + V (.KW 0 0 50)) + (Sigma0 (V (.A 0 0 (50))) + Maj (V (.A 0 0 (50))) (V (.A 0 0 (49))) (V (.A 0 0 (48))))) :
    E.eval env (.add (.add (.add (.var (.n 20)) (.add (.add (.xor (.and (.xor (.var (.n 10)) (.var (.n 18))) (.var (.n 14))) (.var (.n 18))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 27) (.shr (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 5)) (.var (.n 14))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 27) (.shr (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 5)) (.var (.n 14))) 6))) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 23) (.shr (.var (.n 22)) 9)) (.var (.n 22))) 21) (.shr (.xor (.or (.shl (.var (.n 22)) 23) (.shr (.var (.n 22)) 9)) (.var (.n 22))) 11)) (.var (.n 22))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 23) (.shr (.var (.n 22)) 9)) (.var (.n 22))) 21) (.shr (.xor (.or (.shl (.var (.n 22)) 23) (.shr (.var (.n 22)) 9)) (.var (.n 22))) 11)) (.var (.n 22))) 2))) (.or (.and (.or (.var (.n 22)) (.var (.n 0))) (.var (.n 24))) (.and (.var (.n 22)) (.var (.n 0))))) = V (.A 0 0 (51)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (50)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (50)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (49)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (49)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 60))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 60) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 61))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 62))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 63))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 51))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 51))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 51))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core50_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 51))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step50 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L50 inp env) (hm : HMem 128 inp env) :
    Inv1 L51 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K50)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 0 (by decide)).trans (core50_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 1 (by decide)).trans (core50_6 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 27 (by decide)) (inv1_get hI 26 (by decide)) (inv1_get hI 25 (by decide)) (inv1_get hI 24 (by decide)) (qE_succI inp 0 0 (50) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 2 (by decide)).trans (core50_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 3 (by decide)).trans (core50_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 4 (by decide)).trans (core50_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 5 (by decide)).trans (core50_20 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 27 (by decide)) (inv1_get hI 26 (by decide)) (inv1_get hI 25 (by decide)) (inv1_get hI 24 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 7 (by decide)) (qA_succI inp 0 0 (50) (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 6 (by decide)).trans (core50_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 7 (by decide)).trans (core50_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 8 (by decide)).trans (core50_180 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 9 (by decide)).trans (core50_181 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 10 (by decide)).trans (core50_182 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 11 (by decide)).trans (core50_183 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 12 (by decide)).trans (core50_196 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 13 (by decide)).trans (core50_197 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 14 (by decide)).trans (core50_198 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 15 (by decide)).trans (core50_199 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 16 (by decide)).trans (core50_212 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 17 (by decide)).trans (core50_213 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 18 (by decide)).trans (core50_214 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 19 (by decide)).trans (core50_215 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 20 (by decide)).trans (core50_1000 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 21 (by decide)).trans (core50_1001 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 22 (by decide)).trans (core50_1002 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 28 K50 K51 T50 slice50 env 23 (by decide)).trans (core50_1003 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | _ + 24, hk => simp only [L51, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It
