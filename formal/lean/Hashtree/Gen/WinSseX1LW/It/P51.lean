import Hashtree.Gen.WinSseX1LW.It.D51
import Hashtree.Gen.WinSseX1LW.It.D50
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice51 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K51 K52 T51 = true := by
  decide +kernel

theorem core51_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (48))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (48))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (50))))
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (49))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (51))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 51)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 51)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 51)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 51)))
    (_ : V (.E 0 0 (52)) = V (.A 0 0 (48)) + (V (.E 0 0 (48)) + Sigma1 (V (.E 0 0 (51))) + Ch (V (.E 0 0 (51))) (V (.E 0 0 (50))) (V (.E 0 0 (49))) + V (.KW 0 0 51))) :
    E.eval env (.add (.var (.n 0)) (.add (.var (.n 24)) (.add (.add (.xor (.and (.xor (.var (.n 14)) (.var (.n 12))) (.var (.n 6))) (.var (.n 12))) (.ror (.xor (.ror (.xor (.ror (.var (.n 6)) 14) (.var (.n 6))) 5) (.var (.n 6))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))))) = V (.E 0 0 (52)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (51)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (51)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (49)))) :
    E.eval env (.var (.n 12)) = V (.E 0 0 (49)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (50)))) :
    E.eval env (.var (.n 14)) = V (.E 0 0 (50)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (51)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (51)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (50)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (50)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (49)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (49)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (48))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (50))))
    (_ : env (.n 12) = QE.eval V inp (.q (.E 0 0 (49))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (51))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 51)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 51)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 51)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 51)))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (51))))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (49))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (50))))
    (_ : V (.A 0 0 (52)) = (V (.E 0 0 (48)) + Sigma1 (V (.E 0 0 (51))) + Ch (V (.E 0 0 (51))) (V (.E 0 0 (50))) (V (.E 0 0 (49))) + V (.KW 0 0 51)) + (Sigma0 (V (.A 0 0 (51))) + Maj (V (.A 0 0 (51))) (V (.A 0 0 (50))) (V (.A 0 0 (49))))) :
    E.eval env (.add (.add (.add (.var (.n 24)) (.add (.add (.xor (.and (.xor (.var (.n 14)) (.var (.n 12))) (.var (.n 6))) (.var (.n 12))) (.ror (.xor (.ror (.xor (.ror (.var (.n 6)) 14) (.var (.n 6))) 5) (.var (.n 6))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 18)) 9) (.var (.n 18))) 11) (.var (.n 18))) 2)) (.or (.and (.or (.var (.n 18)) (.var (.n 22))) (.var (.n 20))) (.and (.var (.n 18)) (.var (.n 22))))) = V (.A 0 0 (52)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 60))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 60) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 61))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 62))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core51_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 63))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step51 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L51 inp env) (hm : HMem 128 inp env) :
    Inv1 L52 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K51)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 0 (by decide)).trans (core51_0 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 23 (by decide)) (inv1_get hI 22 (by decide)) (inv1_get hI 21 (by decide)) (inv1_get hI 20 (by decide)) (qE_succI inp 0 0 (51) (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 1 (by decide)).trans (core51_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 2 (by decide)).trans (core51_12 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 3 (by decide)).trans (core51_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 4 (by decide)).trans (core51_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 5 (by decide)).trans (core51_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 6 (by decide)).trans (core51_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 7 (by decide)).trans (core51_24 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 23 (by decide)) (inv1_get hI 22 (by decide)) (inv1_get hI 21 (by decide)) (inv1_get hI 20 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 5 (by decide)) (qA_succI inp 0 0 (51) (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 8 (by decide)).trans (core51_180 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 9 (by decide)).trans (core51_181 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 10 (by decide)).trans (core51_182 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 11 (by decide)).trans (core51_183 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 12 (by decide)).trans (core51_196 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 13 (by decide)).trans (core51_197 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 14 (by decide)).trans (core51_198 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 15 (by decide)).trans (core51_199 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 16 (by decide)).trans (core51_212 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 17 (by decide)).trans (core51_213 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 18 (by decide)).trans (core51_214 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 28 K51 K52 T51 slice51 env 19 (by decide)).trans (core51_215 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | _ + 20, hk => simp only [L52, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
