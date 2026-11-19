import Hashtree.Gen.WinAvxX1LW.It.D49
import Hashtree.Gen.WinAvxX1LW.It.D48
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It
open Hashtree.Gen.WinAvxX1LW

theorem slice49 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K49 K50 T49 = true := by
  decide +kernel

theorem core49_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (48)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (48)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (47)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (47)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (49)))) :
    E.eval env (.var (.n 10)) = V (.E 0 0 (49)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (46))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (46))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (48))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (47))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (49))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 49)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 49)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 49)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 49)))
    (_ : V (.E 0 0 (50)) = V (.A 0 0 (46)) + (V (.E 0 0 (46)) + Sigma1 (V (.E 0 0 (49))) + Ch (V (.E 0 0 (49))) (V (.E 0 0 (48))) (V (.E 0 0 (47))) + V (.KW 0 0 49))) :
    E.eval env (.add (.var (.n 14)) (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 10))) (.var (.n 20))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 6))) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))))) = V (.E 0 0 (50)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (48)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (48)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (47)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (47)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (46))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (48))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (47))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (49))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 49)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 49)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 49)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 49)))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (49))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (47))))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (48))))
    (_ : V (.A 0 0 (50)) = (V (.E 0 0 (46)) + Sigma1 (V (.E 0 0 (49))) + Ch (V (.E 0 0 (49))) (V (.E 0 0 (48))) (V (.E 0 0 (47))) + V (.KW 0 0 49)) + (Sigma0 (V (.A 0 0 (49))) + Maj (V (.A 0 0 (49))) (V (.A 0 0 (48))) (V (.A 0 0 (47))))) :
    E.eval env (.add (.add (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 10))) (.var (.n 20))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 27) (.shr (.xor (.or (.shl (.var (.n 10)) 18) (.shr (.var (.n 10)) 14)) (.var (.n 10))) 5)) (.var (.n 10))) 6))) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 21) (.shr (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 11)) (.var (.n 24))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 21) (.shr (.xor (.or (.shl (.var (.n 24)) 23) (.shr (.var (.n 24)) 9)) (.var (.n 24))) 11)) (.var (.n 24))) 2))) (.or (.and (.or (.var (.n 24)) (.var (.n 6))) (.var (.n 0))) (.and (.var (.n 24)) (.var (.n 6))))) = V (.A 0 0 (50)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (49)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (49)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 60))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 60) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 61))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 62))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 63))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 51))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 51))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 51))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 51))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 50))) :
    E.eval env (.var (.n 1004)) = V (.KW 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 50))) :
    E.eval env (.var (.n 1005)) = V (.KW 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 50))) :
    E.eval env (.var (.n 1006)) = V (.KW 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core49_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 50))) :
    E.eval env (.var (.n 1007)) = V (.KW 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step49 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L49 inp env) (hm : HMem 128 inp env) :
    Inv1 L50 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K49)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 0 (by decide)).trans (core49_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 1 (by decide)).trans (core49_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 2 (by decide)).trans (core49_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 3 (by decide)).trans (core49_14 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qE_succI inp 0 0 (49) (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 4 (by decide)).trans (core49_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 5 (by decide)).trans (core49_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 6 (by decide)).trans (core49_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (qA_succI inp 0 0 (49) (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 7 (by decide)).trans (core49_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 8 (by decide)).trans (core49_180 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 9 (by decide)).trans (core49_181 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 10 (by decide)).trans (core49_182 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 11 (by decide)).trans (core49_183 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 12 (by decide)).trans (core49_196 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 13 (by decide)).trans (core49_197 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 14 (by decide)).trans (core49_198 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 15 (by decide)).trans (core49_199 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 16 (by decide)).trans (core49_212 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 17 (by decide)).trans (core49_213 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 18 (by decide)).trans (core49_214 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 19 (by decide)).trans (core49_215 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 20 (by decide)).trans (core49_1000 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 21 (by decide)).trans (core49_1001 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 22 (by decide)).trans (core49_1002 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 23 (by decide)).trans (core49_1003 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 24 (by decide)).trans (core49_1004 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 25 (by decide)).trans (core49_1005 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 26 (by decide)).trans (core49_1006 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 28 K49 K50 T49 slice49 env 27 (by decide)).trans (core49_1007 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | _ + 28, hk => simp only [L50, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It
