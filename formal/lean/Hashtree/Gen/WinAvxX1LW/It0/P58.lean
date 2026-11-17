import Hashtree.Gen.WinAvxX1LW.It0.D58
import Hashtree.Gen.WinAvxX1LW.It0.D57
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It0
open Hashtree.Gen.WinAvxX1LW

theorem slice58 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K58 K59 T58 = true := by
  decide +kernel

theorem core58_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (56)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (56)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (55))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (55))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (57))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (56))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (58))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 58)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 58)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 58)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 58)))
    (_ : V (.E 0 0 (59)) = V (.A 0 0 (55)) + (V (.E 0 0 (55)) + Sigma1 (V (.E 0 0 (58))) + Ch (V (.E 0 0 (58))) (V (.E 0 0 (57))) (V (.E 0 0 (56))) + V (.KW 0 0 58))) :
    E.eval env (.add (.var (.n 6)) (.add (.var (.n 20)) (.add (.add (.xor (.and (.xor (.var (.n 10)) (.var (.n 18))) (.var (.n 14))) (.var (.n 18))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 27) (.shr (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 5)) (.var (.n 14))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 27) (.shr (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 5)) (.var (.n 14))) 6))) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))))) = V (.E 0 0 (59)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (57)))) :
    E.eval env (.var (.n 10)) = V (.E 0 0 (57)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (58)))) :
    E.eval env (.var (.n 14)) = V (.E 0 0 (58)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (56)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (56)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (55))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (57))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (56))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (58))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 58)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 58)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 58)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 58)))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (58))))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (56))))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (57))))
    (_ : V (.A 0 0 (59)) = (V (.E 0 0 (55)) + Sigma1 (V (.E 0 0 (58))) + Ch (V (.E 0 0 (58))) (V (.E 0 0 (57))) (V (.E 0 0 (56))) + V (.KW 0 0 58)) + (Sigma0 (V (.A 0 0 (58))) + Maj (V (.A 0 0 (58))) (V (.A 0 0 (57))) (V (.A 0 0 (56))))) :
    E.eval env (.add (.add (.add (.var (.n 20)) (.add (.add (.xor (.and (.xor (.var (.n 10)) (.var (.n 18))) (.var (.n 14))) (.var (.n 18))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 27) (.shr (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 5)) (.var (.n 14))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 27) (.shr (.xor (.or (.shl (.var (.n 14)) 18) (.shr (.var (.n 14)) 14)) (.var (.n 14))) 5)) (.var (.n 14))) 6))) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 23) (.shr (.var (.n 22)) 9)) (.var (.n 22))) 21) (.shr (.xor (.or (.shl (.var (.n 22)) 23) (.shr (.var (.n 22)) 9)) (.var (.n 22))) 11)) (.var (.n 22))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 23) (.shr (.var (.n 22)) 9)) (.var (.n 22))) 21) (.shr (.xor (.or (.shl (.var (.n 22)) 23) (.shr (.var (.n 22)) 9)) (.var (.n 22))) 11)) (.var (.n 22))) 2))) (.or (.and (.or (.var (.n 22)) (.var (.n 0))) (.var (.n 24))) (.and (.var (.n 22)) (.var (.n 0))))) = V (.A 0 0 (59)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (58)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (58)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (57)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (57)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 60))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 60) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 61))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 62))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 63))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 59))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 59))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 59))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core58_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 59))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step58 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L58 inp env) (hm : HMem 128 inp env) :
    Inv1 L59 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K58)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 0 (by decide)).trans (core58_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 1 (by decide)).trans (core58_6 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 16 (by decide)) (qE_succI inp 0 0 (58) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 2 (by decide)).trans (core58_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 3 (by decide)).trans (core58_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 4 (by decide)).trans (core58_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 5 (by decide)).trans (core58_20 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 19 (by decide)) (inv1_get hI 18 (by decide)) (inv1_get hI 17 (by decide)) (inv1_get hI 16 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 7 (by decide)) (qA_succI inp 0 0 (58) (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 6 (by decide)).trans (core58_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 7 (by decide)).trans (core58_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 8 (by decide)).trans (core58_180 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 9 (by decide)).trans (core58_181 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 10 (by decide)).trans (core58_182 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 11 (by decide)).trans (core58_183 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 12 (by decide)).trans (core58_1000 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 13 (by decide)).trans (core58_1001 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 14 (by decide)).trans (core58_1002 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 28 K58 K59 T58 slice58 env 15 (by decide)).trans (core58_1003 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | _ + 16, hk => simp only [L59, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It0
