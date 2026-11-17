import Hashtree.Gen.WinAvxX1LW.It0.D62
import Hashtree.Gen.WinAvxX1LW.It0.D61
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It0
open Hashtree.Gen.WinAvxX1LW

theorem slice62 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K62 K63 T62 = true := by
  decide +kernel

theorem core62_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (60)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (60)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (59))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (60))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 62)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 62)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 62)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 62)))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (62))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (60))))
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (61))))
    (_ : V (.A 0 0 (63)) = (V (.E 0 0 (59)) + Sigma1 (V (.E 0 0 (62))) + Ch (V (.E 0 0 (62))) (V (.E 0 0 (61))) (V (.E 0 0 (60))) + V (.KW 0 0 62)) + (Sigma0 (V (.A 0 0 (62))) + Maj (V (.A 0 0 (62))) (V (.A 0 0 (61))) (V (.A 0 0 (60))))) :
    E.eval env (.add (.add (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 24)) (.var (.n 0))) (.var (.n 22))) (.var (.n 0))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 27) (.shr (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 5)) (.var (.n 22))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 27) (.shr (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 5)) (.var (.n 22))) 6))) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 23) (.shr (.var (.n 14)) 9)) (.var (.n 14))) 21) (.shr (.xor (.or (.shl (.var (.n 14)) 23) (.shr (.var (.n 14)) 9)) (.var (.n 14))) 11)) (.var (.n 14))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 14)) 23) (.shr (.var (.n 14)) 9)) (.var (.n 14))) 21) (.shr (.xor (.or (.shl (.var (.n 14)) 23) (.shr (.var (.n 14)) 9)) (.var (.n 14))) 11)) (.var (.n 14))) 2))) (.or (.and (.or (.var (.n 14)) (.var (.n 18))) (.var (.n 10))) (.and (.var (.n 14)) (.var (.n 18))))) = V (.A 0 0 (63)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.A 0 0 (61)))) :
    E.eval env (.var (.n 10)) = V (.A 0 0 (61)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (62)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (62)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (60)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (60)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (59))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (59))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (60))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 62)))
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 62)))
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 62)))
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 62)))
    (_ : V (.E 0 0 (63)) = V (.A 0 0 (59)) + (V (.E 0 0 (59)) + Sigma1 (V (.E 0 0 (62))) + Ch (V (.E 0 0 (62))) (V (.E 0 0 (61))) (V (.E 0 0 (60))) + V (.KW 0 0 62))) :
    E.eval env (.add (.var (.n 20)) (.add (.var (.n 6)) (.add (.add (.xor (.and (.xor (.var (.n 24)) (.var (.n 0))) (.var (.n 22))) (.var (.n 0))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 27) (.shr (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 5)) (.var (.n 22))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 27) (.shr (.xor (.or (.shl (.var (.n 22)) 18) (.shr (.var (.n 22)) 14)) (.var (.n 22))) 5)) (.var (.n 22))) 6))) (.or (.or (.and (.shr (.var (.n 1007)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1006)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1005)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1004)) 24) (.const 255)) 24)))))) = V (.E 0 0 (63)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (62)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (62)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (61)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (61)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 63))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 63))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 63))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core62_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 63))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step62 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L62 inp env) (hm : HMem 128 inp env) :
    Inv1 L63 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K62)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 0 (by decide)).trans (core62_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 1 (by decide)).trans (core62_6 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 2 (by decide)) (qA_succI inp 0 0 (62) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 2 (by decide)).trans (core62_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 3 (by decide)).trans (core62_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 4 (by decide)).trans (core62_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 5 (by decide)).trans (core62_20 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 12 (by decide)) (qE_succI inp 0 0 (62) (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 6 (by decide)).trans (core62_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 7 (by decide)).trans (core62_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 8 (by decide)).trans (core62_1000 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 9 (by decide)).trans (core62_1001 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 10 (by decide)).trans (core62_1002 (qv inp) inp env (inv1_get hI 10 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 28 K62 K63 T62 slice62 env 11 (by decide)).trans (core62_1003 (qv inp) inp env (inv1_get hI 11 (by decide)))
  | _ + 12, hk => simp only [L63, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It0
