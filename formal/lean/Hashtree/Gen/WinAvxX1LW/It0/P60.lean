import Hashtree.Gen.WinAvxX1LW.It0.D60
import Hashtree.Gen.WinAvxX1LW.It0.D59
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It0
open Hashtree.Gen.WinAvxX1LW

theorem slice60 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 31 K60 K61 T60 = true := by
  decide +kernel

theorem core60_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (60)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (60)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (59)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (59)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (57))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (59))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (58))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (60))))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 60)))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (60))))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (58))))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (59))))
    (_ : V (.A 0 0 (61)) = (V (.E 0 0 (57)) + Sigma1 (V (.E 0 0 (60))) + Ch (V (.E 0 0 (60))) (V (.E 0 0 (59))) (V (.E 0 0 (58))) + V (.KW 0 0 60)) + (Sigma0 (V (.A 0 0 (60))) + Maj (V (.A 0 0 (60))) (V (.A 0 0 (59))) (V (.A 0 0 (58)))))
    (_ : V (.KW 0 0 60) = 2428436474#32 + V (.W 0 0 60)) :
    E.eval env (.add (.add (.add (.var (.n 10)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 14))) (.var (.n 0))) (.var (.n 14))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 0)) 18) (.shr (.var (.n 0)) 14)) (.var (.n 0))) 27) (.shr (.xor (.or (.shl (.var (.n 0)) 18) (.shr (.var (.n 0)) 14)) (.var (.n 0))) 5)) (.var (.n 0))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 0)) 18) (.shr (.var (.n 0)) 14)) (.var (.n 0))) 27) (.shr (.xor (.or (.shl (.var (.n 0)) 18) (.shr (.var (.n 0)) 14)) (.var (.n 0))) 5)) (.var (.n 0))) 6))) (.add (.var (.n 180)) (.const 2428436474)))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 18)) 23) (.shr (.var (.n 18)) 9)) (.var (.n 18))) 21) (.shr (.xor (.or (.shl (.var (.n 18)) 23) (.shr (.var (.n 18)) 9)) (.var (.n 18))) 11)) (.var (.n 18))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 18)) 23) (.shr (.var (.n 18)) 9)) (.var (.n 18))) 21) (.shr (.xor (.or (.shl (.var (.n 18)) 23) (.shr (.var (.n 18)) 9)) (.var (.n 18))) 11)) (.var (.n 18))) 2))) (.or (.and (.or (.var (.n 18)) (.var (.n 22))) (.var (.n 20))) (.and (.var (.n 18)) (.var (.n 22))))) = V (.A 0 0 (61)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (58)))) :
    E.eval env (.var (.n 14)) = V (.E 0 0 (58)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (60)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (60)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (59)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (59)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (58)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (58)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (57))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (57))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (59))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (58))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (60))))
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 60)))
    (_ : V (.E 0 0 (61)) = V (.A 0 0 (57)) + (V (.E 0 0 (57)) + Sigma1 (V (.E 0 0 (60))) + Ch (V (.E 0 0 (60))) (V (.E 0 0 (59))) (V (.E 0 0 (58))) + V (.KW 0 0 60)))
    (_ : V (.KW 0 0 60) = 2428436474#32 + V (.W 0 0 60)) :
    E.eval env (.add (.var (.n 24)) (.add (.var (.n 10)) (.add (.add (.xor (.and (.xor (.var (.n 6)) (.var (.n 14))) (.var (.n 0))) (.var (.n 14))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 0)) 18) (.shr (.var (.n 0)) 14)) (.var (.n 0))) 27) (.shr (.xor (.or (.shl (.var (.n 0)) 18) (.shr (.var (.n 0)) 14)) (.var (.n 0))) 5)) (.var (.n 0))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 0)) 18) (.shr (.var (.n 0)) 14)) (.var (.n 0))) 27) (.shr (.xor (.or (.shl (.var (.n 0)) 18) (.shr (.var (.n 0)) 14)) (.var (.n 0))) 5)) (.var (.n 0))) 6))) (.add (.var (.n 180)) (.const 2428436474))))) = V (.E 0 0 (61)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 63)))
    (_ : V (.KW 0 0 63) = 3329325298#32 + V (.W 0 0 63)) :
    E.eval env (.add (.var (.n 183)) (.const 3329325298)) = V (.KW 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 63)))
    (_ : V (.KW 0 0 63) = 3329325298#32 + V (.W 0 0 63)) :
    E.eval env (.add (.var (.n 183)) (.const 3329325298)) = V (.KW 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 63)))
    (_ : V (.KW 0 0 63) = 3329325298#32 + V (.W 0 0 63)) :
    E.eval env (.add (.var (.n 183)) (.const 3329325298)) = V (.KW 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 63)))
    (_ : V (.KW 0 0 63) = 3329325298#32 + V (.W 0 0 63)) :
    E.eval env (.add (.var (.n 183)) (.const 3329325298)) = V (.KW 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 62)))
    (_ : V (.KW 0 0 62) = 3204031479#32 + V (.W 0 0 62)) :
    E.eval env (.add (.var (.n 182)) (.const 3204031479)) = V (.KW 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 62)))
    (_ : V (.KW 0 0 62) = 3204031479#32 + V (.W 0 0 62)) :
    E.eval env (.add (.var (.n 182)) (.const 3204031479)) = V (.KW 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 62)))
    (_ : V (.KW 0 0 62) = 3204031479#32 + V (.W 0 0 62)) :
    E.eval env (.add (.var (.n 182)) (.const 3204031479)) = V (.KW 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 62)))
    (_ : V (.KW 0 0 62) = 3204031479#32 + V (.W 0 0 62)) :
    E.eval env (.add (.var (.n 182)) (.const 3204031479)) = V (.KW 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 61)))
    (_ : V (.KW 0 0 61) = 2756734187#32 + V (.W 0 0 61)) :
    E.eval env (.add (.var (.n 181)) (.const 2756734187)) = V (.KW 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 61)))
    (_ : V (.KW 0 0 61) = 2756734187#32 + V (.W 0 0 61)) :
    E.eval env (.add (.var (.n 181)) (.const 2756734187)) = V (.KW 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 61)))
    (_ : V (.KW 0 0 61) = 2756734187#32 + V (.W 0 0 61)) :
    E.eval env (.add (.var (.n 181)) (.const 2756734187)) = V (.KW 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core60_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 61)))
    (_ : V (.KW 0 0 61) = 2756734187#32 + V (.W 0 0 61)) :
    E.eval env (.add (.var (.n 181)) (.const 2756734187)) = V (.KW 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step60 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L60 inp env) (hm : HMem 128 inp env) :
    Inv1 L61 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 31 K60)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 0 (by decide)).trans (core60_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 1 (by decide)).trans (core60_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 2 (by decide)).trans (core60_10 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 5 (by decide)) (qA_succI inp 0 0 (60) (by decide)) ((qKW inp 0 0 60).trans (by rw [show Spec.K 60 = 2428436474#32 from by decide])))
  | 3, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 3 (by decide)).trans (core60_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 4 (by decide)).trans (core60_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 5 (by decide)).trans (core60_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 6 (by decide)).trans (core60_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 7 (by decide)).trans (core60_24 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 8 (by decide)) (qE_succI inp 0 0 (60) (by decide)) ((qKW inp 0 0 60).trans (by rw [show Spec.K 60 = 2428436474#32 from by decide])))
  | 8, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 8 (by decide)).trans (core60_1000 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 63).trans (by rw [show Spec.K 63 = 3329325298#32 from by decide])))
  | 9, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 9 (by decide)).trans (core60_1001 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 63).trans (by rw [show Spec.K 63 = 3329325298#32 from by decide])))
  | 10, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 10 (by decide)).trans (core60_1002 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 63).trans (by rw [show Spec.K 63 = 3329325298#32 from by decide])))
  | 11, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 11 (by decide)).trans (core60_1003 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 63).trans (by rw [show Spec.K 63 = 3329325298#32 from by decide])))
  | 12, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 12 (by decide)).trans (core60_1004 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 62).trans (by rw [show Spec.K 62 = 3204031479#32 from by decide])))
  | 13, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 13 (by decide)).trans (core60_1005 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 62).trans (by rw [show Spec.K 62 = 3204031479#32 from by decide])))
  | 14, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 14 (by decide)).trans (core60_1006 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 62).trans (by rw [show Spec.K 62 = 3204031479#32 from by decide])))
  | 15, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 15 (by decide)).trans (core60_1007 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 62).trans (by rw [show Spec.K 62 = 3204031479#32 from by decide])))
  | 16, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 16 (by decide)).trans (core60_1008 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 61).trans (by rw [show Spec.K 61 = 2756734187#32 from by decide])))
  | 17, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 17 (by decide)).trans (core60_1009 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 61).trans (by rw [show Spec.K 61 = 2756734187#32 from by decide])))
  | 18, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 18 (by decide)).trans (core60_1010 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 61).trans (by rw [show Spec.K 61 = 2756734187#32 from by decide])))
  | 19, _ => exact (slice_trees prog 4 _ _ 31 K60 K61 T60 slice60 env 19 (by decide)).trans (core60_1011 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 61).trans (by rw [show Spec.K 61 = 2756734187#32 from by decide])))
  | _ + 20, hk => simp only [L61, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It0
