import Hashtree.Gen.WinSseX1LW.It.D48
import Hashtree.Gen.WinSseX1LW.It.D47
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It
open Hashtree.Gen.WinSseX1LW

theorem slice48 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 30 K48 K49 T48 = true := by
  decide +kernel

theorem core48_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (48)))) :
    E.eval env (.var (.n 0)) = V (.A 0 0 (48)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (47)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (47)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (45))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (45))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (47))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (46))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (48))))
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48)))
    (_ : V (.E 0 0 (49)) = V (.A 0 0 (45)) + (V (.E 0 0 (45)) + Sigma1 (V (.E 0 0 (48))) + Ch (V (.E 0 0 (48))) (V (.E 0 0 (47))) (V (.E 0 0 (46))) + V (.KW 0 0 48)))
    (_ : V (.KW 0 0 48) = 430227734#32 + V (.W 0 0 48)) :
    E.eval env (.add (.var (.n 12)) (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.var (.n 164)) (.const 430227734))))) = V (.E 0 0 (49)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (46)))) :
    E.eval env (.var (.n 14)) = V (.A 0 0 (46)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (47)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (47)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (46)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (46)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (45))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (47))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (46))))
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (48))))
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48)))
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (48))))
    (_ : env (.n 14) = QE.eval V inp (.q (.A 0 0 (46))))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (47))))
    (_ : V (.A 0 0 (49)) = (V (.E 0 0 (45)) + Sigma1 (V (.E 0 0 (48))) + Ch (V (.E 0 0 (48))) (V (.E 0 0 (47))) (V (.E 0 0 (46))) + V (.KW 0 0 48)) + (Sigma0 (V (.A 0 0 (48))) + Maj (V (.A 0 0 (48))) (V (.A 0 0 (47))) (V (.A 0 0 (46)))))
    (_ : V (.KW 0 0 48) = 430227734#32 + V (.W 0 0 48)) :
    E.eval env (.add (.add (.add (.var (.n 22)) (.add (.add (.xor (.and (.xor (.var (.n 18)) (.var (.n 20))) (.var (.n 24))) (.var (.n 20))) (.ror (.xor (.ror (.xor (.ror (.var (.n 24)) 14) (.var (.n 24))) 5) (.var (.n 24))) 6)) (.add (.var (.n 164)) (.const 430227734)))) (.ror (.xor (.ror (.xor (.ror (.var (.n 0)) 9) (.var (.n 0))) 11) (.var (.n 0))) 2)) (.or (.and (.or (.var (.n 0)) (.var (.n 14))) (.var (.n 6))) (.and (.var (.n 0)) (.var (.n 14))))) = V (.A 0 0 (49)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.E 0 0 (48)))) :
    E.eval env (.var (.n 24)) = V (.E 0 0 (48)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 60))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 60) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 61))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 61) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 62))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 62) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 63))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 63) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : V (.KW 0 0 51) = 883997877#32 + V (.W 0 0 51)) :
    E.eval env (.add (.var (.n 167)) (.const 883997877)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : V (.KW 0 0 51) = 883997877#32 + V (.W 0 0 51)) :
    E.eval env (.add (.var (.n 167)) (.const 883997877)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : V (.KW 0 0 51) = 883997877#32 + V (.W 0 0 51)) :
    E.eval env (.add (.var (.n 167)) (.const 883997877)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51)))
    (_ : V (.KW 0 0 51) = 883997877#32 + V (.W 0 0 51)) :
    E.eval env (.add (.var (.n 167)) (.const 883997877)) = V (.KW 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : V (.KW 0 0 50) = 659060556#32 + V (.W 0 0 50)) :
    E.eval env (.add (.var (.n 166)) (.const 659060556)) = V (.KW 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : V (.KW 0 0 50) = 659060556#32 + V (.W 0 0 50)) :
    E.eval env (.add (.var (.n 166)) (.const 659060556)) = V (.KW 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : V (.KW 0 0 50) = 659060556#32 + V (.W 0 0 50)) :
    E.eval env (.add (.var (.n 166)) (.const 659060556)) = V (.KW 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50)))
    (_ : V (.KW 0 0 50) = 659060556#32 + V (.W 0 0 50)) :
    E.eval env (.add (.var (.n 166)) (.const 659060556)) = V (.KW 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1008 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49)))
    (_ : V (.KW 0 0 49) = 506948616#32 + V (.W 0 0 49)) :
    E.eval env (.add (.var (.n 165)) (.const 506948616)) = V (.KW 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1009 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49)))
    (_ : V (.KW 0 0 49) = 506948616#32 + V (.W 0 0 49)) :
    E.eval env (.add (.var (.n 165)) (.const 506948616)) = V (.KW 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1010 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49)))
    (_ : V (.KW 0 0 49) = 506948616#32 + V (.W 0 0 49)) :
    E.eval env (.add (.var (.n 165)) (.const 506948616)) = V (.KW 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core48_1011 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49)))
    (_ : V (.KW 0 0 49) = 506948616#32 + V (.W 0 0 49)) :
    E.eval env (.add (.var (.n 165)) (.const 506948616)) = V (.KW 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step48 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L48 inp env) (hm : HMem 128 inp env) :
    Inv1 L49 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 30 K48)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 0 (by decide)).trans (core48_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 1 (by decide)).trans (core48_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 2 (by decide)).trans (core48_12 (qv inp) inp env (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 8 (by decide)) (qE_succI inp 0 0 (48) (by decide)) ((qKW inp 0 0 48).trans (by rw [show Spec.K 48 = 430227734#32 from by decide])))
  | 3, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 3 (by decide)).trans (core48_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 4 (by decide)).trans (core48_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 5 (by decide)).trans (core48_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 6 (by decide)).trans (core48_22 (qv inp) inp env (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 1 (by decide)) (qA_succI inp 0 0 (48) (by decide)) ((qKW inp 0 0 48).trans (by rw [show Spec.K 48 = 430227734#32 from by decide])))
  | 7, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 7 (by decide)).trans (core48_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 8 (by decide)).trans (core48_180 (qv inp) inp env (inv1_get hI 12 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 9 (by decide)).trans (core48_181 (qv inp) inp env (inv1_get hI 13 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 10 (by decide)).trans (core48_182 (qv inp) inp env (inv1_get hI 14 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 11 (by decide)).trans (core48_183 (qv inp) inp env (inv1_get hI 15 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 12 (by decide)).trans (core48_196 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 13 (by decide)).trans (core48_197 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 14 (by decide)).trans (core48_198 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 15 (by decide)).trans (core48_199 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 16 (by decide)).trans (core48_212 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 17 (by decide)).trans (core48_213 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 18 (by decide)).trans (core48_214 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 19 (by decide)).trans (core48_215 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 20 (by decide)).trans (core48_1000 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 51).trans (by rw [show Spec.K 51 = 883997877#32 from by decide])))
  | 21, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 21 (by decide)).trans (core48_1001 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 51).trans (by rw [show Spec.K 51 = 883997877#32 from by decide])))
  | 22, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 22 (by decide)).trans (core48_1002 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 51).trans (by rw [show Spec.K 51 = 883997877#32 from by decide])))
  | 23, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 23 (by decide)).trans (core48_1003 (qv inp) inp env (inv1_get hI 11 (by decide)) ((qKW inp 0 0 51).trans (by rw [show Spec.K 51 = 883997877#32 from by decide])))
  | 24, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 24 (by decide)).trans (core48_1004 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 50).trans (by rw [show Spec.K 50 = 659060556#32 from by decide])))
  | 25, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 25 (by decide)).trans (core48_1005 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 50).trans (by rw [show Spec.K 50 = 659060556#32 from by decide])))
  | 26, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 26 (by decide)).trans (core48_1006 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 50).trans (by rw [show Spec.K 50 = 659060556#32 from by decide])))
  | 27, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 27 (by decide)).trans (core48_1007 (qv inp) inp env (inv1_get hI 10 (by decide)) ((qKW inp 0 0 50).trans (by rw [show Spec.K 50 = 659060556#32 from by decide])))
  | 28, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 28 (by decide)).trans (core48_1008 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 49).trans (by rw [show Spec.K 49 = 506948616#32 from by decide])))
  | 29, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 29 (by decide)).trans (core48_1009 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 49).trans (by rw [show Spec.K 49 = 506948616#32 from by decide])))
  | 30, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 30 (by decide)).trans (core48_1010 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 49).trans (by rw [show Spec.K 49 = 506948616#32 from by decide])))
  | 31, _ => exact (slice_trees prog 4 _ _ 30 K48 K49 T48 slice48 env 31 (by decide)).trans (core48_1011 (qv inp) inp env (inv1_get hI 9 (by decide)) ((qKW inp 0 0 49).trans (by rw [show Spec.K 49 = 506948616#32 from by decide])))
  | _ + 32, hk => simp only [L49, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It
