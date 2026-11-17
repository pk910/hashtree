import Hashtree.Gen.WinAvxX1LW.It.D11
import Hashtree.Gen.WinAvxX1LW.It.D10
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.AvxX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinAvxX1LW.It
open Hashtree.Gen.WinAvxX1LW

theorem slice11 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 35 K11 K12 T11 = true := by
  decide +kernel

theorem core11_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.A 0 0 (8))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (8))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (10))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (9))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (11))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 11)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 11)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 11)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 11)))
    (_ : V (.E 0 0 (12)) = V (.A 0 0 (8)) + (V (.E 0 0 (8)) + Sigma1 (V (.E 0 0 (11))) + Ch (V (.E 0 0 (11))) (V (.E 0 0 (10))) (V (.E 0 0 (9))) + V (.KW 0 0 11))) :
    E.eval env (.add (.var (.n 0)) (.add (.var (.n 18)) (.add (.add (.xor (.and (.xor (.var (.n 14)) (.var (.n 10))) (.var (.n 6))) (.var (.n 10))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 6)) 18) (.shr (.var (.n 6)) 14)) (.var (.n 6))) 27) (.shr (.xor (.or (.shl (.var (.n 6)) 18) (.shr (.var (.n 6)) 14)) (.var (.n 6))) 5)) (.var (.n 6))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 6)) 18) (.shr (.var (.n 6)) 14)) (.var (.n 6))) 27) (.shr (.xor (.or (.shl (.var (.n 6)) 18) (.shr (.var (.n 6)) 14)) (.var (.n 6))) 5)) (.var (.n 6))) 6))) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))))) = V (.E 0 0 (12)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (11)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (11)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_10 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (9)))) :
    E.eval env (.var (.n 10)) = V (.E 0 0 (9)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (10)))) :
    E.eval env (.var (.n 14)) = V (.E 0 0 (10)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (8))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (10))))
    (_ : env (.n 10) = QE.eval V inp (.q (.E 0 0 (9))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (11))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 11)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 11)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 11)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 11)))
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (11))))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (9))))
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (10))))
    (_ : V (.A 0 0 (12)) = (V (.E 0 0 (8)) + Sigma1 (V (.E 0 0 (11))) + Ch (V (.E 0 0 (11))) (V (.E 0 0 (10))) (V (.E 0 0 (9))) + V (.KW 0 0 11)) + (Sigma0 (V (.A 0 0 (11))) + Maj (V (.A 0 0 (11))) (V (.A 0 0 (10))) (V (.A 0 0 (9))))) :
    E.eval env (.add (.add (.add (.var (.n 18)) (.add (.add (.xor (.and (.xor (.var (.n 14)) (.var (.n 10))) (.var (.n 6))) (.var (.n 10))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 6)) 18) (.shr (.var (.n 6)) 14)) (.var (.n 6))) 27) (.shr (.xor (.or (.shl (.var (.n 6)) 18) (.shr (.var (.n 6)) 14)) (.var (.n 6))) 5)) (.var (.n 6))) 26) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 6)) 18) (.shr (.var (.n 6)) 14)) (.var (.n 6))) 27) (.shr (.xor (.or (.shl (.var (.n 6)) 18) (.shr (.var (.n 6)) 14)) (.var (.n 6))) 5)) (.var (.n 6))) 6))) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24))))) (.or (.shl (.xor (.or (.shl (.xor (.or (.shl (.var (.n 20)) 23) (.shr (.var (.n 20)) 9)) (.var (.n 20))) 21) (.shr (.xor (.or (.shl (.var (.n 20)) 23) (.shr (.var (.n 20)) 9)) (.var (.n 20))) 11)) (.var (.n 20))) 30) (.shr (.xor (.or (.shl (.xor (.or (.shl (.var (.n 20)) 23) (.shr (.var (.n 20)) 9)) (.var (.n 20))) 21) (.shr (.xor (.or (.shl (.var (.n 20)) 23) (.shr (.var (.n 20)) 9)) (.var (.n 20))) 11)) (.var (.n 20))) 2))) (.or (.and (.or (.var (.n 20)) (.var (.n 24))) (.var (.n 22))) (.and (.var (.n 20)) (.var (.n 24))))) = V (.A 0 0 (12)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (11)))) :
    E.eval env (.var (.n 20)) = V (.A 0 0 (11)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.A 0 0 (10)))) :
    E.eval env (.var (.n 22)) = V (.A 0 0 (10)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (9)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (9)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 20))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 20) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 21))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 21) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 22))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 22) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 23))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 23) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.q (.W 0 0 24))) :
    E.eval env (.add (.const 0) (.var (.n 100))) = V (.W 0 0 24) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.q (.W 0 0 25))) :
    E.eval env (.add (.const 0) (.var (.n 101))) = V (.W 0 0 25) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 132) = QE.eval V inp (.q (.W 0 0 24)))
    (_ : env (.n 133) = QE.eval V inp (.q (.W 0 0 24)))
    (_ : env (.n 102) = QE.eval V inp (.q (.M2 0 0 10)))
    (_ : V (.W 0 0 26) = sigma1 (V (.W 0 0 24)) + V (.M2 0 0 10)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 132)) 10) (.xor (.or (.shr (.var (.n 132)) 17) (.shl (.var (.n 133)) 15)) (.or (.shr (.var (.n 132)) 19) (.shl (.var (.n 133)) 13)))) 24) (.const 255)) 24))) (.var (.n 102))) = V (.W 0 0 26) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 134) = QE.eval V inp (.q (.W 0 0 25)))
    (_ : env (.n 135) = QE.eval V inp (.q (.W 0 0 25)))
    (_ : env (.n 103) = QE.eval V inp (.q (.M2 0 0 11)))
    (_ : V (.W 0 0 27) = sigma1 (V (.W 0 0 25)) + V (.M2 0 0 11)) :
    E.eval env (.add (.or (.or (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 0) (.const 255)) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 16) (.const 255)) 16) (.shl (.and (.shr (.xor (.shr (.var (.n 134)) 10) (.xor (.or (.shr (.var (.n 134)) 17) (.shl (.var (.n 135)) 15)) (.or (.shr (.var (.n 134)) 19) (.shl (.var (.n 135)) 13)))) 24) (.const 255)) 24))) (.var (.n 103))) = V (.W 0 0 27) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 12) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 13))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 13) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core11_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step11 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L11 inp env) (hm : HMem 128 inp env) :
    Inv1 L12 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 35 K11)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 0 (by decide)).trans (core11_0 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (qE_succI inp 0 0 (11) (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 1 (by decide)).trans (core11_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 2 (by decide)).trans (core11_10 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 3 (by decide)).trans (core11_14 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 4 (by decide)).trans (core11_18 (qv inp) inp env (inv1_get hI 4 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 31 (by decide)) (inv1_get hI 30 (by decide)) (inv1_get hI 29 (by decide)) (inv1_get hI 28 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 7 (by decide)) (inv1_get hI 6 (by decide)) (qA_succI inp 0 0 (11) (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 5 (by decide)).trans (core11_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 6 (by decide)).trans (core11_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 7 (by decide)).trans (core11_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 8 (by decide)).trans (core11_164 (qv inp) inp env (inv1_get hI 16 (by decide)))
  | 9, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 9 (by decide)).trans (core11_165 (qv inp) inp env (inv1_get hI 17 (by decide)))
  | 10, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 10 (by decide)).trans (core11_166 (qv inp) inp env (inv1_get hI 18 (by decide)))
  | 11, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 11 (by decide)).trans (core11_167 (qv inp) inp env (inv1_get hI 19 (by decide)))
  | 12, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 12 (by decide)).trans (core11_180 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 13 (by decide)).trans (core11_181 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 14 (by decide)).trans (core11_182 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 15 (by decide)).trans (core11_183 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 16 (by decide)).trans (core11_196 (qv inp) inp env (inv1_get hI 8 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 17 (by decide)).trans (core11_197 (qv inp) inp env (inv1_get hI 9 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 18 (by decide)).trans (core11_198 (qv inp) inp env (inv1_get hI 12 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 10 (by decide)) (qW_recM2 inp 0 0 26 (by decide) (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 19 (by decide)).trans (core11_199 (qv inp) inp env (inv1_get hI 14 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 11 (by decide)) (qW_recM2 inp 0 0 27 (by decide) (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 20 (by decide)).trans (core11_212 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 21 (by decide)).trans (core11_213 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 22 (by decide)).trans (core11_214 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 35 K11 K12 T11 slice11 env 23 (by decide)).trans (core11_215 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | _ + 24, hk => simp only [L12, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinAvxX1LW.It
