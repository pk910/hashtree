import Hashtree.Gen.SseX1LW.It0.D63
import Hashtree.Gen.SseX1LW.It0.D62
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It0
open Hashtree.Gen.SseX1LW

theorem slice63 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K63 K64 T63 = true := by
  decide +kernel

theorem core63_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (60))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (63))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 63)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 63)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 63)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 63)))
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (63))))
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 0 (61))))
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 0 (62))))
    (_ : V (.A 0 0 (64)) = (V (.E 0 0 (60)) + Sigma1 (V (.E 0 0 (63))) + Ch (V (.E 0 0 (63))) (V (.E 0 0 (62))) (V (.E 0 0 (61))) + V (.KW 0 0 63)) + (Sigma0 (V (.A 0 0 (63))) + Maj (V (.A 0 0 (63))) (V (.A 0 0 (62))) (V (.A 0 0 (61))))) :
    E.eval env (.add (.add (.add (.var (.n 0)) (.add (.add (.xor (.and (.xor (.var (.n 20)) (.var (.n 22))) (.var (.n 18))) (.var (.n 22))) (.ror (.xor (.ror (.xor (.ror (.var (.n 18)) 14) (.var (.n 18))) 5) (.var (.n 18))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 6)) 9) (.var (.n 6))) 11) (.var (.n 6))) 2)) (.or (.and (.or (.var (.n 6)) (.var (.n 16))) (.var (.n 2))) (.and (.var (.n 6)) (.var (.n 16))))) = V (.A 0 0 (64)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core63_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.A 0 0 (62)))) :
    E.eval env (.var (.n 2)) = V (.A 0 0 (62)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core63_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.A 0 0 (63)))) :
    E.eval env (.var (.n 6)) = V (.A 0 0 (63)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core63_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 0 (61)))) :
    E.eval env (.var (.n 16)) = V (.A 0 0 (61)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core63_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (63)))) :
    E.eval env (.var (.n 18)) = V (.E 0 0 (63)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core63_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (62)))) :
    E.eval env (.var (.n 20)) = V (.E 0 0 (62)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core63_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (61)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (61)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core63_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (60))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (60))))
    (_ : env (.n 20) = QE.eval V inp (.q (.E 0 0 (62))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (61))))
    (_ : env (.n 18) = QE.eval V inp (.q (.E 0 0 (63))))
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 63)))
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 63)))
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 63)))
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 63)))
    (_ : V (.E 0 0 (64)) = V (.A 0 0 (60)) + (V (.E 0 0 (60)) + Sigma1 (V (.E 0 0 (63))) + Ch (V (.E 0 0 (63))) (V (.E 0 0 (62))) (V (.E 0 0 (61))) + V (.KW 0 0 63))) :
    E.eval env (.add (.var (.n 24)) (.add (.var (.n 0)) (.add (.add (.xor (.and (.xor (.var (.n 20)) (.var (.n 22))) (.var (.n 18))) (.var (.n 22))) (.ror (.xor (.ror (.xor (.ror (.var (.n 18)) 14) (.var (.n 18))) 5) (.var (.n 18))) 6)) (.or (.or (.and (.shr (.var (.n 1003)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1002)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1001)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1000)) 24) (.const 255)) 24)))))) = V (.E 0 0 (64)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step63 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L63 inp env) (hm : HMem 128 inp env) :
    Inv1 L64 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 28 K63)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 28 K63 K64 T63 slice63 env 0 (by decide)).trans (core63_0 (qv inp) inp env (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 11 (by decide)) (inv1_get hI 10 (by decide)) (inv1_get hI 9 (by decide)) (inv1_get hI 8 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 1 (by decide)) (qA_succI inp 0 0 (63) (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 28 K63 K64 T63 slice63 env 1 (by decide)).trans (core63_2 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 28 K63 K64 T63 slice63 env 2 (by decide)).trans (core63_6 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 28 K63 K64 T63 slice63 env 3 (by decide)).trans (core63_16 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 28 K63 K64 T63 slice63 env 4 (by decide)).trans (core63_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 28 K63 K64 T63 slice63 env 5 (by decide)).trans (core63_20 (qv inp) inp env (inv1_get hI 5 (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 28 K63 K64 T63 slice63 env 6 (by decide)).trans (core63_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 28 K63 K64 T63 slice63 env 7 (by decide)).trans (core63_24 (qv inp) inp env (inv1_get hI 7 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 5 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 11 (by decide)) (inv1_get hI 10 (by decide)) (inv1_get hI 9 (by decide)) (inv1_get hI 8 (by decide)) (qE_succI inp 0 0 (63) (by decide)))
  | _ + 8, hk => simp only [L64, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It0
