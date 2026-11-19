import Hashtree.Gen.SseX1LW.It0.D29
import Hashtree.Gen.SseX1LW.It0.D28
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It0
open Hashtree.Gen.SseX1LW

theorem slice29 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K29 K30 T29 = true := by
  decide +kernel

theorem core29_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (28)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (28)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (26))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (28))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (27))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (29))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 29)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 29)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 29)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 29)))
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 0 (29))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (27))))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (28))))
    (_ : V (.A 0 0 (30)) = (V (.E 0 0 (26)) + Sigma1 (V (.E 0 0 (29))) + Ch (V (.E 0 0 (29))) (V (.E 0 0 (28))) (V (.E 0 0 (27))) + V (.KW 0 0 29)) + (Sigma0 (V (.A 0 0 (29))) + Maj (V (.A 0 0 (29))) (V (.A 0 0 (28))) (V (.A 0 0 (27))))) :
    E.eval env (.add (.add (.add (.var (.n 2)) (.add (.add (.xor (.and (.xor (.var (.n 0)) (.var (.n 6))) (.var (.n 22))) (.var (.n 6))) (.ror (.xor (.ror (.xor (.ror (.var (.n 22)) 14) (.var (.n 22))) 5) (.var (.n 22))) 6)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 16)) 9) (.var (.n 16))) 11) (.var (.n 16))) 2)) (.or (.and (.or (.var (.n 16)) (.var (.n 18))) (.var (.n 24))) (.and (.var (.n 16)) (.var (.n 18))))) = V (.A 0 0 (30)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (27)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (27)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 0 (29)))) :
    E.eval env (.var (.n 16)) = V (.A 0 0 (29)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (27)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (27)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (26))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (26))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (28))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (27))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (29))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 29)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 29)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 29)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 29)))
    (_ : V (.E 0 0 (30)) = V (.A 0 0 (26)) + (V (.E 0 0 (26)) + Sigma1 (V (.E 0 0 (29))) + Ch (V (.E 0 0 (29))) (V (.E 0 0 (28))) (V (.E 0 0 (27))) + V (.KW 0 0 29))) :
    E.eval env (.add (.var (.n 20)) (.add (.var (.n 2)) (.add (.add (.xor (.and (.xor (.var (.n 0)) (.var (.n 6))) (.var (.n 22))) (.var (.n 6))) (.ror (.xor (.ror (.xor (.ror (.var (.n 22)) 14) (.var (.n 22))) 5) (.var (.n 22))) 6)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))))) = V (.E 0 0 (30)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (29)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (29)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (28)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (28)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.add (.q (.W 0 0 37)) (.q (.W 0 0 28))))
    (_ : env (.n 116) = QE.eval V inp (.or (.shl (.q (.W 0 0 29)) 25) (.shr (.q (.W 0 0 29)) 7)))
    (_ : env (.n 148) = QE.eval V inp (.q (.W 0 0 29)))
    (_ : V (.M2 0 0 28) = V (.M1 0 0 28) + V (.W 0 0 37))
    (_ : V (.M1 0 0 28) = V (.W 0 0 28) + sigma0 (V (.W 0 0 29))) :
    E.eval env (.add (.var (.n 100)) (.xor (.xor (.xor (.var (.n 116)) (.shl (.var (.n 148)) 14)) (.shr (.var (.n 148)) 18)) (.shr (.var (.n 148)) 3))) = V (.M2 0 0 28) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.add (.q (.W 0 0 38)) (.q (.W 0 0 29))))
    (_ : env (.n 117) = QE.eval V inp (.or (.shl (.q (.W 0 0 30)) 25) (.shr (.q (.W 0 0 30)) 7)))
    (_ : env (.n 149) = QE.eval V inp (.q (.W 0 0 30)))
    (_ : V (.M2 0 0 29) = V (.M1 0 0 29) + V (.W 0 0 38))
    (_ : V (.M1 0 0 29) = V (.W 0 0 29) + sigma0 (V (.W 0 0 30))) :
    E.eval env (.add (.var (.n 101)) (.xor (.xor (.xor (.var (.n 117)) (.shl (.var (.n 149)) 14)) (.shr (.var (.n 149)) 18)) (.shr (.var (.n 149)) 3))) = V (.M2 0 0 29) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.add (.q (.W 0 0 39)) (.q (.W 0 0 30))))
    (_ : env (.n 118) = QE.eval V inp (.or (.shl (.q (.W 0 0 31)) 25) (.shr (.q (.W 0 0 31)) 7)))
    (_ : env (.n 150) = QE.eval V inp (.q (.W 0 0 31)))
    (_ : V (.M2 0 0 30) = V (.M1 0 0 30) + V (.W 0 0 39))
    (_ : V (.M1 0 0 30) = V (.W 0 0 30) + sigma0 (V (.W 0 0 31))) :
    E.eval env (.add (.var (.n 102)) (.xor (.xor (.xor (.var (.n 118)) (.shl (.var (.n 150)) 14)) (.shr (.var (.n 150)) 18)) (.shr (.var (.n 150)) 3))) = V (.M2 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.add (.q (.W 0 0 40)) (.q (.W 0 0 31))))
    (_ : env (.n 119) = QE.eval V inp (.or (.shl (.q (.W 0 0 32)) 25) (.shr (.q (.W 0 0 32)) 7)))
    (_ : env (.n 151) = QE.eval V inp (.q (.W 0 0 32)))
    (_ : V (.M2 0 0 31) = V (.M1 0 0 31) + V (.W 0 0 40))
    (_ : V (.M1 0 0 31) = V (.W 0 0 31) + sigma0 (V (.W 0 0 32))) :
    E.eval env (.add (.var (.n 103)) (.xor (.xor (.xor (.var (.n 119)) (.shl (.var (.n 151)) 14)) (.shr (.var (.n 151)) 18)) (.shr (.var (.n 151)) 3))) = V (.M2 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 32))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 32) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 33))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 33) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 34))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 34) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 35))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 35) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 36))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 36) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 37))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 37) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 38))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 38) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 39))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 39) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 40))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 40) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 41))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 41) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 42))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 42) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 43))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 43) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 31))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 31))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 31))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 31))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 31) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 30))) :
    E.eval env (.var (.n 1004)) = V (.KW 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 30))) :
    E.eval env (.var (.n 1005)) = V (.KW 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 30))) :
    E.eval env (.var (.n 1006)) = V (.KW 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core29_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 30))) :
    E.eval env (.var (.n 1007)) = V (.KW 0 0 30) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step29 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L29 inp env) (hm : HMem 128 inp env) :
    Inv1 L30 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K29)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 0 (by decide)).trans (core29_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 1 (by decide)).trans (core29_2 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 7 (by decide)) (qA_succI inp 0 0 (29) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 2 (by decide)).trans (core29_6 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 3 (by decide)).trans (core29_16 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 4 (by decide)).trans (core29_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 5 (by decide)).trans (core29_20 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (qE_succI inp 0 0 (29) (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 6 (by decide)).trans (core29_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 7 (by decide)).trans (core29_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 8 (by decide)).trans (core29_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 16 (by decide)) (qM2 inp 0 0 28) (qM1 inp 0 0 28))
  | 9, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 9 (by decide)).trans (core29_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 17 (by decide)) (qM2 inp 0 0 29) (qM1 inp 0 0 29))
  | 10, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 10 (by decide)).trans (core29_102 (qv inp) inp env (inv1_get hI 10 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 18 (by decide)) (qM2 inp 0 0 30) (qM1 inp 0 0 30))
  | 11, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 11 (by decide)).trans (core29_103 (qv inp) inp env (inv1_get hI 11 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 19 (by decide)) (qM2 inp 0 0 31) (qM1 inp 0 0 31))
  | 12, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 12 (by decide)).trans (core29_132 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 13 (by decide)).trans (core29_133 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 14 (by decide)).trans (core29_134 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 15 (by decide)).trans (core29_135 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 16 (by decide)).trans (core29_164 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 17 (by decide)).trans (core29_165 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 18 (by decide)).trans (core29_166 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 19 (by decide)).trans (core29_167 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 20 (by decide)).trans (core29_180 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 21 (by decide)).trans (core29_181 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 22 (by decide)).trans (core29_182 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 23 (by decide)).trans (core29_183 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 24 (by decide)).trans (core29_196 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 25 (by decide)).trans (core29_197 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 26 (by decide)).trans (core29_198 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 27 (by decide)).trans (core29_199 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 28 (by decide)).trans (core29_1000 (qv inp) inp env (inv1_get hI 32 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 29 (by decide)).trans (core29_1001 (qv inp) inp env (inv1_get hI 33 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 30 (by decide)).trans (core29_1002 (qv inp) inp env (inv1_get hI 34 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 31 (by decide)).trans (core29_1003 (qv inp) inp env (inv1_get hI 35 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 32 (by decide)).trans (core29_1004 (qv inp) inp env (inv1_get hI 36 (by decide)))
  | 33, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 33 (by decide)).trans (core29_1005 (qv inp) inp env (inv1_get hI 37 (by decide)))
  | 34, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 34 (by decide)).trans (core29_1006 (qv inp) inp env (inv1_get hI 38 (by decide)))
  | 35, _ => exact (slice_trees prog 4 _ _ 38 K29 K30 T29 slice29 env 35 (by decide)).trans (core29_1007 (qv inp) inp env (inv1_get hI 39 (by decide)))
  | _ + 36, hk => simp only [L30, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It0
