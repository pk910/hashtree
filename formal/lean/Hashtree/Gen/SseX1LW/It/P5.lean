import Hashtree.Gen.SseX1LW.It.D5
import Hashtree.Gen.SseX1LW.It.D4
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It
open Hashtree.Gen.SseX1LW

theorem slice5 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K5 K6 T5 = true := by
  decide +kernel

theorem core5_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (4)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (4)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_2 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (2))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (4))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (3))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (5))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 5)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 5)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 5)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 5)))
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 0 (5))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (3))))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (4))))
    (_ : V (.A 0 0 (6)) = (V (.E 0 0 (2)) + Sigma1 (V (.E 0 0 (5))) + Ch (V (.E 0 0 (5))) (V (.E 0 0 (4))) (V (.E 0 0 (3))) + V (.KW 0 0 5)) + (Sigma0 (V (.A 0 0 (5))) + Maj (V (.A 0 0 (5))) (V (.A 0 0 (4))) (V (.A 0 0 (3))))) :
    E.eval env (.add (.add (.add (.var (.n 2)) (.add (.add (.xor (.and (.xor (.var (.n 0)) (.var (.n 6))) (.var (.n 22))) (.var (.n 6))) (.ror (.xor (.ror (.xor (.ror (.var (.n 22)) 14) (.var (.n 22))) 5) (.var (.n 22))) 6)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 16)) 9) (.var (.n 16))) 11) (.var (.n 16))) 2)) (.or (.and (.or (.var (.n 16)) (.var (.n 18))) (.var (.n 24))) (.and (.var (.n 16)) (.var (.n 18))))) = V (.A 0 0 (6)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (3)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_16 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 16) = QE.eval V inp (.q (.A 0 0 (5)))) :
    E.eval env (.var (.n 16)) = V (.A 0 0 (5)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (3)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (3)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (2))))
    (_ : env (.n 2) = QE.eval V inp (.q (.E 0 0 (2))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (4))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (3))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (5))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 5)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 5)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 5)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 5)))
    (_ : V (.E 0 0 (6)) = V (.A 0 0 (2)) + (V (.E 0 0 (2)) + Sigma1 (V (.E 0 0 (5))) + Ch (V (.E 0 0 (5))) (V (.E 0 0 (4))) (V (.E 0 0 (3))) + V (.KW 0 0 5))) :
    E.eval env (.add (.var (.n 20)) (.add (.var (.n 2)) (.add (.add (.xor (.and (.xor (.var (.n 0)) (.var (.n 6))) (.var (.n 22))) (.var (.n 6))) (.ror (.xor (.ror (.xor (.ror (.var (.n 22)) 14) (.var (.n 22))) 5) (.var (.n 22))) 6)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))))) = V (.E 0 0 (6)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (5)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (5)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (4)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (4)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.add (.q (.W 0 0 13)) (.q (.W 0 0 4))))
    (_ : env (.n 116) = QE.eval V inp (.or (.shl (.q (.W 0 0 5)) 25) (.shr (.q (.W 0 0 5)) 7)))
    (_ : env (.n 148) = QE.eval V inp (.q (.W 0 0 5)))
    (_ : V (.M2 0 0 4) = V (.M1 0 0 4) + V (.W 0 0 13))
    (_ : V (.M1 0 0 4) = V (.W 0 0 4) + sigma0 (V (.W 0 0 5))) :
    E.eval env (.add (.var (.n 100)) (.xor (.xor (.xor (.var (.n 116)) (.shl (.var (.n 148)) 14)) (.shr (.var (.n 148)) 18)) (.shr (.var (.n 148)) 3))) = V (.M2 0 0 4) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.add (.q (.W 0 0 14)) (.q (.W 0 0 5))))
    (_ : env (.n 117) = QE.eval V inp (.or (.shl (.q (.W 0 0 6)) 25) (.shr (.q (.W 0 0 6)) 7)))
    (_ : env (.n 149) = QE.eval V inp (.q (.W 0 0 6)))
    (_ : V (.M2 0 0 5) = V (.M1 0 0 5) + V (.W 0 0 14))
    (_ : V (.M1 0 0 5) = V (.W 0 0 5) + sigma0 (V (.W 0 0 6))) :
    E.eval env (.add (.var (.n 101)) (.xor (.xor (.xor (.var (.n 117)) (.shl (.var (.n 149)) 14)) (.shr (.var (.n 149)) 18)) (.shr (.var (.n 149)) 3))) = V (.M2 0 0 5) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.add (.q (.W 0 0 15)) (.q (.W 0 0 6))))
    (_ : env (.n 118) = QE.eval V inp (.or (.shl (.q (.W 0 0 7)) 25) (.shr (.q (.W 0 0 7)) 7)))
    (_ : env (.n 150) = QE.eval V inp (.q (.W 0 0 7)))
    (_ : V (.M2 0 0 6) = V (.M1 0 0 6) + V (.W 0 0 15))
    (_ : V (.M1 0 0 6) = V (.W 0 0 6) + sigma0 (V (.W 0 0 7))) :
    E.eval env (.add (.var (.n 102)) (.xor (.xor (.xor (.var (.n 118)) (.shl (.var (.n 150)) 14)) (.shr (.var (.n 150)) 18)) (.shr (.var (.n 150)) 3))) = V (.M2 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.add (.q (.W 0 0 16)) (.q (.W 0 0 7))))
    (_ : env (.n 119) = QE.eval V inp (.or (.shl (.q (.W 0 0 8)) 25) (.shr (.q (.W 0 0 8)) 7)))
    (_ : env (.n 151) = QE.eval V inp (.q (.W 0 0 8)))
    (_ : V (.M2 0 0 7) = V (.M1 0 0 7) + V (.W 0 0 16))
    (_ : V (.M1 0 0 7) = V (.W 0 0 7) + sigma0 (V (.W 0 0 8))) :
    E.eval env (.add (.var (.n 103)) (.xor (.xor (.xor (.var (.n 119)) (.shl (.var (.n 151)) 14)) (.shr (.var (.n 151)) 18)) (.shr (.var (.n 151)) 3))) = V (.M2 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 16))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 16) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 17))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 17) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 18))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 18) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 19))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 19) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 8))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 8) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 9))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 9) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 10))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 10) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 11))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 11) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_212 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 212) = QE.eval V inp (.q (.W 0 0 12))) :
    E.eval env (.var (.n 212)) = V (.W 0 0 12) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_213 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 213) = QE.eval V inp (.q (.W 0 0 13))) :
    E.eval env (.var (.n 213)) = V (.W 0 0 13) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_214 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 214) = QE.eval V inp (.q (.W 0 0 14))) :
    E.eval env (.var (.n 214)) = V (.W 0 0 14) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_215 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 215) = QE.eval V inp (.q (.W 0 0 15))) :
    E.eval env (.var (.n 215)) = V (.W 0 0 15) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 7))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 7))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 7))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 7))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 7) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 6))) :
    E.eval env (.var (.n 1004)) = V (.KW 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 6))) :
    E.eval env (.var (.n 1005)) = V (.KW 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 6))) :
    E.eval env (.var (.n 1006)) = V (.KW 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core5_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 6))) :
    E.eval env (.var (.n 1007)) = V (.KW 0 0 6) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step5 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L5 inp env) (hm : HMem 128 inp env) :
    Inv1 L6 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K5)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 0 (by decide)).trans (core5_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 1 (by decide)).trans (core5_2 (qv inp) inp env (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 7 (by decide)) (qA_succI inp 0 0 (5) (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 2 (by decide)).trans (core5_6 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 3 (by decide)).trans (core5_16 (qv inp) inp env (inv1_get hI 3 (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 4 (by decide)).trans (core5_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 5 (by decide)).trans (core5_20 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (qE_succI inp 0 0 (5) (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 6 (by decide)).trans (core5_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 7 (by decide)).trans (core5_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 8 (by decide)).trans (core5_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 16 (by decide)) (qM2 inp 0 0 4) (qM1 inp 0 0 4))
  | 9, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 9 (by decide)).trans (core5_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 17 (by decide)) (qM2 inp 0 0 5) (qM1 inp 0 0 5))
  | 10, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 10 (by decide)).trans (core5_102 (qv inp) inp env (inv1_get hI 10 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 18 (by decide)) (qM2 inp 0 0 6) (qM1 inp 0 0 6))
  | 11, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 11 (by decide)).trans (core5_103 (qv inp) inp env (inv1_get hI 11 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 19 (by decide)) (qM2 inp 0 0 7) (qM1 inp 0 0 7))
  | 12, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 12 (by decide)).trans (core5_132 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 13 (by decide)).trans (core5_133 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 14 (by decide)).trans (core5_134 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 15 (by decide)).trans (core5_135 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 16 (by decide)).trans (core5_164 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 17 (by decide)).trans (core5_165 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 18 (by decide)).trans (core5_166 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 19 (by decide)).trans (core5_167 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 20 (by decide)).trans (core5_196 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 21 (by decide)).trans (core5_197 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 22 (by decide)).trans (core5_198 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 23 (by decide)).trans (core5_199 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 24 (by decide)).trans (core5_212 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 25 (by decide)).trans (core5_213 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 26 (by decide)).trans (core5_214 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 27 (by decide)).trans (core5_215 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 28 (by decide)).trans (core5_1000 (qv inp) inp env (inv1_get hI 32 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 29 (by decide)).trans (core5_1001 (qv inp) inp env (inv1_get hI 33 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 30 (by decide)).trans (core5_1002 (qv inp) inp env (inv1_get hI 34 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 31 (by decide)).trans (core5_1003 (qv inp) inp env (inv1_get hI 35 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 32 (by decide)).trans (core5_1004 (qv inp) inp env (inv1_get hI 36 (by decide)))
  | 33, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 33 (by decide)).trans (core5_1005 (qv inp) inp env (inv1_get hI 37 (by decide)))
  | 34, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 34 (by decide)).trans (core5_1006 (qv inp) inp env (inv1_get hI 38 (by decide)))
  | 35, _ => exact (slice_trees prog 4 _ _ 38 K5 K6 T5 slice5 env 35 (by decide)).trans (core5_1007 (qv inp) inp env (inv1_get hI 39 (by decide)))
  | _ + 36, hk => simp only [L6, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.It
