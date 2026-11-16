import Hashtree.Gen.WinSseX1LW.It0.D45
import Hashtree.Gen.WinSseX1LW.It0.D44
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.It0
open Hashtree.Gen.WinSseX1LW

theorem slice45 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K45 K46 T45 = true := by
  decide +kernel

theorem core45_0 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (44)))) :
    E.eval env (.var (.n 0)) = V (.E 0 0 (44)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_6 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (43)))) :
    E.eval env (.var (.n 6)) = V (.E 0 0 (43)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_12 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (45)))) :
    E.eval env (.var (.n 12)) = V (.A 0 0 (45)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_14 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (42))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (44))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (43))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (45))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 45)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 45)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 45)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 45)))
    (_ : env (.n 12) = QE.eval V inp (.q (.A 0 0 (45))))
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (43))))
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (44))))
    (_ : V (.A 0 0 (46)) = (V (.E 0 0 (42)) + Sigma1 (V (.E 0 0 (45))) + Ch (V (.E 0 0 (45))) (V (.E 0 0 (44))) (V (.E 0 0 (43))) + V (.KW 0 0 45)) + (Sigma0 (V (.A 0 0 (45))) + Maj (V (.A 0 0 (45))) (V (.A 0 0 (44))) (V (.A 0 0 (43))))) :
    E.eval env (.add (.add (.add (.var (.n 14)) (.add (.add (.xor (.and (.xor (.var (.n 0)) (.var (.n 6))) (.var (.n 22))) (.var (.n 6))) (.ror (.xor (.ror (.xor (.ror (.var (.n 22)) 14) (.var (.n 22))) 5) (.var (.n 22))) 6)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24))))) (.ror (.xor (.ror (.xor (.ror (.var (.n 12)) 9) (.var (.n 12))) 11) (.var (.n 12))) 2)) (.or (.and (.or (.var (.n 12)) (.var (.n 18))) (.var (.n 24))) (.and (.var (.n 12)) (.var (.n 18))))) = V (.A 0 0 (46)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_18 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 18) = QE.eval V inp (.q (.A 0 0 (43)))) :
    E.eval env (.var (.n 18)) = V (.A 0 0 (43)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_20 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 20) = QE.eval V inp (.q (.A 0 0 (42))))
    (_ : env (.n 14) = QE.eval V inp (.q (.E 0 0 (42))))
    (_ : env (.n 0) = QE.eval V inp (.q (.E 0 0 (44))))
    (_ : env (.n 6) = QE.eval V inp (.q (.E 0 0 (43))))
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (45))))
    (_ : env (.n 1011) = QE.eval V inp (.q (.KW 0 0 45)))
    (_ : env (.n 1010) = QE.eval V inp (.q (.KW 0 0 45)))
    (_ : env (.n 1009) = QE.eval V inp (.q (.KW 0 0 45)))
    (_ : env (.n 1008) = QE.eval V inp (.q (.KW 0 0 45)))
    (_ : V (.E 0 0 (46)) = V (.A 0 0 (42)) + (V (.E 0 0 (42)) + Sigma1 (V (.E 0 0 (45))) + Ch (V (.E 0 0 (45))) (V (.E 0 0 (44))) (V (.E 0 0 (43))) + V (.KW 0 0 45))) :
    E.eval env (.add (.var (.n 20)) (.add (.var (.n 14)) (.add (.add (.xor (.and (.xor (.var (.n 0)) (.var (.n 6))) (.var (.n 22))) (.var (.n 6))) (.ror (.xor (.ror (.xor (.ror (.var (.n 22)) 14) (.var (.n 22))) 5) (.var (.n 22))) 6)) (.or (.or (.and (.shr (.var (.n 1011)) 0) (.const 255)) (.shl (.and (.shr (.var (.n 1010)) 8) (.const 255)) 8)) (.or (.shl (.and (.shr (.var (.n 1009)) 16) (.const 255)) 16) (.shl (.and (.shr (.var (.n 1008)) 24) (.const 255)) 24)))))) = V (.E 0 0 (46)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_22 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 22) = QE.eval V inp (.q (.E 0 0 (45)))) :
    E.eval env (.var (.n 22)) = V (.E 0 0 (45)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_24 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 24) = QE.eval V inp (.q (.A 0 0 (44)))) :
    E.eval env (.var (.n 24)) = V (.A 0 0 (44)) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_100 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 100) = QE.eval V inp (.add (.q (.W 0 0 53)) (.q (.W 0 0 44))))
    (_ : env (.n 116) = QE.eval V inp (.or (.shl (.q (.W 0 0 45)) 25) (.shr (.q (.W 0 0 45)) 7)))
    (_ : env (.n 148) = QE.eval V inp (.q (.W 0 0 45)))
    (_ : V (.M2 0 0 44) = V (.M1 0 0 44) + V (.W 0 0 53))
    (_ : V (.M1 0 0 44) = V (.W 0 0 44) + sigma0 (V (.W 0 0 45))) :
    E.eval env (.add (.var (.n 100)) (.xor (.xor (.xor (.var (.n 116)) (.shl (.var (.n 148)) 14)) (.shr (.var (.n 148)) 18)) (.shr (.var (.n 148)) 3))) = V (.M2 0 0 44) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_101 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 101) = QE.eval V inp (.add (.q (.W 0 0 54)) (.q (.W 0 0 45))))
    (_ : env (.n 117) = QE.eval V inp (.or (.shl (.q (.W 0 0 46)) 25) (.shr (.q (.W 0 0 46)) 7)))
    (_ : env (.n 149) = QE.eval V inp (.q (.W 0 0 46)))
    (_ : V (.M2 0 0 45) = V (.M1 0 0 45) + V (.W 0 0 54))
    (_ : V (.M1 0 0 45) = V (.W 0 0 45) + sigma0 (V (.W 0 0 46))) :
    E.eval env (.add (.var (.n 101)) (.xor (.xor (.xor (.var (.n 117)) (.shl (.var (.n 149)) 14)) (.shr (.var (.n 149)) 18)) (.shr (.var (.n 149)) 3))) = V (.M2 0 0 45) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_102 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 102) = QE.eval V inp (.add (.q (.W 0 0 55)) (.q (.W 0 0 46))))
    (_ : env (.n 118) = QE.eval V inp (.or (.shl (.q (.W 0 0 47)) 25) (.shr (.q (.W 0 0 47)) 7)))
    (_ : env (.n 150) = QE.eval V inp (.q (.W 0 0 47)))
    (_ : V (.M2 0 0 46) = V (.M1 0 0 46) + V (.W 0 0 55))
    (_ : V (.M1 0 0 46) = V (.W 0 0 46) + sigma0 (V (.W 0 0 47))) :
    E.eval env (.add (.var (.n 102)) (.xor (.xor (.xor (.var (.n 118)) (.shl (.var (.n 150)) 14)) (.shr (.var (.n 150)) 18)) (.shr (.var (.n 150)) 3))) = V (.M2 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_103 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 103) = QE.eval V inp (.add (.q (.W 0 0 56)) (.q (.W 0 0 47))))
    (_ : env (.n 119) = QE.eval V inp (.or (.shl (.q (.W 0 0 48)) 25) (.shr (.q (.W 0 0 48)) 7)))
    (_ : env (.n 151) = QE.eval V inp (.q (.W 0 0 48)))
    (_ : V (.M2 0 0 47) = V (.M1 0 0 47) + V (.W 0 0 56))
    (_ : V (.M1 0 0 47) = V (.W 0 0 47) + sigma0 (V (.W 0 0 48))) :
    E.eval env (.add (.var (.n 103)) (.xor (.xor (.xor (.var (.n 119)) (.shl (.var (.n 151)) 14)) (.shr (.var (.n 151)) 18)) (.shr (.var (.n 151)) 3))) = V (.M2 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_132 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_133 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_134 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_135 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_164 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 164) = QE.eval V inp (.q (.W 0 0 48))) :
    E.eval env (.var (.n 164)) = V (.W 0 0 48) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_165 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 165) = QE.eval V inp (.q (.W 0 0 49))) :
    E.eval env (.var (.n 165)) = V (.W 0 0 49) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_166 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 166) = QE.eval V inp (.q (.W 0 0 50))) :
    E.eval env (.var (.n 166)) = V (.W 0 0 50) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_167 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 167) = QE.eval V inp (.q (.W 0 0 51))) :
    E.eval env (.var (.n 167)) = V (.W 0 0 51) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_180 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 180) = QE.eval V inp (.q (.W 0 0 52))) :
    E.eval env (.var (.n 180)) = V (.W 0 0 52) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_181 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 181) = QE.eval V inp (.q (.W 0 0 53))) :
    E.eval env (.var (.n 181)) = V (.W 0 0 53) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_182 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 182) = QE.eval V inp (.q (.W 0 0 54))) :
    E.eval env (.var (.n 182)) = V (.W 0 0 54) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_183 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 183) = QE.eval V inp (.q (.W 0 0 55))) :
    E.eval env (.var (.n 183)) = V (.W 0 0 55) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_196 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 196) = QE.eval V inp (.q (.W 0 0 56))) :
    E.eval env (.var (.n 196)) = V (.W 0 0 56) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_197 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 197) = QE.eval V inp (.q (.W 0 0 57))) :
    E.eval env (.var (.n 197)) = V (.W 0 0 57) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_198 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 198) = QE.eval V inp (.q (.W 0 0 58))) :
    E.eval env (.var (.n 198)) = V (.W 0 0 58) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_199 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 199) = QE.eval V inp (.q (.W 0 0 59))) :
    E.eval env (.var (.n 199)) = V (.W 0 0 59) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_1000 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1000) = QE.eval V inp (.q (.KW 0 0 47))) :
    E.eval env (.var (.n 1000)) = V (.KW 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_1001 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1001) = QE.eval V inp (.q (.KW 0 0 47))) :
    E.eval env (.var (.n 1001)) = V (.KW 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_1002 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1002) = QE.eval V inp (.q (.KW 0 0 47))) :
    E.eval env (.var (.n 1002)) = V (.KW 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_1003 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1003) = QE.eval V inp (.q (.KW 0 0 47))) :
    E.eval env (.var (.n 1003)) = V (.KW 0 0 47) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_1004 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1004) = QE.eval V inp (.q (.KW 0 0 46))) :
    E.eval env (.var (.n 1004)) = V (.KW 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_1005 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1005) = QE.eval V inp (.q (.KW 0 0 46))) :
    E.eval env (.var (.n 1005)) = V (.KW 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_1006 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1006) = QE.eval V inp (.q (.KW 0 0 46))) :
    E.eval env (.var (.n 1006)) = V (.KW 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem core45_1007 (V : Q → Word) (inp : Nat → Byte) (env : Key → W32)
    (_ : env (.n 1007) = QE.eval V inp (.q (.KW 0 0 46))) :
    E.eval env (.var (.n 1007)) = V (.KW 0 0 46) := by
  simp_all only [E.eval, QE.eval, Sigma0, Sigma1, Ch, Maj, sigma0, sigma1, Spec.rotr, bswap]
  all_goals bv_decide (timeout := 600)

theorem step45 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L45 inp env) (hm : HMem 128 inp env) :
    Inv1 L46 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([] : List Nat))) 38 K45)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | 0, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 0 (by decide)).trans (core45_0 (qv inp) inp env (inv1_get hI 0 (by decide)))
  | 1, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 1 (by decide)).trans (core45_6 (qv inp) inp env (inv1_get hI 1 (by decide)))
  | 2, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 2 (by decide)).trans (core45_12 (qv inp) inp env (inv1_get hI 2 (by decide)))
  | 3, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 3 (by decide)).trans (core45_14 (qv inp) inp env (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (inv1_get hI 2 (by decide)) (inv1_get hI 4 (by decide)) (inv1_get hI 7 (by decide)) (qA_succI inp 0 0 (45) (by decide)))
  | 4, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 4 (by decide)).trans (core45_18 (qv inp) inp env (inv1_get hI 4 (by decide)))
  | 5, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 5 (by decide)).trans (core45_20 (qv inp) inp env (inv1_get hI 5 (by decide)) (inv1_get hI 3 (by decide)) (inv1_get hI 0 (by decide)) (inv1_get hI 1 (by decide)) (inv1_get hI 6 (by decide)) (inv1_get hI 43 (by decide)) (inv1_get hI 42 (by decide)) (inv1_get hI 41 (by decide)) (inv1_get hI 40 (by decide)) (qE_succI inp 0 0 (45) (by decide)))
  | 6, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 6 (by decide)).trans (core45_22 (qv inp) inp env (inv1_get hI 6 (by decide)))
  | 7, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 7 (by decide)).trans (core45_24 (qv inp) inp env (inv1_get hI 7 (by decide)))
  | 8, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 8 (by decide)).trans (core45_100 (qv inp) inp env (inv1_get hI 8 (by decide)) (inv1_get hI 12 (by decide)) (inv1_get hI 16 (by decide)) (qM2 inp 0 0 44) (qM1 inp 0 0 44))
  | 9, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 9 (by decide)).trans (core45_101 (qv inp) inp env (inv1_get hI 9 (by decide)) (inv1_get hI 13 (by decide)) (inv1_get hI 17 (by decide)) (qM2 inp 0 0 45) (qM1 inp 0 0 45))
  | 10, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 10 (by decide)).trans (core45_102 (qv inp) inp env (inv1_get hI 10 (by decide)) (inv1_get hI 14 (by decide)) (inv1_get hI 18 (by decide)) (qM2 inp 0 0 46) (qM1 inp 0 0 46))
  | 11, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 11 (by decide)).trans (core45_103 (qv inp) inp env (inv1_get hI 11 (by decide)) (inv1_get hI 15 (by decide)) (inv1_get hI 19 (by decide)) (qM2 inp 0 0 47) (qM1 inp 0 0 47))
  | 12, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 12 (by decide)).trans (core45_132 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 13, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 13 (by decide)).trans (core45_133 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 14, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 14 (by decide)).trans (core45_134 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 15, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 15 (by decide)).trans (core45_135 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 16, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 16 (by decide)).trans (core45_164 (qv inp) inp env (inv1_get hI 20 (by decide)))
  | 17, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 17 (by decide)).trans (core45_165 (qv inp) inp env (inv1_get hI 21 (by decide)))
  | 18, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 18 (by decide)).trans (core45_166 (qv inp) inp env (inv1_get hI 22 (by decide)))
  | 19, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 19 (by decide)).trans (core45_167 (qv inp) inp env (inv1_get hI 23 (by decide)))
  | 20, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 20 (by decide)).trans (core45_180 (qv inp) inp env (inv1_get hI 24 (by decide)))
  | 21, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 21 (by decide)).trans (core45_181 (qv inp) inp env (inv1_get hI 25 (by decide)))
  | 22, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 22 (by decide)).trans (core45_182 (qv inp) inp env (inv1_get hI 26 (by decide)))
  | 23, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 23 (by decide)).trans (core45_183 (qv inp) inp env (inv1_get hI 27 (by decide)))
  | 24, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 24 (by decide)).trans (core45_196 (qv inp) inp env (inv1_get hI 28 (by decide)))
  | 25, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 25 (by decide)).trans (core45_197 (qv inp) inp env (inv1_get hI 29 (by decide)))
  | 26, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 26 (by decide)).trans (core45_198 (qv inp) inp env (inv1_get hI 30 (by decide)))
  | 27, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 27 (by decide)).trans (core45_199 (qv inp) inp env (inv1_get hI 31 (by decide)))
  | 28, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 28 (by decide)).trans (core45_1000 (qv inp) inp env (inv1_get hI 32 (by decide)))
  | 29, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 29 (by decide)).trans (core45_1001 (qv inp) inp env (inv1_get hI 33 (by decide)))
  | 30, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 30 (by decide)).trans (core45_1002 (qv inp) inp env (inv1_get hI 34 (by decide)))
  | 31, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 31 (by decide)).trans (core45_1003 (qv inp) inp env (inv1_get hI 35 (by decide)))
  | 32, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 32 (by decide)).trans (core45_1004 (qv inp) inp env (inv1_get hI 36 (by decide)))
  | 33, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 33 (by decide)).trans (core45_1005 (qv inp) inp env (inv1_get hI 37 (by decide)))
  | 34, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 34 (by decide)).trans (core45_1006 (qv inp) inp env (inv1_get hI 38 (by decide)))
  | 35, _ => exact (slice_trees prog 4 _ _ 38 K45 K46 T45 slice45 env 35 (by decide)).trans (core45_1007 (qv inp) inp env (inv1_get hI 39 (by decide)))
  | _ + 36, hk => simp only [L46, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.WinSseX1LW.It0
