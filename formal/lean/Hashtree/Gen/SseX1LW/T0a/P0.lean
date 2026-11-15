import Hashtree.Gen.SseX1LW.T0a.D0
import Std.Tactic.BVDecide

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.T0a
open Hashtree.Gen.SseX1LW

theorem slice0 : sliceCheck prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([13] : List Nat))) 10 KH0 K1 T0 = true := by
  decide +kernel

theorem step0 (inp : Nat → Byte) (env : Key → W32) (hI : Inv1 L0 inp env) (hm : HMem 128 inp env) :
    Inv1 L1 inp (envAbs env (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([13] : List Nat))) 10 KH0)) := by
  apply inv1_of_get
  intro k hk
  match k, hk with
  | _ + 0, hk => simp only [L1, List.length_cons, List.length_nil] at hk; omega

end Hashtree.Gen.SseX1LW.T0a
