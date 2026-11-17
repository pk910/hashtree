import Hashtree.Gen.SseX1LW.It0.Final

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.SseX1LW.It0
open Hashtree.Gen.SseX1LW

def tauE : List Lin := [(⟨64, [1]⟩ : Lin), (⟨32, [0, 1]⟩ : Lin), (⟨-1, [0, 0, 1]⟩ : Lin), (⟨64, [1]⟩ : Lin), (⟨0, []⟩ : Lin)]

theorem KF_gpr : gprRel 0 (KH1.substL tauE).gpr KF.gpr = true := by decide
theorem KF_vr : vrRel 0 KH1.vr KF.vr = true := by decide
theorem KF_shape : { ({ KF with gpr := (KH1.substL tauE).gpr, vr := KH1.vr } : State E Lin) with mem := [], assume := [] } = KH1.substL tauE := by decide

theorem KF_inst (env0 : Key → W32) (σ : Nat → Int) :
    mapState (EF env0) σ KF = mapState (EF env0) σ { KF with gpr := (KH1.substL tauE).gpr, vr := KH1.vr } :=
  mapState_inst (E128 env0) σ _ _ _ _ _ _ _ _ slice128 (KH1.substL tauE).gpr KH1.vr KF_gpr KF_vr

end Hashtree.Gen.SseX1LW.It0
