import Hashtree.Gen.WinSseX1LW.T0a.P0
import Hashtree.Asm.X86SymWin

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86Win.SseX1 Hashtree.Asm.SpecQ Hashtree.Spec
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Gen.WinSseX1LW.T0a
open Hashtree.Gen.WinSseX1LW

def E0 (env0 : Key → W32) : Key → W32 := env0
def E1 (env0 : Key → W32) : Key → W32 := envAbs (E0 env0) (run prog 4 (mem0sW 4 rodata pushL) (fun pc => decide (pc ∈ ([24] : List Nat))) 21 KH0)

def KF : State E Lin := K1
def EF (env0 : Key → W32) : Key → W32 := E1 env0
def NS : Nat := 21

theorem inv_final (inp : Nat → Byte) (env0 : Key → W32) (hm : HMem 128 inp env0) :
    Inv1 L1 inp (E1 env0) := by
  have i0 : Inv1 L0 inp (E0 env0) := fun p hp => by cases hp
  have i1 : Inv1 L1 inp (E1 env0) := step0 inp (E0 env0) i0 hm
  exact i1

def A0 : List (Cond Lin × Bool) := [((.eq (⟨0, [0, 1]⟩ : Lin) (⟨0, [0, 1, 32]⟩ : Lin)), true)]
theorem asm0 (σ : Nat → Int) (hσ : σ 2 = 0) : ∀ p ∈ A0, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A0, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl <;>
    simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;> omega

theorem run_final (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (h0 : Mem0Rel env0 σ (mem0sW 4 rodata pushL) mem0c) (hσ : σ 2 = 0) :
    run prog 4 mem0c orcC NS (mapState env0 σ KH0) = mapState (EF env0) σ KF := by
  have m0 : Mem0Rel env0 σ (mem0sW 4 rodata pushL) mem0c := h0
  have m1 : Mem0Rel (E1 env0) σ (mem0sW 4 rodata pushL) mem0c := mem0Rel_envAbs _ σ _ mem0c (mem0sW_keyed 4 rodata pushL (by decide)) m0 _
  have r0 : run prog 4 mem0c orcC 21 (mapState env0 σ KH0) = mapState (E1 env0) σ K1 := (slice_sound env0 σ (mem0sW 4 rodata pushL) mem0c m0 prog 4 (fun pc => decide (pc ∈ ([24] : List Nat))) orcC 21 KH0 K1 T0 slice0 rfl (assumeOk_of σ K1 A0 rfl (asm0 σ hσ))).1
  show run prog 4 mem0c orcC (21) (mapState env0 σ KH0) = _
  exact r0
theorem log_final : ∀ p ∈ KF.mem, (p.1.region = rOut ∧ p.1.off.c = [0, 1] ∧ 0 ≤ p.1.off.k ∧ p.1.off.k < 0) ∨
    (p.1.region = rStack ∧ stackRel p.1.off = some p.1.off.k ∧ -264 ≤ p.1.off.k ∧ p.1.off.k < -200) := by
  decide

theorem KF_halted : KF.halted = true := by decide
theorem KF_err : KF.err = none := by decide
theorem KF_tail : KF.tail = none := by decide

end Hashtree.Gen.WinSseX1LW.T0a
