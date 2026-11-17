import Hashtree.Proofs.WinAvxX4Link
import Hashtree.Proofs.WinAvxX4WOut
import Hashtree.Proofs.WinAvxX4Small

/-!
# R5: kernel facts for `WinAvxX4Cert`

The step function `stepsW` of the windows avx_x4 certificate, the scan that the stream never
writes the Win64 callee-saved registers (nor rsi/rdi), the 32 x 16 vector files of the exit cuts
`KSmW`, `KTE`, `KTEs`, and the stack-only log of the early exit `KSmW` (inside `[σ 9 - 568, σ 9)`).
Kept apart so that `WinAvxX4Cert` checks in seconds.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvxX4Cert

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.RunExit
open Hashtree.Proofs.WinChain (p4)
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk)
open Hashtree.Proofs.ShaniW (OutLogW fr_nil)
open Hashtree.Proofs.WinAvxX4Link (X4WinCert rodata4W KSpecC4_of_cert)
open Hashtree.Proofs.WinAvxX4Bridge (KSpecC4)
open Hashtree.Proofs.WinAvxX4WOut (TurnOut4W TurnOut4WLast x4wRunSteps x4wLastSteps)
open Hashtree.Proofs.WinShaniSeedAlign (mapState_getG)
open Hashtree.Proofs.WrapperAmd64 (sAt_eval)
open Hashtree.Proofs.WinAvxX4W (exitGprW KTE)
open Hashtree.Proofs.WinAvxX4WStrip (KTEs)
open Hashtree.Proofs.WinAvxX4Small (KSmW)

/-- The step function: early exit, one pass, or `c / 4 - 1` passes. -/
def stepsW (c : Nat) : Nat := if c < 4 then 28 else if c < 8 then x4wLastSteps else x4wRunSteps (c / 4 - 2)

/-! ## Kernel facts -/

theorem unwritten : unwrittenScan p4 [3, 5, 6, 7, 12, 13, 14, 15] = true := by decide +kernel

/-- The vector file shape of the three exit cuts and the stack-only log of the early exit. -/
def vrOk (K : State E Lin) : Bool := (K.vr.length == 32) && K.vr.all (fun v => v.length == 16)

def stackLog (K : State E Lin) : Bool :=
  K.mem.all (fun p => (p.1.region == rStack) && (p.1.off.c == stkC) && decide (-568 ≤ p.1.off.k) &&
    decide (p.1.off.k < 0))

theorem KSmW_facts : vrOk KSmW = true ∧ stackLog KSmW = true := by
  constructor <;> decide +kernel
theorem KTE_vr : vrOk KTE = true := by decide +kernel
theorem KTEs_vr : vrOk KTEs = true := by decide +kernel

theorem vrOk_sound (e : Key → W32) (τ : Nat → Int) (K : State E Lin) (h : vrOk K = true) :
    (mapState e τ K).vr.length = 32 ∧ ∀ v ∈ (mapState e τ K).vr, v.length = 16 := by
  simp only [vrOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨by simp [mapState, h.1], fun v hv => ?_⟩
  simp only [mapState, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  simpa using h.2 w hw

theorem stackLog_sound (e : Key → W32) (τ : Nat → Int) (K : State E Lin) (h : stackLog K = true) :
    ∀ p ∈ (mapState e τ K).mem, p.1.region = rStack ∧ τ 9 - 568 ≤ p.1.off ∧ p.1.off < τ 9 := by
  intro p hp
  simp only [mapState, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [stackLog, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h q hq
  obtain ⟨⟨r, ⟨k, cs⟩⟩, cell⟩ := q
  simp only at h1 h2 h3 h4
  subst h1; subst h2
  have := sAt_eval τ k
  simp only [mapAddr]
  refine ⟨by first | rfl | trivial, ?_, ?_⟩ <;> simp only [sAt] at this <;> rw [show (⟨k, stkC⟩ : Lin) = sAt k from rfl, sAt_eval] <;> omega

end Hashtree.Proofs.WinAvxX4Cert
