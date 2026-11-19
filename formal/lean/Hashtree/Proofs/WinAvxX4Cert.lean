import Hashtree.Proofs.WinAvxX4Link
import Hashtree.Proofs.WinAvxX4WOut
import Hashtree.Proofs.WinAvxX4Small
import Hashtree.Proofs.WinAvxX4CertFacts

/-!
# R5: the windows avx_x4 certificate interface `X4WinCert` from R2's windows W-mode loop

`x4WinCert_of`: given the output contracts `TurnOut4W` / `TurnOut4WLast` of R2's windows-stream
loop (R2c), the interface `WinAvxX4Link.X4WinCert` holds with the step function `stepsW`:
* `0 < c < 4`: the early exit `WinAvxX4Small.small_prefixW` (28 instructions, the cut `KSmW`:
  the call registers, the 160 saved bytes in the frame);
* `4 ≤ c < 8`: `WinAvxX4WAll.x4w_runW_last_all` to the exit cut `KTE`;
* `c ≥ 8`: `WinAvxX4WAll.x4w_runW_all` with `j = c / 4 - 2`, `s = c % 4 + 4`, to `KTEs`.
The registers come from the exit cuts (`exitGprW`), the Win64 callee-saved ones (and rsi/rdi) by
preservation (`unwritten`, `run_preserve_all`), the log facts from `TurnOut4W*` on the empty
caller log.  With `KSpecC4_of_cert` this is the avx_x4 link (`KSpecC4_of_turnOut4W`).
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

/-! ## The exit registers -/

theorem eg8 : exitGprW[8]? = some (.ptr ⟨rNum, ⟨-4, [0, 0, 1]⟩⟩) := by decide +kernel
theorem eg1 : exitGprW[1]? = some (.ptr ⟨rOut, ⟨128, [0, 1]⟩⟩) := by decide +kernel
theorem eg2 : exitGprW[2]? = some (.ptr ⟨rIn, ⟨256, [1]⟩⟩) := by decide +kernel
theorem eg4 : exitGprW[4]? = some (.ptr ⟨rStack, sAt 0⟩) := by decide +kernel

theorem exit_regs (e : Key → W32) (τ : Nat → Int) (K : State E Lin) (hK : K.gpr = exitGprW) (M : CLog) :
    (fr M (mapState e τ K)).getG 8 = .ptr ⟨rNum, τ 2 - 4⟩ ∧
    (fr M (mapState e τ K)).getG 1 = .ptr ⟨rOut, τ 1 + 128⟩ ∧
    (fr M (mapState e τ K)).getG 2 = .ptr ⟨rIn, τ 0 + 256⟩ ∧
    (fr M (mapState e τ K)).getG 4 = .ptr ⟨rStack, τ 9⟩ := by
  have g : ∀ j v, exitGprW[j]? = some v → (fr M (mapState e τ K)).getG j = mapVal e τ v := by
    intro j v h
    show (mapState e τ K).getG j = _
    exact mapState_getG (by rw [hK]; exact h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [g 8 _ eg8]; simp [mapVal, mapAddr, Lin.eval, dotC]; omega
  · rw [g 1 _ eg1]; simp [mapVal, mapAddr, Lin.eval, dotC]; omega
  · rw [g 2 _ eg2]; simp [mapVal, mapAddr, Lin.eval, dotC]; omega
  · rw [g 4 _ eg4]; simp [mapVal, mapAddr, sAt_eval]

/-! ## Projections as rewrites (generic in the cut: no cut is unfolded) -/

theorem ms_err (e : Key → W32) (τ : Nat → Int) (K : State E Lin) : (mapState e τ K).err = K.err := rfl
theorem ms_tail (e : Key → W32) (τ : Nat → Int) (K : State E Lin) : (mapState e τ K).tail = K.tail := rfl
theorem fr_err (M : CLog) (s : CState) : (fr M s).err = s.err := rfl
theorem fr_tail (M : CLog) (s : CState) : (fr M s).tail = s.tail := rfl
theorem fr_vr (M : CLog) (s : CState) : (fr M s).vr = s.vr := rfl

theorem KTE_facts : KTE.err = none ∧ KTE.tail = some "hashtree_sha256_avx_x1" ∧ KTE.gpr = exitGprW := by
  have h := Hashtree.Proofs.WinAvxX4W.tailOk_true
  simp only [Hashtree.Proofs.WinAvxX4W.tailOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, t8⟩, _⟩, t10⟩, _⟩, t12⟩ := h
  exact ⟨t8, t10, t12⟩

theorem KTEs_facts : KTEs.err = none ∧ KTEs.tail = some "hashtree_sha256_avx_x1" ∧ KTEs.gpr = exitGprW := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, s11, s12, _, _, _, _, s17, _⟩ :=
    Hashtree.Proofs.WinAvxX4WStrip.stripFacts Hashtree.Proofs.WinAvxX4WStrip.stripOk_true
  exact ⟨s12, s11, s17⟩

/-! ## The certificate -/

section Spec
variable (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
  (c : Nat) (inp : Nat → Spec.Byte)

theorem preserve (n : Nat) (h : (run p4 4 m0 orcC n (mapState env σ entryWin)).err = none) :
    ∀ j, j ∈ [3, 5, 6, 7, 12, 13, 14, 15] →
      (run p4 4 m0 orcC n (mapState env σ entryWin)).getG j = (mapState env σ entryWin).getG j :=
  fun j hj => run_preserve_all p4 4 m0 orcC j (unwrittenScan_sound unwritten j hj) n _ h

theorem len (n : Nat) : (run p4 4 m0 orcC n (mapState env σ entryWin)).gpr.length = 16 :=
  Hashtree.Proofs.WinShaniCall.run_gpr_len p4 n _ (Hashtree.Proofs.WinShaniBridge.stW_len env σ)

/-- The log facts from a `TurnOut4W*` footprint on the empty caller log. -/
theorem log_facts (L : CLog) (nb : Nat) (hnb : 4 ≤ nb) (hc : nb ≤ c)
    (hL : ∀ p ∈ L, p ∈ ([] : CLog) ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * (nb : Int)) ∨
      (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)) :
    OutLogW (σ 9) L ∧ Foot (σ 9) 568 (σ 1) (32 * c) L := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rcases hL p hp with h | ⟨h, _⟩ | ⟨h, _, h'⟩
    · cases h
    · exact Or.inl h
    · exact Or.inr ⟨h, h'⟩
  · rcases hL p hp with h | ⟨h, a, b⟩ | h
    · cases h
    · left; refine ⟨h, a, ?_⟩; push_cast; omega
    · exact Or.inr h

theorem spec (hT : TurnOut4W) (hTL : TurnOut4WLast)
    (hw : WfMemW rodata4W [] env σ m0) (he : EnvMem env σ m0) (hc : σ 2 = c) (hc0 : c ≠ 0)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let f := run p4 4 m0 orcC (stepsW c) (mapState env σ entryWin)
    f.err = none ∧ f.tail = some "hashtree_sha256_avx_x1" ∧ f.gpr.length = 16 ∧
    f.getG 8 = .ptr ⟨rNum, ((c % 4 : Nat) : Int)⟩ ∧
    f.getG 1 = .ptr ⟨rOut, σ 1 + 32 * ((c - c % 4 : Nat) : Int)⟩ ∧
    f.getG 2 = .ptr ⟨rIn, σ 0 + 64 * ((c - c % 4 : Nat) : Int)⟩ ∧
    f.getG 4 = .ptr ⟨rStack, σ 9⟩ ∧
    (∀ j, j ∈ [3, 5, 6, 7, 12, 13, 14, 15] → f.getG j = (mapState env σ entryWin).getG j) ∧
    (f.vr.length = 32 ∧ ∀ v ∈ f.vr, v.length = 16) ∧
    OutLogW (σ 9) f.mem ∧ Foot (σ 9) 568 (σ 1) (32 * c) f.mem ∧ OutOk inp (σ 1) (c - c % 4) f.mem := by
  intro f
  have hlen := len env σ m0 orcC (stepsW c)
  by_cases h4 : c < 4
  · -- the early exit
    have hf : f = mapState (envAbs env (run p4 4 Hashtree.Proofs.WinAvxX4W.m0W
        Hashtree.Proofs.WinAvxX4Small.orcK 28 entryWin)) σ KSmW := by
      exact (congrArg (fun n => run p4 4 m0 orcC n (mapState env σ entryWin))
        (show stepsW c = 28 by simp [stepsW, h4])).trans
        (Hashtree.Proofs.WinAvxX4Small.small_prefixW env σ m0 orcC hw he (by omega) (by omega))
    obtain ⟨_, _, herr, _, htail, _, hgpr, _⟩ := Hashtree.Proofs.WinAvxX4Small.smallFacts
    have herr' : f.err = none := (congrArg State.err hf).trans ((ms_err _ σ KSmW).trans herr)
    have hg : ∀ j v, entryWin.gpr[j]? = some v → f.getG j = mapVal (envAbs env (run p4 4
        Hashtree.Proofs.WinAvxX4W.m0W Hashtree.Proofs.WinAvxX4Small.orcK 28 entryWin)) σ v := by
      intro j v h; rw [hf]; exact mapState_getG (by rw [hgpr]; exact h)
    have hcm : c % 4 = c := Nat.mod_eq_of_lt h4
    have hcd : c - c % 4 = 0 := by omega
    refine ⟨herr', (congrArg State.tail hf).trans ((ms_tail _ σ KSmW).trans htail), hlen, ?_, ?_, ?_, ?_,
      preserve env σ m0 orcC _ herr', by rw [hf]; exact vrOk_sound _ σ _ KSmW_facts.1, ?_⟩
    · rw [hg 8 _ Hashtree.Proofs.WinShaniBridge.entryWin_gpr8, hcm]
      simp [mapVal, mapAddr, Lin.eval_sym, hc]
    · rw [hg 1 _ Hashtree.Proofs.WinShaniBridge.entryWin_gpr1, hcd]
      simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [hg 2 _ Hashtree.Proofs.WinShaniBridge.entryWin_gpr2, hcd]
      simp [mapVal, mapAddr, Lin.eval_sym]
    · rw [hg 4 _ Hashtree.Proofs.WinShaniBridge.entryWin_gpr4]
      simp [mapVal, mapAddr, sAt_eval]
    · have hs := stackLog_sound (envAbs env (run p4 4 Hashtree.Proofs.WinAvxX4W.m0W
        Hashtree.Proofs.WinAvxX4Small.orcK 28 entryWin)) σ KSmW KSmW_facts.2
      rw [hf, hcd]
      refine ⟨fun p hp => Or.inr ⟨(hs p hp).1, (hs p hp).2.2⟩, fun p hp => Or.inr (hs p hp), ?_⟩
      intro n _ _ hn; omega
  by_cases h8 : c < 8
  · -- one pass
    have hst : stepsW c = x4wLastSteps := by simp [stepsW, h4, h8]
    have hstN : stepsW c = 16 + (Hashtree.Proofs.WinAvxX4WBody.BODYLEN + 37) := hst.trans rfl
    obtain ⟨e', M', hrun, _⟩ := Hashtree.Proofs.WinAvxX4WAll.x4w_runW_last_all env σ m0 orcC [] hw
      (fun p hp => by cases hp) (by omega) (by omega)
    rw [fr_nil] at hrun
    have hf : f = fr M' (mapState e' σ KTE) :=
      (congrArg (fun n => run p4 4 m0 orcC n (mapState env σ entryWin)) hstN).trans hrun
    obtain ⟨herr, htail, hgpr⟩ := KTE_facts
    have herr' : f.err = none :=
      (congrArg State.err hf).trans ((fr_err _ _).trans ((ms_err _ _ _).trans herr))
    obtain ⟨r8, r1, r2, r4⟩ := exit_regs e' σ KTE hgpr M'
    obtain ⟨hTf, hTo⟩ := hTL env σ m0 orcC [] inp hw (fun p hp => by cases hp) (by omega) (by omega) hin
    rw [fr_nil] at hTf hTo
    have hcm : c % 4 = c - 4 := by omega
    have hcd : c - c % 4 = 4 := by omega
    have hLf := log_facts σ c f.mem 4 (Nat.le_refl 4) (by omega) (by
      intro p hp
      rcases hTf p (by rw [← hst]; exact hp) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h.1, h.2.1, by have := h.2.2; push_cast; omega⟩)
      · exact Or.inr (Or.inr h))
    refine ⟨herr', (congrArg State.tail hf).trans ((fr_tail _ _).trans ((ms_tail _ _ _).trans htail)), hlen, ?_, ?_, ?_, ?_,
      preserve env σ m0 orcC _ herr', by rw [hf, fr_vr]; exact vrOk_sound e' σ KTE KTE_vr, hLf.1, hLf.2, ?_⟩
    · have e : σ 2 - 4 = ((c % 4 : Nat) : Int) := by rw [hcm]; push_cast [show 4 ≤ c by omega]; omega
      rw [e] at r8; rw [hf, r8]
    · have e : σ 1 + 128 = σ 1 + 32 * ((c - c % 4 : Nat) : Int) := by rw [hcd]; push_cast; omega
      rw [e] at r1; rw [hf, r1]
    · have e : σ 0 + 256 = σ 0 + 64 * ((c - c % 4 : Nat) : Int) := by rw [hcd]; push_cast; omega
      rw [e] at r2; rw [hf, r2]
    · rw [hf, r4]
    · rw [hcd]; show OutOk inp (σ 1) 4 (run p4 4 m0 orcC (stepsW c) _).mem; rw [hst]; exact hTo
  · -- several passes
    have hj : σ 2 = 4 * (((c / 4 - 2 : Nat) : Int) + 1) + ((c % 4 + 4 : Nat) : Int) := by
      rw [hc]; push_cast [show 2 ≤ c / 4 by omega]; omega
    have hst : stepsW c = x4wRunSteps (c / 4 - 2) := by simp [stepsW, h4, h8]
    have hstN : stepsW c = 16 + (Hashtree.Proofs.WinAvxX4WLoop.TURNLEN + ((c / 4 - 2) *
        Hashtree.Proofs.WinAvxX4WLoop.TURNLEN + (Hashtree.Proofs.WinAvxX4WBody.BODYLEN + 37))) := hst.trans rfl
    obtain ⟨e', M', hrun, _⟩ := Hashtree.Proofs.WinAvxX4WAll.x4w_runW_all env σ m0 orcC [] hw
      (fun p hp => by cases hp) (c / 4 - 2) (c % 4 + 4) (by omega) (by omega) hj
    rw [fr_nil] at hrun
    have hf : f = fr M' (mapState e' (Hashtree.Proofs.WinAvxX4WLoop.sItW (c / 4 - 2 + 1) σ) KTEs) := by
      exact (congrArg (fun n => run p4 4 m0 orcC n (mapState env σ entryWin)) hstN).trans hrun
    obtain ⟨herr, htail, hgpr⟩ := KTEs_facts
    have herr' : f.err = none :=
      (congrArg State.err hf).trans ((fr_err _ _).trans ((ms_err _ _ _).trans herr))
    obtain ⟨r8, r1, r2, r4⟩ := exit_regs e' (Hashtree.Proofs.WinAvxX4WLoop.sItW (c / 4 - 2 + 1) σ) KTEs hgpr M'
    rw [Hashtree.Proofs.WinAvxX4WLoop.sItW_count] at r8
    rw [Hashtree.Proofs.WinAvxX4WLoop.sItW_out] at r1
    rw [Hashtree.Proofs.WinAvxX4WLoop.sItW_in] at r2
    rw [Hashtree.Proofs.WinAvxX4WLoop.sItW_s9] at r4
    obtain ⟨hTf, hTo⟩ := hT env σ m0 orcC [] (c / 4 - 2) (c % 4 + 4) inp hw (fun p hp => by cases hp)
      (by omega) (by omega) hj hin
    rw [fr_nil] at hTf hTo
    have hcd : c - c % 4 = 4 * (c / 4 - 2 + 2) := by omega
    have hLf := log_facts σ c f.mem (4 * (c / 4 - 2 + 2)) (by omega) (by omega) (by
      intro p hp
      rcases hTf p (by rw [← hst]; exact hp) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h.1, h.2.1, by have := h.2.2; push_cast [show 2 ≤ c / 4 by omega] at this ⊢; omega⟩)
      · exact Or.inr (Or.inr h))
    refine ⟨herr', (congrArg State.tail hf).trans ((fr_tail _ _).trans ((ms_tail _ _ _).trans htail)), hlen, ?_, ?_, ?_, ?_,
      preserve env σ m0 orcC _ herr', by rw [hf, fr_vr]; exact vrOk_sound _ _ KTEs KTEs_vr, hLf.1, hLf.2, ?_⟩
    · have e : σ 2 - 4 * ((c / 4 - 2 + 1 : Nat) : Int) - 4 = ((c % 4 : Nat) : Int) := by
        push_cast [show 2 ≤ c / 4 by omega]; omega
      rw [e] at r8; rw [hf, r8]
    · have e : σ 1 + 128 * ((c / 4 - 2 + 1 : Nat) : Int) + 128 = σ 1 + 32 * ((c - c % 4 : Nat) : Int) := by
        rw [hcd]; push_cast [show 2 ≤ c / 4 by omega]; omega
      rw [e] at r1; rw [hf, r1]
    · have e : σ 0 + 256 * ((c / 4 - 2 + 1 : Nat) : Int) + 256 = σ 0 + 64 * ((c - c % 4 : Nat) : Int) := by
        rw [hcd]; push_cast [show 2 ≤ c / 4 by omega]; omega
      rw [e] at r2; rw [hf, r2]
    · rw [hf, r4]
    · rw [hcd]; show OutOk inp (σ 1) _ (run p4 4 m0 orcC (stepsW c) _).mem; rw [hst]; exact hTo

end Spec

/-- **`X4WinCert` from R2c's output contracts of the windows avx_x4 loop.** -/
def x4WinCert_of (hT : TurnOut4W) (hTL : TurnOut4WLast) : X4WinCert where
  steps := stepsW
  spec := fun env σ m0 orcC c inp hw he hc hc0 hin => spec env σ m0 orcC c inp hT hTL hw he hc hc0 hin

/-- **The avx_x4 link**, given the output contracts. -/
theorem KSpecC4_of_turnOut4W (hT : TurnOut4W) (hTL : TurnOut4WLast) (env : Key → W32) (σ : Nat → Int)
    (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte) :
    KSpecC4 (fun c => if c = 0 then 4 else (x4WinCert_of hT hTL).steps c) env σ m0 orcC c inp :=
  KSpecC4_of_cert (x4WinCert_of hT hTL) env σ m0 orcC c inp

end Hashtree.Proofs.WinAvxX4Cert
