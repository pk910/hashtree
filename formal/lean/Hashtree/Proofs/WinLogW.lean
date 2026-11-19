import Hashtree.Asm.X86Loop
import Hashtree.Asm.X86SymW
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW

/-!
# W-mode write logs for the windows kernels

The linux W-mode loops keep these facts in `AvxX4LoopWFrame`/`AvxX4LoopWEntry`, whose
imports reach the linux pilot archives; the windows tree carries only the windows archives, so
the (kernel-independent) log machinery is restated here, verbatim.  `OutLogW σ M`: every
write of `M` is an output cell or a stack cell below the return marker `σ 9`.
-/

namespace Hashtree.Proofs.WinLogW

def OutLogW (σ : Nat → Int) (M : CLog) : Prop :=
  ∀ p ∈ M, p.1.region = rOut ∨ (p.1.region = rStack ∧ p.1.off < σ 9)

theorem outLogW_app (σ : Nat → Int) {L M : CLog} (hL : OutLogW σ L) (hM : OutLogW σ M) :
    OutLogW σ (L ++ M) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hM p h

/-- A W-mode log never holds a write to an address outside the output buffer or at the
return marker or above it. -/
theorem outLogW_ne (M : CLog) (σ : Nat → Int) (hM : OutLogW σ M) (a : Addr Int)
    (ha : a.region ≠ rOut ∧ (a.region = rStack → σ 9 ≤ a.off)) : ∀ p ∈ M, p.1 ≠ a := by
  intro p hp heq
  rcases hM p hp with h | ⟨h1, h2⟩
  · rw [heq] at h; exact ha.1 h
  · rw [heq] at h1 h2
    have := ha.2 h1
    omega

/-- `OutLogW` depends on `σ` only through `σ 9`. -/
theorem outLogW_s9 (M : CLog) {σ σ' : Nat → Int} (h9 : σ' 9 = σ 9) (hM : OutLogW σ M) :
    OutLogW σ' M := by
  intro p hp
  rcases hM p hp with h | ⟨h, hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, by rw [h9]; exact hlt⟩

/-- Older W-mode writes leave the caller's memory well formed (`push = []`, so the environment
may change). -/
theorem wfW_view (rodata : List Nat) (env env' : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (M : CLog) (hM : OutLogW σ M)
    (hw : WfMemW rodata [] env σ m) : WfMemW rodata [] env' σ (view M m) := by
  obtain ⟨hro, hret, hin, hpush⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o
    rw [view_other M m _ (outLogW_ne M σ hM _
      ⟨show (4 : Region) ≠ rOut by decide,
        fun h => absurd (show (4 : Region) = rStack from h) (by decide)⟩)]
    exact hro o
  · intro k h0 h8
    rw [view_other M m _ (outLogW_ne M σ hM _
      ⟨show rStack ≠ rOut by decide, fun _ => by simp only; omega⟩)]
    exact hret k h0 h8
  · intro o
    rw [view_other M m _ (outLogW_ne M σ hM _
      ⟨show rIn ≠ rOut by decide,
        fun h => absurd (show (1 : Region) = rStack from h) (by decide)⟩)]
    exact hin o
  · intro k c hk
    simp [plookup] at hk

/-- `WfMemW` with no push list reads `σ` only at the return marker. -/
theorem wfMemW_s9 (rodata : List Nat) (env : Key → W32) (σ σ' : Nat → Int)
    (m : Addr Int → Cell W32 Int) (hw : WfMemW rodata [] env σ m) (h9 : σ' 9 = σ 9) :
    WfMemW rodata [] env σ' m := by
  obtain ⟨hro, hret, hin, hpush⟩ := hw
  refine ⟨hro, ?_, hin, ?_⟩
  · intro k h0 h8
    rw [h9]
    exact hret k h0 h8
  · intro k c hk
    simp [plookup] at hk

/-- Structural check on the addresses of one W-mode turn's log: output cells, or stack
offsets of the form `k + σ 9` with `k < 0`. -/
def logOkBW (p : Addr Lin × Cell E Lin) : Bool :=
  if p.1.region = rOut then true
  else if p.1.region = rStack then
    decide (p.1.off.c = stkC ∧ p.1.off.k < 0)
  else false

theorem sAtW_eval (σ : Nat → Int) (k : Int) : (⟨k, stkC⟩ : Lin).eval σ = k + σ 9 := by
  simp [Lin.eval, stkC, dotC]

/-- A stack offset whose coefficient list is `stkC` evaluates to `k + σ 9`. -/
theorem eval_stk (σ : Nat → Int) (a : Lin) (hc : a.c = stkC) : a.eval σ = a.k + σ 9 := by
  simp only [Lin.eval, hc]
  exact sAtW_eval σ a.k

/-- A cut whose writes pass `logOkBW` has a W-mode log at every valuation. -/
theorem outLogW_of_logB (K : State E Lin) (h : K.mem.all logOkBW = true) (σ : Nat → Int)
    (e : Key → W32) : OutLogW σ (K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hq' : logOkBW q = true := List.all_eq_true.mp h q hq
  by_cases h1 : q.1.region = rOut
  · exact Or.inl (by simpa [mapAddr] using h1)
  by_cases h2 : q.1.region = rStack
  · have hd : decide (q.1.off.c = stkC ∧ q.1.off.k < 0) = true := by
      rw [logOkBW, if_neg h1, if_pos h2] at hq'
      exact hq'
    obtain ⟨hc, hk⟩ := of_decide_eq_true hd
    refine Or.inr ⟨by simpa [mapAddr] using h2, ?_⟩
    have hoff : q.1.off.eval σ = q.1.off.k + σ 9 := eval_stk σ q.1.off hc
    show q.1.off.eval σ < σ 9
    rw [hoff]
    omega
  · exfalso
    rw [logOkBW, if_neg h1, if_neg h2] at hq'
    cases hq'

/-- Viewing through an appended log is viewing through its parts. -/
theorem view_append (L M : CLog) (m : Addr Int → Cell W32 Int) :
    view (L ++ M) m = view L (view M m) := by
  funext a
  simp only [view, lookup_append]
  obtain ⟨rl, hl⟩ := lookup_conc_ok a L
  rw [hl]
  cases rl with
  | none => rfl
  | some c => rfl

/-- Appending a log behind another. -/
theorem fr_app (M L : CLog) (s : CState) : fr M (fr L s) = fr (L ++ M) s := by
  simp only [fr, List.append_assoc]

end Hashtree.Proofs.WinLogW
