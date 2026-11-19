import Hashtree.Proofs.AvxX4LoopW
import Hashtree.Proofs.AvxX4LoopFrame

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.AvxX4
namespace Hashtree.Proofs.AvxX4LoopWFrame
open Hashtree.Gen.AvxX4P
open Hashtree.Proofs.AvxX4W
open Hashtree.Proofs.AvxX4Loop
open Hashtree.Proofs.AvxX4LoopTurn
open Hashtree.Proofs.AvxX4LoopW
open Hashtree.Proofs.AvxX4LoopFrame

/-!
# Framing and iteration of the W-mode x4 loop turn

`AvxX4LoopW.turn_runW` proves one turn from the rebased loop head.  Iterating it needs the
same two ingredients as the absolute-stack version (`AvxX4LoopFrame`): a log condition under
which older writes leave the caller's memory well formed (`WfMemW`), and the observation that
the turn ends in a substitution instance of the head.

The stack in W mode is relative: the return marker sits at `σ 9`, and the kernel's frame is
the 408 bytes *below* it, so a log is harmless when its stack writes are all below `σ 9`
(`OutLogW`).  `σ 9` is untouched by the loop substitution `tau`, so the condition survives
every turn.
-/

/-! ## Logs that only hold output and below-frame stack bytes -/

/-- Older writes in W mode: output bytes, or stack bytes below the return marker at `σ 9`. -/
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

/-- Older writes leave the caller's memory well formed, so the next turn starts from the
same well-formedness invariant.  The pushed-cell clause is vacuous here (`push = []`), which
is why the environment may change (`env` at the call, `env'` after the turn). -/
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

/-! ## The turn's log -/

/-- Structural check on the addresses of one W-mode turn's log: output cells, or stack
offsets of the form `k + σ 9` with `k < 0`. -/
def logOkBW (p : Addr Lin × Cell E Lin) : Bool :=
  if p.1.region = rOut then true
  else if p.1.region = rStack then
    decide (p.1.off.c = stkC ∧ p.1.off.k < 0)
  else false

/-- Every write of one W-mode loop turn is an output byte or a stack byte below `σ 9`. -/
theorem KHpW_logB : KHpW.mem.all logOkBW = true := by decide +kernel

theorem KHpW_log (p : Addr Lin × Cell E Lin) (hp : p ∈ KHpW.mem) :
    p.1.region = rOut ∨ (p.1.region = rStack ∧ p.1.off.c = stkC ∧ p.1.off.k < 0) := by
  have h : logOkBW p = true := List.all_eq_true.mp KHpW_logB p hp
  by_cases h1 : p.1.region = rOut
  · exact Or.inl h1
  by_cases h2 : p.1.region = rStack
  · right
    have hd : decide (p.1.off.c = stkC ∧ p.1.off.k < 0) = true := by
      rw [logOkBW, if_neg h1, if_pos h2] at h
      exact h
    exact ⟨h2, of_decide_eq_true hd⟩
  · exfalso
    rw [logOkBW, if_neg h1, if_neg h2] at h
    cases h

/-- The evaluation of an `sAt` offset: `k + σ 9`. -/
theorem sAt_eval (σ : Nat → Int) (k : Int) : (⟨k, stkC⟩ : Lin).eval σ = k + σ 9 := by
  simp [Lin.eval, stkC, dotC]

/-- A stack offset whose coefficient list is `stkC` evaluates to `k + σ 9`. -/
theorem eval_stk (σ : Nat → Int) (a : Lin) (hc : a.c = stkC) : a.eval σ = a.k + σ 9 := by
  simp only [Lin.eval, hc]
  exact sAt_eval σ a.k

/-- The turn's log, after substituting the concrete symbols, still satisfies `OutLogW`. -/
theorem outLogW_map_KHpW (σ : Nat → Int) (e : Key → W32) :
    OutLogW σ (KHpW.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases KHpW_log q hq with h | ⟨h, hc, hk⟩
  · left
    simpa [mapAddr] using h
  · right
    have hreg : (mapAddr σ q.1).region = rStack := by simpa [mapAddr] using h
    refine ⟨hreg, ?_⟩
    have hoff : q.1.off.eval σ = q.1.off.k + σ 9 := eval_stk σ q.1.off hc
    show q.1.off.eval σ < σ 9
    rw [hoff]
    omega

/-- The loop substitution leaves the stack base symbol alone. -/
theorem tau_s9 (σ : Nat → Int) : sigmaOf tau σ 9 = σ 9 := by
  have ht : tauAt tau 9 = (⟨0, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩ : Lin) := by
    unfold tauAt tau
    split <;> rfl
  rw [sigmaOf, ht]
  simp [Lin.eval, dotC]

/-- `j` turns leave the stack base symbol alone. -/
theorem sIt_s9 : ∀ (j : Nat) (σ : Nat → Int), sIt j σ 9 = σ 9
  | 0, _ => rfl
  | j + 1, σ => by
    rw [show sIt (j + 1) σ = sIt j (sigmaOf tau σ) from rfl,
      sIt_s9 j (sigmaOf tau σ), tau_s9]

/-- The environment the next W-mode iteration starts from: the turn's env chain from the
restarted environment (memory keys re-read through the log). -/
def turnEW (e : Key → W32) : Key → W32 :=
  envAbs (G200W (envAbs e (run prog 4 m0W (fun _ => false) 68 KHL2W)))
    (run prog 4 m0W (fun _ => false) 23 K200W)

/-- The loop step in the concrete state space: the state after a W-mode turn is an instance
of `KHL2W` under `sigmaOf tau σ`, seen through the turn's memory log. -/
theorem turn_stepW (e : Key → W32) (σ : Nat → Int) :
    mapState e σ KHpW =
      fr (KHpW.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)))
        (mapState e (sigmaOf tau σ) KHL2W) :=
  mapState_reached e σ KHpW KHL2W tau KHpW_shape

/-- `WfMemW` reads only the stack base symbol `σ 9` (and only in its return-marker clause),
so any `σ'` with the same stack base satisfies it too. -/
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

/-- **One framed W-mode loop turn.**  Starting from the invariant head behind an accumulated
log `M` (`OutLogW σ M`), one turn reproduces the head under `sigmaOf tau σ` and appends its
own writes, so the next turn is framed too. -/
theorem iter_stepW (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env : Key → W32) (σ0 : Nat → Int) (σ : Nat → Int)
    (hw : WfMemW rodata [] env σ0 mem0c) (h9 : σ 9 = σ0 9)
    (e : Key → W32) (M : CLog)
    (hM : OutLogW σ M) (hge : 4 ≤ σ 2) :
    ∃ e' M',
      run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHL2W)) =
        fr M' (mapState e' (sigmaOf tau σ) KHL2W) ∧ OutLogW (sigmaOf tau σ) M' := by
  let E := ecomb e σ (view M mem0c)
  have hrel : Mem0Rel E σ m0W (view M mem0c) := by
    rw [m0W_eq]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c)
      (wfW_view rodata env E σ mem0c M hM
        (wfMemW_s9 rodata env σ0 σ mem0c hw h9)) (envMem_ecomb E σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHL2W)) =
      fr M (mapState (turnEW E) σ KHpW) := by
    rw [run_fr]
    rw [mapState_nOnly e E σ (fun _ => rfl) KHL2W KHL2W_nOnly]
    exact congrArg (fr M) (turn_runW E σ (view M mem0c) orcC hrel hge)
  refine ⟨turnEW E,
    KHpW.mem.map (fun p => (mapAddr σ p.1, mapCell (turnEW E) σ p.2)) ++ M, ?_, ?_⟩
  · rw [hrun, turn_stepW (turnEW E) σ, fr_fr]
  · have h := outLogW_app σ (outLogW_map_KHpW σ (turnEW E)) hM
    intro p hp
    rw [tau_s9]
    exact h p hp

/-- **The W-mode loop iterates.**  From the invariant head at any count `c = 4j + s` with
`4 ≤ s < 8`, `j` framed turns run behind the accumulated log and leave the head at count `s`,
with a log that still satisfies `OutLogW`. -/
theorem loopW (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env : Key → W32) (σ0 : Nat → Int) (hw : WfMemW rodata [] env σ0 mem0c)
    (s : Nat) (hs : 4 ≤ s) (hs8 : s < 8) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog),
      σ 2 = 4 * (j : Int) + (s : Int) → σ 9 = σ0 9 → OutLogW σ M →
      ∃ e' M',
        run prog 4 mem0c orcC (j * TURNLEN) (fr M (mapState e σ KHL2W)) =
          fr M' (mapState e' (sIt j σ) KHL2W) ∧ OutLogW (sIt j σ) M' := by
  intro j
  induction j with
  | zero =>
    intro e σ M hσ h9 hM
    exact ⟨e, M, rfl, hM⟩
  | succ j ih =>
    intro e σ M hσ h9 hM
    have hge : 4 ≤ σ 2 := by
      rw [hσ]
      have hsj : (0 : Int) ≤ (s : Int) := by exact_mod_cast (Nat.zero_le s)
      omega
    obtain ⟨e1, M1, hrun, hM1⟩ := iter_stepW mem0c orcC env σ0 σ hw h9 e M hM hge
    have hσ1 : sigmaOf tau σ 2 = 4 * (j : Int) + (s : Int) := by
      rw [tau_count]
      rw [hσ]
      omega
    have h9' : sigmaOf tau σ 9 = σ0 9 := by rw [tau_s9]; exact h9
    obtain ⟨e2, M2, hrun2, hM2⟩ := ih e1 (sigmaOf tau σ) M1 hσ1 h9' hM1
    refine ⟨e2, M2, ?_, hM2⟩
    have hlen : (j + 1) * TURNLEN = TURNLEN + j * TURNLEN := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hlen, run_add, hrun, hrun2]
    rfl

end Hashtree.Proofs.AvxX4LoopWFrame
