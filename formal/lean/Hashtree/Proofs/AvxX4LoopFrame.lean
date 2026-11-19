
import Hashtree.Proofs.AvxX4LoopTurn

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86.AvxX4

/-!
# Iterating the `avx_x4` loop turn under an accumulated memory log

`AvxX4LoopTurn.turn_run` proves one turn from the bare pilot memory.  A real run of the
loop carries the output writes of earlier turns in front of the initial memory; the
framing lemma `X86Frame.run_fr` lets us replay a slice under such a log `M`, but only if
`M` touches neither the input nor the rodata nor the return marker (`OutLog`).

This file adds the structural invariant of one turn's own log (`KH'_log`: outputs, and
constant stack offsets below the entry offset 24), shows it is preserved by the address
map, and iterates `turn_run` over a symbolic count `c = 4j + s` with `4 <= s < 8`.
Condition `hs8` is what the final body/exit segments need: the last turn starts at a
count in `[4, 8)`, so after it the pointer arithmetic has fewer than four blocks left.
-/

namespace Hashtree.Proofs.AvxX4LoopFrame
open Hashtree.Gen.AvxX4P
open Hashtree.Proofs.AvxX4Loop
open Hashtree.Proofs.AvxX4LoopTurn

/-- Appending a log after another. -/
theorem fr_fr (M L : CLog) (s : CState) : fr M (fr L s) = fr (L ++ M) s := by
  simp only [fr, List.append_assoc]

theorem outLog_app {L M : CLog} (hL : OutLog L) (hM : OutLog M) : OutLog (L ++ M) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hM p h

/-- Structural check on the addresses of one turn's log: output cells, or constant stack
offsets below the entry offset `24`. -/
def logOkB (p : Addr Lin × Cell E Lin) : Bool :=
  if p.1.region = rOut then true
  else if p.1.region = rStack then
    decide (p.1.off.c = ([] : List Int) ∧ p.1.off.k < 24)
  else false

/-- Every write of one loop turn is an output byte or a stack byte below `24`. -/
theorem KH'_logB : KH'.mem.all logOkB = true := by decide +kernel

theorem KH'_log (p : Addr Lin × Cell E Lin) (hp : p ∈ KH'.mem) :
    p.1.region = rOut ∨ (p.1.region = rStack ∧ p.1.off.c = [] ∧ p.1.off.k < 24) := by
  have h : logOkB p = true := List.all_eq_true.mp KH'_logB p hp
  by_cases h1 : p.1.region = rOut
  · exact Or.inl h1
  by_cases h2 : p.1.region = rStack
  · right
    have hd : decide (p.1.off.c = ([] : List Int) ∧ p.1.off.k < 24) = true := by
      rw [logOkB, if_neg h1, if_pos h2] at h
      exact h
    exact ⟨h2, of_decide_eq_true hd⟩
  · exfalso
    rw [logOkB, if_neg h1, if_neg h2] at h
    cases h

/-- The turn's log, after substituting the concrete symbols, still satisfies `OutLog`. -/
theorem outLog_map_KH' (σ : Nat → Int) (e : Key → W32) :
    OutLog (KH'.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases KH'_log q hq with h | ⟨h, hc, hk⟩
  · left
    simpa [mapAddr] using h
  · right
    have hreg : (mapAddr σ q.1).region = rStack := by simpa [mapAddr] using h
    refine ⟨hreg, ?_⟩
    have hoff : q.1.off.eval σ = q.1.off.k := by
      simp [Lin.eval, hc, dotC]
    show q.1.off.eval σ < 24
    rw [hoff]
    exact hk

/-- The environment the next iteration starts from: the turn's env chain from the
restarted environment (memory keys re-read through the log). -/
def turnE (e : Key → W32) : Key → W32 :=
  envAbs (G200 (envAbs e (run prog 4 m0q (fun _ => false) 68 KHL2)))
    (run prog 4 m0q (fun _ => false) 23 K200)

/-- One full turn's length: the 68-step head, the 199 body slices and the 23-step tail. -/
def TURNLEN : Nat := 68 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)

theorem KHL2_nOnly : KHL2.nOnly = true := by decide +kernel

/-- The count at the loop head decreases by four per turn, whatever the flags. -/
theorem tau_count (σ : Nat → Int) : sigmaOf tau σ 2 = σ 2 - 4 := by
  have ht : tauAt tau 2 = (⟨-4, [0, 0, 1]⟩ : Lin) := by
    unfold tauAt tau
    split <;> rfl
  rw [sigmaOf, ht]
  simp [Lin.eval, dotC]
  omega

/-- **One framed loop turn.**  Starting from the invariant head behind an accumulated
log `M` (`OutLog M`), one turn reproduces the head under `sigmaOf tau σ` and appends its
own writes (`OutLog` again means the next turn can be framed too). -/
theorem iter_step (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMem 4 rodata 24 mem0c) (e : Key → W32) (σ : Nat → Int) (M : CLog)
    (hM : OutLog M) (hge : 4 ≤ σ 2) (hK0 : KHL2.nOnly = true) :
    ∃ e' M',
      run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHL2)) =
        fr M' (mapState e' (sigmaOf tau σ) KHL2) ∧ OutLog M' := by
  let E := ecomb e σ (view M mem0c)
  have hrel : Mem0Rel E σ m0q (view M mem0c) := by
    rw [m0q_eq]
    exact mem0Rel_of_wf 4 rodata 24 E σ (view M mem0c)
      (wf_view rodata mem0c M hM hw) (envMem_ecomb E σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHL2)) =
      fr M (mapState (turnE E) σ KH') := by
    rw [run_fr]
    rw [mapState_nOnly e E σ (fun _ => rfl) KHL2 hK0]
    exact congrArg (fr M) (turn_run E σ (view M mem0c) orcC hrel hge)
  refine ⟨turnE E,
    KH'.mem.map (fun p => (mapAddr σ p.1, mapCell (turnE E) σ p.2)) ++ M, ?_, ?_⟩
  · rw [hrun, turn_step (turnE E) σ, fr_fr]
  · exact outLog_app (outLog_map_KH' σ (turnE E)) hM

/-- `j` turns shift the symbols `j` times. -/
def sIt : Nat → (Nat → Int) → Nat → Int
  | 0, σ => σ
  | j + 1, σ => sIt j (sigmaOf tau σ)

/-- **The loop iterates.**  From the invariant head at any count `c = 4j + s` with
`4 <= s < 8`, `j` framed turns run behind the accumulated log and leave the head at
count `s`, with a log that still satisfies `OutLog`. -/
theorem loop (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMem 4 rodata 24 mem0c) (s : Nat) (hs : 4 ≤ s) (hs8 : s < 8) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog),
      σ 2 = 4 * (j : Int) + (s : Int) → OutLog M →
      ∃ e' M',
        run prog 4 mem0c orcC (j * TURNLEN) (fr M (mapState e σ KHL2)) =
          fr M' (mapState e' (sIt j σ) KHL2) ∧ OutLog M' := by
  intro j
  induction j with
  | zero =>
    intro e σ M hσ hM
    exact ⟨e, M, rfl, hM⟩
  | succ j ih =>
    intro e σ M hσ hM
    have hge : 4 ≤ σ 2 := by
      rw [hσ]
      have hsj : (0 : Int) ≤ (s : Int) := by exact_mod_cast (Nat.zero_le s)
      omega
    obtain ⟨e1, M1, hrun, hM1⟩ := iter_step mem0c orcC hw e σ M hM hge KHL2_nOnly
    have hσ1 : sigmaOf tau σ 2 = 4 * (j : Int) + (s : Int) := by
      rw [tau_count]
      rw [hσ]
      omega
    obtain ⟨e2, M2, hrun2, hM2⟩ := ih e1 (sigmaOf tau σ) M1 hσ1 hM1
    refine ⟨e2, M2, ?_, hM2⟩
    have hlen : (j + 1) * TURNLEN = TURNLEN + j * TURNLEN := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hlen, run_add, hrun, hrun2]
    rfl

end Hashtree.Proofs.AvxX4LoopFrame
