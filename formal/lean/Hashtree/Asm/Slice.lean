import Hashtree.Asm.Cut
import Hashtree.Asm.X86RunHom

/-!
# Slices: one kernel-checked symbolic run between two cuts

`sliceCheck` runs the symbolic machine `n` steps from the cut `K`, and checks (by evaluation)
that the run did not fail, that the bounds of the cut hold, that its cut is `K'`, and that the
tracked locations hold the given trees.  `slice_sound`: then the concrete machine, started in
any state `K` denotes, ends in the state `K'` denotes under the environment of the run, and every
tracked variable's value is the value of its tree.
-/

set_option linter.unusedVariables false

namespace Hashtree.Asm
open Hashtree.Asm.X86

/-- The expression at a location variable of a state (as `envAbs` reads it). -/
def treeAt (R : State E Lin) (i : Nat) : Option E :=
  if i < 100 then
    match R.gpr[i / 2]? with
    | some (.num lo hi) => some (if i % 2 = 0 then lo else hi)
    | _ => none
  else if i < 1000 then
    match R.vr[(i - 100) / 16]? with
    | some v => v[(i - 100) % 16]?
    | none => none
  else
    match R.mem[i - 1000]? with
    | some (_, .dat x _) => some x
    | _ => none

theorem envAbs_treeAt (env : Key → W32) (R : State E Lin) (i : Nat) (t : E) (h : treeAt R i = some t) :
    envAbs env R (.n i) = t.eval env := by
  simp only [treeAt] at h
  simp only [envAbs]
  by_cases h1 : i < 100
  · rw [if_pos h1] at h ⊢
    split at h
    · rename_i lo hi heq
      rw [heq]
      split at h <;> (cases h; simp_all)
    · cases h
  · rw [if_neg h1] at h ⊢
    by_cases h2 : i < 1000
    · rw [if_pos h2] at h ⊢
      split at h
      · rename_i v heq
        rw [heq]
        simp [List.getD_eq_getElem?_getD, h]
      · cases h
    · rw [if_neg h2] at h ⊢
      split at h
      · rename_i a x k heq
        cases h; rw [heq]
      · cases h

/-- The checks of one slice. -/
def sliceCheck (prog : Array Instr) (ro : Region) (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool)
    (n : Nat) (K K' : State E Lin) (trees : List (Nat × E)) : Bool :=
  let R := run prog ro mem0 orc n K
  decide (R.err = none) && decide (CutOk R) && decide (abstract R = K') &&
    trees.all (fun p => decide (treeAt R p.1 = some p.2))

/-- Initial memory whose unknown bytes are memory keys: environments that agree on those keys
relate it to the same concrete memory. -/
def MemKeyed (mem0s : Addr Lin → Cell E Lin) : Prop :=
  ∀ a, (∃ v k, mem0s a = .dat (.const v) k) ∨ (∃ r o k, mem0s a = .dat (.var (.m r o)) k) ∨
    (∃ p k, mem0s a = .pb p k)

theorem mem0Rel_envAbs (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin)
    (mem0c : Addr Int → Cell W32 Int) (hk : MemKeyed mem0s) (h0 : Mem0Rel env σ mem0s mem0c)
    (R : State E Lin) : Mem0Rel (envAbs env R) σ mem0s mem0c := by
  intro a ha
  rw [h0 a ha]
  rcases hk a with ⟨v, k, h⟩ | ⟨r, o, k, h⟩ | ⟨p, k, h⟩ <;> rw [h] <;> rfl

theorem slice_sound (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin)
    (mem0c : Addr Int → Cell W32 Int) (h0 : Mem0Rel env σ mem0s mem0c)
    (prog : Array Instr) (ro : Region) (orc orcC : Nat → Bool) (n : Nat) (K K' : State E Lin)
    (trees : List (Nat × E)) (hc : sliceCheck prog ro mem0s orc n K K' trees = true)
    (hK : K.err = none) (hA : AssumeOk σ K') :
    run prog ro mem0c orcC n (mapState env σ K) =
        mapState (envAbs env (run prog ro mem0s orc n K)) σ K' ∧
      ∀ p ∈ trees, envAbs env (run prog ro mem0s orc n K) (.n p.1) = p.2.eval env := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨herr, hcut⟩, habs⟩, htrees⟩ := hc
  have hAR : AssumeOk σ (run prog ro mem0s orc n K) := by
    intro p hp; apply hA; rw [← habs]; exact hp
  refine ⟨?_, fun p hp => envAbs_treeAt env _ p.1 p.2 (htrees p hp)⟩
  rw [run_hom env σ mem0s mem0c h0 prog ro orc orcC n K hK herr hAR, ← habs,
    abstract_sound env σ _ hcut]

/-- Runs compose. -/
theorem run_add {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    ∀ (a b : Nat) (s : State α γ), run prog ro mem0 orc (a + b) s = run prog ro mem0 orc b (run prog ro mem0 orc a s)
  | 0, b, s => by simp [run]
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [run]
    split
    · rename_i hh; rw [run_halted prog ro mem0 orc b s hh]
    · split
      · exact run_add prog ro mem0 orc a b _
      · rename_i hf
        rw [run_halted prog ro mem0 orc b _ (by simp only [State.fail]; split <;> rfl)]

end Hashtree.Asm
