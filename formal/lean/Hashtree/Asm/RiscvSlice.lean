import Hashtree.Asm.Cut
import Hashtree.Asm.Slice
import Hashtree.Asm.RiscvRunHom

/-!
# Slices of RV64 runs

`Slice.lean` for `Riscv.run`: `rvSliceCheck` runs the symbolic machine `n` steps from a cut and
checks (by evaluation) no failure, the cut bounds, the next cut and the tracked trees;
`rvSlice_sound` gives the concrete run.  The cut machinery (`abstract`, `envAbs`, `treeAt`,
`MemKeyed`) is machine independent and reused.
-/

set_option linter.unusedVariables false

namespace Hashtree.Asm.Riscv
open Hashtree.Asm

/-- The checks of one slice. -/
def rvSliceCheck (prog : Array Instr) (pe : Env) (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool)
    (n : Nat) (K K' : State E Lin) (trees : List (Nat × E)) : Bool :=
  let R := run prog pe mem0 orc n K
  decide (R.err = none) && decide (CutOk R) && decide (abstract R = K') &&
    trees.all (fun p => decide (treeAt R p.1 = some p.2))

theorem rvSlice_sound (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin)
    (mem0c : Addr Int → Cell W32 Int) (h0 : Mem0Rel env σ mem0s mem0c)
    (prog : Array Instr) (pe : Env) (orc orcC : Nat → Bool) (n : Nat) (K K' : State E Lin)
    (trees : List (Nat × E)) (hc : rvSliceCheck prog pe mem0s orc n K K' trees = true)
    (hK : K.err = none) (hA : AssumeOk σ K') :
    run prog pe mem0c orcC n (mapState env σ K) =
        mapState (envAbs env (run prog pe mem0s orc n K)) σ K' ∧
      ∀ p ∈ trees, envAbs env (run prog pe mem0s orc n K) (.n p.1) = p.2.eval env := by
  simp only [rvSliceCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨herr, hcut⟩, habs⟩, htrees⟩ := hc
  have hAR : AssumeOk σ (run prog pe mem0s orc n K) := by
    intro p hp; apply hA; rw [← habs]; exact hp
  refine ⟨?_, fun p hp => envAbs_treeAt env _ p.1 p.2 (htrees p hp)⟩
  rw [run_hom env σ mem0s mem0c h0 prog pe orc orcC n K hK herr hAR, ← habs,
    abstract_sound env σ _ hcut]

theorem rvSlice_trees (prog : Array Instr) (pe : Env) (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool)
    (n : Nat) (K K' : State E Lin) (trees : List (Nat × E))
    (hc : rvSliceCheck prog pe mem0 orc n K K' trees = true) (env : Key → W32) :
    ∀ k (hk : k < trees.length),
      envAbs env (run prog pe mem0 orc n K) (.n trees[k].1) = trees[k].2.eval env := by
  intro k hk
  simp only [rvSliceCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  exact envAbs_treeAt env _ _ _ (hc.2 _ (List.getElem_mem hk))

/-- Runs compose. -/
theorem rvRun_add {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    (prog : Array Instr) (pe : Env) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    ∀ (a b : Nat) (s : State α γ), run prog pe mem0 orc (a + b) s = run prog pe mem0 orc b (run prog pe mem0 orc a s)
  | 0, b, s => by simp [run]
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [run]
    split
    · rename_i hh; rw [run_halted prog pe mem0 orc b s hh]
    · split
      · exact rvRun_add prog pe mem0 orc a b _
      · rename_i hf
        rw [run_halted prog pe mem0 orc b _ (by simp only [State.fail]; split <;> rfl)]

end Hashtree.Asm.Riscv
