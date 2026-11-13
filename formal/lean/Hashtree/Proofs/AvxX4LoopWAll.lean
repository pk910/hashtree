import Hashtree.Proofs.AvxX4LoopWEntry

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.AvxX4
namespace Hashtree.Proofs.AvxX4LoopWAll
open Hashtree.Gen.AvxX4P
open Hashtree.Proofs.AvxX4W
open Hashtree.Proofs.AvxX4Loop
open Hashtree.Proofs.AvxX4LoopTurn
open Hashtree.Proofs.AvxX4LoopW
open Hashtree.Proofs.AvxX4LoopFrame
open Hashtree.Proofs.AvxX4LoopWFrame
open Hashtree.Proofs.AvxX4LoopWExit

/-!
# Every count for the W-mode x4 kernel

The composite the wrapper needs: from the call state `entryW` at any count `c ≥ 4`, the
kernel reaches the exit cut `K201W` (a tail call into `hashtree_sha256_avx_x1` with the
relative stack restored), behind the caller's log.

`x4_runW_last` handles the residual batch `4 ≤ c < 8`: the 72-step entry reaches the body,
and the body plus the 27-step exit slice reach the exit cut.  `x4_runW` handles
`c = 4 * (j + 1) + s` with `4 ≤ s < 8` and `j` further turns: the entry reaches the first
body cut, the body and the 23-step tail complete the first turn (the first turn's head slice
is part of the entry), `loopW` runs `j` more framed turns, and the final segment
(68 + body + 27) reaches the exit cut at the residual count `s`.

What these theorems establish is the *state trajectory*: the run's length, the resulting
environment, and the accumulated log (`OutLogW`, so a caller above can frame on it).  Output
byte correctness in W mode is not part of it (the W-mode slices are checked with empty tree
lists); see `formal/notes/R2.md`.
-/

/-- `WfMemW` does not depend on the environment when nothing is pushed. -/
theorem wfMemW_env (rodata : List Nat) (env env' : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (hw : WfMemW rodata [] env σ m) :
    WfMemW rodata [] env' σ m := by
  obtain ⟨hro, hret, hin, hpush⟩ := hw
  refine ⟨hro, hret, hin, ?_⟩
  intro k c hk
  simp [plookup] at hk

/-- `j` turns decrease the count symbol by `4j`. -/
theorem sIt_2W : ∀ (j : Nat) (σ : Nat → Int), sIt j σ 2 = σ 2 - 4 * (j : Int)
  | 0, σ => by simp [sIt]
  | j + 1, σ => by
    rw [show sIt (j + 1) σ = sIt j (sigmaOf tau σ) from rfl, sIt_2W j (sigmaOf tau σ),
      tau_count]
    omega

/-- The environment invariant used by the body after the entry segment. -/
theorem entry_relW (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) :
    Mem0Rel (G1W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) m0W (view M mem0c) := by
  have hrelW0 : WfMemW rodata [] env0 σ (view M mem0c) :=
    wfW_view rodata env0 env0 σ mem0c M hM hw
  have hrelE0 : Mem0Rel (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) m0W (view M mem0c) := by
    rw [m0W_eq]
    exact mem0RelW_of_wf rodata [] _ _ (view M mem0c)
      (wfMemW_upd15 rodata env0 _ σ (view M mem0c) hrelW0) (fun r off => rfl)
  exact mem0Rel_envAbs (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) m0W (view M mem0c)
    m0W_keyed hrelE0 (run prog 4 m0W orcW 72 entryWx)

/-- **The residual batch `4 ≤ c < 8`.**  Entry, body and exit slice reach the exit cut. -/
theorem x4_runW_last (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (s : Nat) (hs : 4 ≤ s) (hs8 : s < 8) (hc : σ 2 = (s : Int)) :
    ∃ e' M',
      run prog 4 mem0c orcC (72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)) (fr M (mapState env0 σ entryW)) =
        fr M' (mapState e' (sIt 0 (upd15 σ)) K201W) ∧
      OutLogW (sIt 0 (upd15 σ))
        (K201W.mem.map (fun p => (mapAddr (sIt 0 (upd15 σ)) p.1,
          mapCell e' (sIt 0 (upd15 σ)) p.2)) ++ M') := by
  have hM15 : OutLogW (upd15 σ) M := outLogW_s9 M (upd15_9 σ) hM
  have hs4 : (4 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hs8' : (s : Int) < 8 := by exact_mod_cast hs8
  have hc15 : upd15 σ 2 = (s : Int) := by
    have h : upd15 σ 2 = σ 2 := by simp [upd15]
    rw [h]
    exact hc
  have hge15 : 4 ≤ upd15 σ 2 := by rw [hc15]; exact hs4
  have hlt15 : upd15 σ 2 < 8 := by rw [hc15]; exact hs8'
  have hentry := entry_runW env0 σ mem0c orcC M hw hge15 hM15
  have hrel1 : Mem0Rel (G1W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) m0W (view M mem0c) :=
    entry_relW env0 σ mem0c M hw hM
  have hbody := body_runW (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx)) (upd15 σ) (view M mem0c) orcC hrel1 hge15
  have hm2 := body_memW (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx)) (upd15 σ) (view M mem0c) hrel1
  have hexit := (slice_sound (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) m0W (view M mem0c) hm2 prog 4
    orcExitW orcC 27 K200W K201W [] exit27W K200W_err
    (assumeOk_of (upd15 σ) K201W A1W K201W_assume (asm1geW (upd15 σ) hge15 hlt15))).1
  have sA := run_add prog 4 mem0c orcC 72 ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27) (fr M (mapState env0 σ entryW))
  have sB := run_add prog 4 mem0c orcC (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) 27
    (run prog 4 mem0c orcC 72 (fr M (mapState env0 σ entryW)))
  have sC : run prog 4 mem0c orcC (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (fr M (mapState (G1W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) K1W)) =
      fr M (run prog 4 (view M mem0c) orcC (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (mapState (G1W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) K1W)) := by
    rw [run_fr]
  have sD : run prog 4 mem0c orcC 27
        (fr M (mapState (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) K200W)) =
      fr M (run prog 4 (view M mem0c) orcC 27
        (mapState (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) K200W)) := by
    rw [run_fr]
  refine ⟨envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W orcExitW 27 K200W), M, ?_, ?_⟩
  · rw [sA, sB, hentry, sC, hbody, sD, hexit]
    rfl
  · exact outLogW_app (upd15 σ)
      (outLogW_map_K201W (upd15 σ) (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W orcExitW 27 K200W))) hM15

/-- **Every count `c = 4 * (j + 1) + s` with `4 ≤ s < 8`.**  One turn (entry, body, tail),
`j` framed turns, and the final segment reach the exit cut. -/
theorem x4_runW (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (j s : Nat) (hs : 4 ≤ s) (hs8 : s < 8)
    (hc : σ 2 = 4 * ((j : Int) + 1) + (s : Int)) :
    ∃ e' M',
      run prog 4 mem0c orcC (((72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)) + j * TURNLEN) + (68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)))
          (fr M (mapState env0 σ entryW)) =
        fr M' (mapState e' (sIt (j + 1) (upd15 σ)) K201W) ∧
      OutLogW (sIt (j + 1) (upd15 σ))
        (K201W.mem.map (fun p => (mapAddr (sIt (j + 1) (upd15 σ)) p.1,
          mapCell e' (sIt (j + 1) (upd15 σ)) p.2)) ++ M') := by
  let σ1 : Nat → Int := sigmaOf tau (upd15 σ)
  let L1 : CLog :=
    KHpW.mem.map (fun p => (mapAddr (upd15 σ) p.1, mapCell (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W (fun _ => false) 23 K200W)) (upd15 σ) p.2)) ++ M
  have hM15 : OutLogW (upd15 σ) M := outLogW_s9 M (upd15_9 σ) hM
  have hs4 : (4 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hc15 : upd15 σ 2 = 4 * ((j : Int) + 1) + (s : Int) := by
    have h : upd15 σ 2 = σ 2 := by simp [upd15]
    rw [h]
    exact hc
  have hge15 : 4 ≤ upd15 σ 2 := by rw [hc15]; omega
  have hentry := entry_runW env0 σ mem0c orcC M hw hge15 hM15
  have hrel1 : Mem0Rel (G1W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) m0W (view M mem0c) :=
    entry_relW env0 σ mem0c M hw hM
  have hbody := body_runW (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx)) (upd15 σ) (view M mem0c) orcC hrel1 hge15
  have hm2 := body_memW (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx)) (upd15 σ) (view M mem0c) hrel1
  have htail := (slice_sound (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) m0W (view M mem0c) hm2 prog 4
    (fun _ => false) orcC 23 K200W KHpW [] KHpW_slice K200W_err
    (assumeOk_of (upd15 σ) KHpW A0 KHpW_assume (asm0ge (upd15 σ) hge15))).1
  have hMB : run prog 4 mem0c orcC ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)
        (fr M (mapState (G1W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) K1W)) = fr L1 (mapState (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W (fun _ => false) 23 K200W)) σ1 KHL2W) := by
    rw [run_fr, run_add, hbody, htail, turn_stepW (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W (fun _ => false) 23 K200W)) (upd15 σ), fr_fr]
  have hM1' : OutLogW (upd15 σ) L1 :=
    outLogW_app (upd15 σ) (outLogW_map_KHpW (upd15 σ) (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W (fun _ => false) 23 K200W))) hM15
  have hM1 : OutLogW σ1 L1 := outLogW_s9 L1 (tau_s9 (upd15 σ)) hM1'
  have hrelW15 : WfMemW rodata [] env0 (upd15 σ) mem0c :=
    wfMemW_upd15 rodata env0 env0 σ mem0c hw
  have hwbase : WfMemW rodata [] (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W (fun _ => false) 23 K200W)) σ1 mem0c :=
    wfMemW_env rodata env0 (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W (fun _ => false) 23 K200W)) σ1 mem0c
      (wfMemW_s9 rodata env0 (upd15 σ) σ1 mem0c hrelW15 (tau_s9 (upd15 σ)))
  have hcount : σ1 2 = 4 * (j : Int) + (s : Int) := by
    show sigmaOf tau (upd15 σ) 2 = 4 * (j : Int) + (s : Int)
    rw [tau_count, hc15]
    omega
  obtain ⟨e2, M2, hloop, hM2⟩ :=
    loopW mem0c orcC (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W (fun _ => false) 23 K200W)) σ1 hwbase s hs hs8 j (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W (fun _ => false) 23 K200W)) σ1 L1 hcount rfl hM1
  have h2f : sIt j σ1 2 = (s : Int) := by
    rw [sIt_2W, hcount]
    omega
  have hge2 : 4 ≤ sIt j σ1 2 := by rw [h2f]; omega
  have hlt2 : sIt j σ1 2 < 8 := by rw [h2f]; omega
  have hwfin : WfMemW rodata [] e2 σ1 mem0c :=
    wfMemW_env rodata (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W (fun _ => false) 23 K200W)) e2 σ1 mem0c hwbase
  obtain ⟨e3, hfin, hM3⟩ :=
    final_runW e2 (sIt j σ1) mem0c orcC σ1 hwfin (sIt_s9 j σ1) M2 hM2 hge2 hlt2
  have sA := run_add prog 4 mem0c orcC ((72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)) + j * TURNLEN) (68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27))
    (fr M (mapState env0 σ entryW))
  have sB := run_add prog 4 mem0c orcC (72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)) (j * TURNLEN)
    (fr M (mapState env0 σ entryW))
  have sC := run_add prog 4 mem0c orcC 72 ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)
    (fr M (mapState env0 σ entryW))
  refine ⟨e3, M2, ?_, hM3⟩
  rw [sA, sB, sC, hentry, hMB, hloop]
  exact hfin

end Hashtree.Proofs.AvxX4LoopWAll
