import Hashtree.Proofs.AvxX4LoopWOut

/-!
# R2c — the one-pass linux avx_x4 W-mode exit output (`TurnOut4Last`)

R2's statement `Avx2X8OutLink.TurnOut4Last` (research/formal-r2-amd64 2da19f1), its text copied
verbatim with `x4LastSteps` (`Avx2X8X4WAgree`'s literal) and `OutOk` this project's
(`Avx512X16WOut.OutOk`, the text of `ShaniW.OutOk`).  The run is `AvxX4LoopWAll.x4_runW_last`'s:
entry (72) + body + exit tail (27, `orcExitW`) into `K201W`; the invariant is the lifted pilot chain
`stepW4_entry` / `invW4_body` / `stepW4_exit` and the digests `outOk_K201W`, as in `turnOut4`.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.AvxX4 Hashtree.Gen.AvxX4P
open Hashtree.Proofs.AvxX4W Hashtree.Proofs.AvxX4Loop Hashtree.Proofs.AvxX4LoopTurn
open Hashtree.Proofs.AvxX4LoopW Hashtree.Proofs.AvxX4LoopFrame Hashtree.Proofs.AvxX4LoopWFrame
open Hashtree.Proofs.AvxX4LoopWExit Hashtree.Proofs.AvxX4LoopWAll
open Hashtree.Proofs.AvxX4LoopWOut
open Hashtree.Proofs.Avx512X16WOut (OutOk outOk_append_left)

namespace Hashtree.Proofs.AvxX4LoopWOutLast

/-- `Avx2X8X4WAgree.x4LastSteps` (R2's literal). -/
def x4LastSteps : Nat := 72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)

/-- **`TurnOut4Last`** (R2's `Avx2X8OutLink.TurnOut4Last`, verbatim). -/
def TurnOut4Last : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c →
    Hashtree.Proofs.AvxX4LoopWFrame.OutLogW σ M → 4 ≤ σ 2 → σ 2 < 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC
        x4LastSteps (fr M (mapState env0 σ entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 128) ∨
        (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 4
      (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC
        x4LastSteps (fr M (mapState env0 σ entryW))).mem

theorem turnOut4Last : TurnOut4Last := by
  intro env0 σ mem0c orcC M inp hw hM hge hlt hin
  have hM15 : OutLogW (upd15 σ) M := outLogW_s9 M (upd15_9 σ) hM
  have hge15 : 4 ≤ upd15 σ 2 := by rw [upd15_2]; exact hge
  have hlt15 : upd15 σ 2 < 8 := by rw [upd15_2]; exact hlt
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
  have hall : run prog 4 mem0c orcC x4LastSteps (fr M (mapState env0 σ entryW)) =
      fr M (mapState (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W orcExitW 27 K200W)) (upd15 σ) K201W) := by
    unfold x4LastSteps
    rw [sA, sB, hentry, sC, hbody, sD, hexit]
  -- the invariant at `L201` and the digests
  have hmE1 : HMem 256 inp (envM env0 (view M mem0c) (upd15 σ)) := hmem_envM env0 σ M mem0c inp hM hin
  have hI : InvC inp (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W orcExitW 27 K200W)) L201 :=
    stepW4_exit inp _ (invW4_body inp _ (stepW4_entry inp _ hmE1) hmE1) hmE1
  have hsh := outShape4_sound K201W K201W_outShape4 (envAbs (G200W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (run prog 4 m0W orcExitW 27 K200W)) (upd15 σ)
  have hout := outOk_K201W inp _ (upd15 σ) hI
  rw [upd15_1] at hout
  rw [hall]
  show (∀ p ∈ (mapState _ (upd15 σ) K201W).mem ++ M, _) ∧ OutOk inp (σ 1) 4 ((mapState _ (upd15 σ) K201W).mem ++ M)
  refine ⟨?_, outOk_append_left inp (σ 1) 4 _ M hout⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · rcases hsh p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [upd15_1] at h2 h3
      exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
    · rw [upd15_9] at h2 h3
      exact Or.inr (Or.inr ⟨h1, h2, h3⟩)
  · exact Or.inl h

end Hashtree.Proofs.AvxX4LoopWOutLast
