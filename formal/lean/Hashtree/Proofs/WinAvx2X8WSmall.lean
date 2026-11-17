import Hashtree.Proofs.WinAvx2X8WLoop
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinLogW
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WLoop (entryWin_nOnly x8P_assume)

/-!
# The windows avx2_x8 small path, `0 < c < 8`, at the wrapper call state

For a count below 8 the kernel runs its prologue (the pushes, the alignment, the frame and the
`r12..r15`/`ymm6..15` saves), takes `jb` at pc 24 to the restores at 6086 and tail-calls
`hashtree_sha256_avx_x4` with the frame popped: 42 instructions from `entryWin`.  The cut `x8Sm r`
(35 instructions from the aligned state `x8A r`) has the wrapper's general registers
(`gpr = entryWin.gpr`), `ymm6..15` reloaded from their saves (the upper `zmm` lanes cleared by
the VEX loads; the low lanes are the saved ones), the conditions `c < 8`, `c ≠ 0`, and a W-mode
log of 368 bytes (the pushes and the saves).  Checked at the two ABI residues `r = 8, 24`.
-/

namespace Hashtree.Proofs.WinAvx2X8WSmall

/-- `jb` at pc 24 taken (count below 8). -/
def orcSm : Nat → Bool := fun pc => decide (pc ∈ ([24] : List Nat))

/-- The small path's cut: 35 instructions from `x8A r`. -/
def x8Sm (r : Nat) : State E Lin := abstract (run prog 4 m8W orcSm 35 (x8A r))

/-- The small path's recorded conditions: `c < 8` (taken) and `c ≠ 0` (taken). -/
def A1Sm : List (Cond Lin × Bool) :=
  [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨8, []⟩ : Lin)), true),
   ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]

theorem asmSm (σ : Nat → Int) (h0 : 0 < σ 2) (h8 : σ 2 < 8) :
    ∀ p ∈ A1Sm, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A1Sm, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega

/-- The small-path facts at one residue, as one boolean. -/
def smOk (r : Nat) : Bool :=
  sliceCheck prog 4 m8W orcSm 35 (x8A r) (x8Sm r) [] &&
  decide ((x8Sm r).tail = some "hashtree_sha256_avx_x4") && decide ((x8Sm r).err = none) &&
  decide ((x8Sm r).halted = true) && decide ((x8Sm r).pc = 6103) &&
  decide ((x8Sm r).gpr = entryWin.gpr) && decide ((x8Sm r).assume = A1Sm) &&
  (x8Sm r).mem.all logOkBW

theorem smOk_8 : smOk 8 = true := by decide +kernel
theorem smOk_24 : smOk 24 = true := by decide +kernel

theorem smFacts (r : Nat) (h : smOk r = true) :
    sliceCheck prog 4 m8W orcSm 35 (x8A r) (x8Sm r) [] = true ∧
    (x8Sm r).tail = some "hashtree_sha256_avx_x4" ∧ (x8Sm r).err = none ∧
    (x8Sm r).halted = true ∧ (x8Sm r).pc = 6103 ∧ (x8Sm r).gpr = entryWin.gpr ∧
    (x8Sm r).assume = A1Sm ∧ (x8Sm r).mem.all logOkBW = true := by
  simp only [smOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem smOk_abi (r : Nat) (hr : r = 8 ∨ r = 24) : smOk r = true := by
  rcases hr with rfl | rfl
  · exact smOk_8
  · exact smOk_24

/-- **The windows avx2_x8 small path.**  For `0 < c < 8` and the ABI residue
`r = (σ 9 - 16) % 32`, 42 instructions from `fr M (mapState env0 σ entryWin)` reach
`fr M (mapState e' σ (x8Sm r))`: halted on the tail call into `hashtree_sha256_avx_x4`, the
wrapper's general registers restored, behind a W-mode log. -/
theorem x8w_small_run (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (h0 : 0 < σ 2) (h8 : σ 2 < 8) (r : Nat) (hr : (r : Int) = (σ 9 - 16) % 32)
    (habi : r = 8 ∨ r = 24) :
    ∃ e', run prog 4 mem0c orcC 42 (fr M (mapState env0 σ entryWin)) =
        fr M (mapState e' σ (x8Sm r)) ∧
      OutLogW σ ((x8Sm r).mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  have hf := smFacts r (smOk_abi r habi)
  let E := ecomb env0 σ (view M mem0c)
  have hw' : WfMemW rodata [] E σ (view M mem0c) := wfW_view rodata env0 E σ mem0c M hM hw
  have hrel : Mem0Rel E σ m8W (view M mem0c) := by
    rw [m8W_eq]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c) hw' (envMem_ecomb E σ (view M mem0c))
  have r6 := (slice_sound E σ m8W (view M mem0c) hrel prog 4 orcNZ orcC 6 entryWin x8P []
    sliceP entryWin_err (assumeOk_of σ x8P A1nz x8P_assume (asmNZ σ h0))).1
  have hrel1 : Mem0Rel (envAbs E (run prog 4 m8W orcNZ 6 entryWin)) σ m8W (view M mem0c) :=
    mem0Rel_envAbs _ _ _ _ m8W_keyed hrel _
  have r1 := run1_align (envAbs E (run prog 4 m8W orcNZ 6 entryWin)) σ (view M mem0c) orcC r hr
  have r35 := (slice_sound _ σ m8W (view M mem0c) hrel1 prog 4 orcSm orcC 35 (x8A r) (x8Sm r) []
    hf.1 (x8A_err r) (assumeOk_of σ (x8Sm r) A1Sm hf.2.2.2.2.2.2.1 (asmSm σ h0 h8))).1
  refine ⟨envAbs (envAbs E (run prog 4 m8W orcNZ 6 entryWin)) (run prog 4 m8W orcSm 35 (x8A r)),
    ?_, outLogW_app σ (outLogW_of_logB (x8Sm r) hf.2.2.2.2.2.2.2 σ _) hM⟩
  rw [run_fr, mapState_nOnly env0 E σ (fun _ => rfl) entryWin entryWin_nOnly]
  refine congrArg (fr M) ?_
  rw [show (42 : Nat) = 6 + (1 + 35) from rfl, run_add, r6, run_add, r1]
  exact r35

end Hashtree.Proofs.WinAvx2X8WSmall
