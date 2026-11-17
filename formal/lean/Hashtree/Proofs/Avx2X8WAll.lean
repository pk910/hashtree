import Hashtree.Proofs.Avx2X8WLoop
import Hashtree.Proofs.Avx2X8WStrip
import Hashtree.Proofs.Avx2X8WBodyR0
import Hashtree.Proofs.Avx2X8WBodyR0S
import Hashtree.Proofs.Avx2X8WBodyR16
import Hashtree.Proofs.Avx2X8WBodyR16S
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.Avx2X8
open Hashtree.Proofs.AvxX4W (upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW)
open Hashtree.Proofs.Avx2X8Align
open Hashtree.Proofs.Avx2X8WShift
open Hashtree.Proofs.Avx2X8WStrip
open Hashtree.Proofs.Avx2X8WLoop

/-!
# The avx2_x8 kernel at the wrapper call state, every count, at the two ABI residues

The residue-generic loop (`Avx2X8WLoop`) instantiated with the kernel-checked cut facts
(`Avx2X8WShift`, `Avx2X8WStrip`) and the generated body runs (`Avx2X8WBodyR{r}`,
`Avx2X8WBodyR{r}S`) at the residues `r = 0` and `r = 16`, the two the wrapper ABI allows
(`Avx2X8Align.residue_abi`), and the all-count theorems with the residue selected by `σ 9`.
-/

namespace Hashtree.Proofs.Avx2X8WAll

/-! ## Residue 0 -/

theorem cutsW_0 : CutsW 0 := by
  obtain ⟨_, _, _, h4, h5, h6, _, h8, h9, h10, _, _, _, _, h15, h16, _, h18, h19, h20⟩ :=
    stripFacts 0 stripOk_0
  exact
    { sliceE := sliceE_0, sliceT := sliceT_0, sliceX := sliceX_0, KT_shape := h18,
      KT_assume := KT_assume_0, KT_logB := KT_logB_0, KT_push := h19,
      KTE_assume := KTE_assume_0, KTE_logB := KTE_logB_0,
      sliceTs := h4, sliceXs := h5, KTs_shape := h6, KTs_assume := h8, KTs_logB := h9,
      KTs_nopush := h20, KHs_nOnly := h10, KTEs_assume := h15, KTEs_logB := h16,
      m8P_keyed := m8P_keyed_0 }

def bodyW_0 : BodyW 0 :=
  { Gf := Avx2X8WBodyR0.G210, GSf := Avx2X8WBodyR0S.GS210,
    run := Avx2X8WBodyR0.body_runW, mem := Avx2X8WBodyR0.body_memW,
    runS := Avx2X8WBodyR0S.bodyS_runW, memS := Avx2X8WBodyR0S.bodyS_memW }

/-! ## Residue 16 -/

theorem cutsW_16 : CutsW 16 := by
  obtain ⟨_, _, _, h4, h5, h6, _, h8, h9, h10, _, _, _, _, h15, h16, _, h18, h19, h20⟩ :=
    stripFacts 16 stripOk_16
  exact
    { sliceE := sliceE_16, sliceT := sliceT_16, sliceX := sliceX_16, KT_shape := h18,
      KT_assume := KT_assume_16, KT_logB := KT_logB_16, KT_push := h19,
      KTE_assume := KTE_assume_16, KTE_logB := KTE_logB_16,
      sliceTs := h4, sliceXs := h5, KTs_shape := h6, KTs_assume := h8, KTs_logB := h9,
      KTs_nopush := h20, KHs_nOnly := h10, KTEs_assume := h15, KTEs_logB := h16,
      m8P_keyed := m8P_keyed_16 }

def bodyW_16 : BodyW 16 :=
  { Gf := Avx2X8WBodyR16.G210, GSf := Avx2X8WBodyR16S.GS210,
    run := Avx2X8WBodyR16.body_runW, mem := Avx2X8WBodyR16.body_memW,
    runS := Avx2X8WBodyR16S.bodyS_runW, memS := Avx2X8WBodyR16S.bodyS_memW }

/-! ## Every count, residue selected by the stack pointer -/

/-- The residue of the wrapper call: with `σ 9 ≡ 8 (mod 16)` it is `0` or `16`. -/
theorem residue_cases (σ : Nat → Int) (h : σ 9 % 16 = 8) :
    ((0 : Nat) : Int) = (σ 9 - 8) % 32 ∨ ((16 : Nat) : Int) = (σ 9 - 8) % 32 := by
  rcases residue_abi σ h with h0 | h16
  · left; rw [h0]; rfl
  · right; rw [h16]; rfl

/-- **`avx2_x8` for `8 ≤ c < 16` at the wrapper call state.**  The exit cut is `KTE r` for the
residue `r` of `σ 9`: the tail call into `hashtree_sha256_avx_x4` with the frame popped and
the entry registers restored (`Avx2X8WShift.exitGpr`). -/
theorem x8_runW_last_abi (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run prog 4 mem0c orcC (16 + (BODYLEN + 31)) (fr M (mapState env0 σ entryW)) =
        fr M' (mapState e' (upd15 σ) (KTE r)) ∧
      OutLogW (upd15 σ) ((KTE r).mem.map (fun p =>
        (mapAddr (upd15 σ) p.1, mapCell e' (upd15 σ) p.2)) ++ M') := by
  rcases residue_cases σ habi with h0 | h16
  · obtain ⟨e', M', hrun, hlog⟩ :=
      x8_runW_last cutsW_0 bodyW_0 env0 σ mem0c orcC M hw hM hge hlt h0
    exact ⟨0, e', M', Or.inl rfl, hrun, hlog⟩
  · obtain ⟨e', M', hrun, hlog⟩ :=
      x8_runW_last cutsW_16 bodyW_16 env0 σ mem0c orcC M hw hM hge hlt h16
    exact ⟨16, e', M', Or.inr rfl, hrun, hlog⟩

/-- **`avx2_x8` for `c = 8 (j + 1) + s`, `8 ≤ s < 16`, at the wrapper call state.**  The exit
cut is `KTEs r` after `j + 1` turns: the tail call into `hashtree_sha256_avx_x4` with the
residual `s` blocks (`sIt8 (j + 1)` advances the input by `512 (j + 1)`, the output by
`256 (j + 1)` and lowers the count by `8 (j + 1)`), behind a W-mode log. -/
theorem x8_runW_abi (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (j s : Nat) (hs : 8 ≤ s) (hs16 : s < 16) (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int))
    (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run prog 4 mem0c orcC (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31))))
          (fr M (mapState env0 σ entryW)) =
        fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r)) ∧
      OutLogW (sIt8 (j + 1) (upd15 σ)) ((KTEs r).mem.map (fun p =>
        (mapAddr (sIt8 (j + 1) (upd15 σ)) p.1, mapCell e' (sIt8 (j + 1) (upd15 σ)) p.2)) ++ M') := by
  rcases residue_cases σ habi with h0 | h16
  · obtain ⟨e', M', hrun, hlog⟩ :=
      x8_runW cutsW_0 bodyW_0 env0 σ mem0c orcC M hw hM j s hs hs16 hc h0
    exact ⟨0, e', M', Or.inl rfl, hrun, hlog⟩
  · obtain ⟨e', M', hrun, hlog⟩ :=
      x8_runW cutsW_16 bodyW_16 env0 σ mem0c orcC M hw hM j s hs hs16 hc h16
    exact ⟨16, e', M', Or.inr rfl, hrun, hlog⟩

end Hashtree.Proofs.Avx2X8WAll
