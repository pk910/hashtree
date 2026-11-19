import Hashtree.Proofs.WinAvx2X8WLoop
import Hashtree.Proofs.WinAvx2X8WShift8
import Hashtree.Proofs.WinAvx2X8WShift24
import Hashtree.Proofs.WinAvx2X8WStrip8
import Hashtree.Proofs.WinAvx2X8WStrip24
import Hashtree.Proofs.WinAvx2X8WBodyR8
import Hashtree.Proofs.WinAvx2X8WBodyR8S
import Hashtree.Proofs.WinAvx2X8WBodyR24
import Hashtree.Proofs.WinAvx2X8WBodyR24S
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinLogW (OutLogW)
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip
open Hashtree.Proofs.WinAvx2X8WLoop

/-!
# The windows avx2_x8 kernel at the wrapper call state, every count `c ≥ 8`, at the two ABI
residues

The residue-generic loop (`WinAvx2X8WLoop`) instantiated with the kernel-checked cut facts
(`WinAvx2X8WShift{8,24}`, `WinAvx2X8WStrip{8,24}`, the push-list shape below) and the generated
body runs (`WinAvx2X8WBodyR{r}`, `WinAvx2X8WBodyR{r}S`) at the residues `r = 8` and `r = 24`,
the two the wrapper ABI allows (`WinAvx2X8WShift.residue_abi`), and the all-count theorems with
the residue selected by `σ 9`.
-/

namespace Hashtree.Proofs.WinAvx2X8WAll

theorem push_shape_8 : (pushC 8).all shapeOk = true := by decide +kernel
theorem push_shape_24 : (pushC 24).all shapeOk = true := by decide +kernel
theorem push_bounds_8 : (pushC 8).all (fun p => decide (-368 - ((8 : Nat) : Int) ≤ p.1 ∧ p.1 < 0)) = true := by
  decide +kernel
theorem push_bounds_24 : (pushC 24).all (fun p => decide (-368 - ((24 : Nat) : Int) ≤ p.1 ∧ p.1 < 0)) = true := by
  decide +kernel

/-! ## Residue 8 -/

theorem cutsW_8 : CutsW 8 := by
  obtain ⟨s1, s2, s3, s4, _, _, _, _, _, _, _, _, _, _⟩ := shiftFacts 8 shiftOk_8
  obtain ⟨_, _, _, _, h5, h6, h7, h8, h9, h10, h11, _, _, _, _, h16, h17, _, h19, h20, h21⟩ :=
    stripFacts 8 stripOk_8
  obtain ⟨_, _, _, _, _, t6, _, _, _, _, x11, _, t13, x14⟩ := shiftFacts 8 shiftOk_8
  exact
    { sliceE := s1, sliceE2 := s2, sliceT := s3, sliceX := s4, KT_shape := h19,
      KT_assume := t6, KT_logB := t13, KT_save := h20,
      KTE_assume := x11, KTE_logB := x14,
      sliceTs := h5, sliceXs := h6, KTs_shape := h7, KTs_assume := h9, KTs_logB := h10,
      KTs_nopush := h21, KHs_nOnly := h11, KTEs_assume := h16, KTEs_logB := h17,
      m8P_keyed := m8P_keyed_8, push_shape := push_shape_8, push_bounds := push_bounds_8 }

def bodyW_8 : BodyW 8 :=
  { Gf := WinAvx2X8WBodyR8.G211, GSf := WinAvx2X8WBodyR8S.GS211,
    run := WinAvx2X8WBodyR8.body_runW, mem := WinAvx2X8WBodyR8.body_memW,
    runS := WinAvx2X8WBodyR8S.bodyS_runW, memS := WinAvx2X8WBodyR8S.bodyS_memW }

/-! ## Residue 24 -/

theorem cutsW_24 : CutsW 24 := by
  obtain ⟨s1, s2, s3, s4, _, _, _, _, _, _, _, _, _, _⟩ := shiftFacts 24 shiftOk_24
  obtain ⟨_, _, _, _, h5, h6, h7, h8, h9, h10, h11, _, _, _, _, h16, h17, _, h19, h20, h21⟩ :=
    stripFacts 24 stripOk_24
  obtain ⟨_, _, _, _, _, t6, _, _, _, _, x11, _, t13, x14⟩ := shiftFacts 24 shiftOk_24
  exact
    { sliceE := s1, sliceE2 := s2, sliceT := s3, sliceX := s4, KT_shape := h19,
      KT_assume := t6, KT_logB := t13, KT_save := h20,
      KTE_assume := x11, KTE_logB := x14,
      sliceTs := h5, sliceXs := h6, KTs_shape := h7, KTs_assume := h9, KTs_logB := h10,
      KTs_nopush := h21, KHs_nOnly := h11, KTEs_assume := h16, KTEs_logB := h17,
      m8P_keyed := m8P_keyed_24, push_shape := push_shape_24, push_bounds := push_bounds_24 }

def bodyW_24 : BodyW 24 :=
  { Gf := WinAvx2X8WBodyR24.G211, GSf := WinAvx2X8WBodyR24S.GS211,
    run := WinAvx2X8WBodyR24.body_runW, mem := WinAvx2X8WBodyR24.body_memW,
    runS := WinAvx2X8WBodyR24S.bodyS_runW, memS := WinAvx2X8WBodyR24S.bodyS_memW }

/-! ## Every count, residue selected by the stack pointer -/

/-- The residue of the wrapper call: with `σ 9 ≡ 8 (mod 16)` it is `8` or `24`. -/
theorem residue_cases (σ : Nat → Int) (h : σ 9 % 16 = 8) :
    ((8 : Nat) : Int) = (σ 9 - 16) % 32 ∨ ((24 : Nat) : Int) = (σ 9 - 16) % 32 := by
  omega

/-- **The windows `avx2_x8` for `8 ≤ c < 16` at the wrapper call state.**  The exit cut is
`KTE r` for the residue `r` of `σ 9`: the tail call into `hashtree_sha256_avx_x4` with the frame
popped and the wrapper registers restored (`WinAvx2X8WShift.exitGprW`). -/
theorem x8w_runW_last_abi (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32), (r = 8 ∨ r = 24) ∧
      run prog 4 mem0c orcC (24 + (BODYLEN + 42)) (fr M (mapState env0 σ entryWin)) =
        fr M (mapState e' σ (KTE r)) ∧
      OutLogW σ ((KTE r).mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  rcases residue_cases σ habi with h8 | h24
  · obtain ⟨e', hrun, hlog⟩ :=
      x8w_runW_last cutsW_8 bodyW_8 env0 σ mem0c orcC M hw hM hge hlt h8
    exact ⟨8, e', Or.inl rfl, hrun, hlog⟩
  · obtain ⟨e', hrun, hlog⟩ :=
      x8w_runW_last cutsW_24 bodyW_24 env0 σ mem0c orcC M hw hM hge hlt h24
    exact ⟨24, e', Or.inr rfl, hrun, hlog⟩

/-- **The windows `avx2_x8` for `c = 8 (j + 1) + s`, `8 ≤ s < 16`, at the wrapper call state.**
The exit cut is `KTEs r` after `j + 1` turns: the tail call into `hashtree_sha256_avx_x4` with
the residual `s` blocks (`sIt8 (j + 1)` advances the input by `512 (j + 1)`, the output by
`256 (j + 1)` and lowers the count by `8 (j + 1)`), behind a W-mode log. -/
theorem x8w_runW_abi (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (j s : Nat) (hs : 8 ≤ s) (hs16 : s < 16) (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int))
    (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 8 ∨ r = 24) ∧
      run prog 4 mem0c orcC (24 + (TURNLEN + (j * TURNLEN + (BODYLEN + 42))))
          (fr M (mapState env0 σ entryWin)) =
        fr M' (mapState e' (sIt8 (j + 1) σ) (KTEs r)) ∧
      OutLogW (sIt8 (j + 1) σ) ((KTEs r).mem.map (fun p =>
        (mapAddr (sIt8 (j + 1) σ) p.1, mapCell e' (sIt8 (j + 1) σ) p.2)) ++ M') := by
  rcases residue_cases σ habi with h8 | h24
  · obtain ⟨e', M', hrun, hlog⟩ :=
      x8w_runW cutsW_8 bodyW_8 env0 σ mem0c orcC M hw hM j s hs hs16 hc h8
    exact ⟨8, e', M', Or.inl rfl, hrun, hlog⟩
  · obtain ⟨e', M', hrun, hlog⟩ :=
      x8w_runW cutsW_24 bodyW_24 env0 σ mem0c orcC M hw hM j s hs hs16 hc h24
    exact ⟨24, e', M', Or.inr rfl, hrun, hlog⟩

end Hashtree.Proofs.WinAvx2X8WAll
