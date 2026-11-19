import Hashtree.Proofs.WinAvxX4WLoop
import Hashtree.Proofs.WinAvxX4WStrip
import Hashtree.Proofs.WinAvxX4WBodyS
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.AvxX4
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinLogW (OutLogW)
open Hashtree.Proofs.WinAvxX4W
open Hashtree.Proofs.WinAvxX4WStrip
open Hashtree.Proofs.WinAvxX4WLoop

/-!
# The windows avx_x4 kernel at the wrapper call state, every count

The loop (`WinAvxX4WLoop`) instantiated with the kernel-checked cut facts (`WinAvxX4WShift`,
`WinAvxX4WStrip`) and the generated body runs (`WinAvxX4WBody`, `WinAvxX4WBodyS`).
-/

namespace Hashtree.Proofs.WinAvxX4WAll

theorem cutsW : CutsW := by
  have h := tailOk_true
  simp only [tailOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t1, _⟩, _⟩, _⟩, t5⟩, t6⟩, _⟩, _⟩, _⟩, _⟩, t11⟩, _⟩ := h
  obtain ⟨_, _, _, s4, s5, s6, _, s8, s9, s10, _, _, _, _, s15, s16, _, s18, s19, s20, s21, s22⟩ :=
    stripFacts stripOk_true
  exact
    { sliceT := t1, sliceX := t6, KT_shape := s18, KT_assume := t5, KT_logB := s21,
      KT_save := s19, KTE_assume := t11, KTE_logB := s22,
      sliceTs := s4, sliceXs := s5, KTs_shape := s6, KTs_assume := s8, KTs_logB := s9,
      KTs_nopush := s20, KHs_nOnly := s10, KTEs_assume := s15, KTEs_logB := s16 }

def bodyW : BodyW :=
  { Gf := WinAvxX4WBody.G203, GSf := WinAvxX4WBodyS.GS203,
    run := WinAvxX4WBody.body_runW, mem := WinAvxX4WBody.body_memW,
    runS := WinAvxX4WBodyS.bodyS_runW, memS := WinAvxX4WBodyS.bodyS_memW }

/-- **The windows `avx_x4` for `4 ≤ c < 8` at the wrapper call state.**  The exit cut is `KTE`:
the tail call into `hashtree_sha256_avx_x1` with the frame popped, `xmm6..15` restored and the
entry registers restored (`WinAvxX4WShift.exitGprW`), behind a W-mode log. -/
theorem x4w_runW_last_all (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    ∃ e' M', run prog 4 mem0c orcC (16 + (WinAvxX4WBody.BODYLEN + 37))
        (fr M (mapState env0 σ entryWin)) =
        fr M' (mapState e' σ KTE) ∧
      OutLogW σ (KTE.mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M') :=
  x4w_runW_last cutsW bodyW env0 σ mem0c orcC M hw hM hge hlt

/-- **The windows `avx_x4` for `c = 4 (j + 1) + s`, `4 ≤ s < 8`, at the wrapper call state.**
The exit cut is `KTEs` after `j + 1` turns (`sItW (j + 1)` advances the input by `256 (j + 1)`,
the output by `128 (j + 1)` and lowers the count by `4 (j + 1)`), behind a W-mode log. -/
theorem x4w_runW_all (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (j s : Nat) (hs : 4 ≤ s) (hs8 : s < 8) (hc : σ 2 = 4 * ((j : Int) + 1) + (s : Int)) :
    ∃ e' M', run prog 4 mem0c orcC
        (16 + (TURNLEN + (j * TURNLEN + (WinAvxX4WBody.BODYLEN + 37))))
        (fr M (mapState env0 σ entryWin)) =
        fr M' (mapState e' (sItW (j + 1) σ) KTEs) ∧
      OutLogW (sItW (j + 1) σ) (KTEs.mem.map (fun p =>
        (mapAddr (sItW (j + 1) σ) p.1, mapCell e' (sItW (j + 1) σ) p.2)) ++ M') :=
  x4w_runW cutsW bodyW env0 σ mem0c orcC M hw hM j s hs hs8 hc

end Hashtree.Proofs.WinAvxX4WAll
