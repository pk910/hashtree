import Hashtree.Proofs.RegionLift
import Hashtree.Proofs.WinRegionTags
import Hashtree.Proofs.WinShaniBridge
import Hashtree.Proofs.WinShaniSeedAlign

/-!
# R5: the region side condition of the frame-slot lift for the push-saving windows kernels

`entryWin_regRel`: the wrapper's call state satisfies the entry table `entryWinRegs`;
`regionOk_sse` / `regionOk_avx1` / `regionOk_avx2`: along every error-free run of the kernel from
it, every non-halted state has its non-rsp memory bases outside `rStack` (`FrameLift.RegionOk`).
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinRegionLift

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.RegionTags
open Hashtree.Proofs.RegionLift Hashtree.Proofs.WinRegionTags
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinShaniBridge (stW_len entryWin_gpr1 entryWin_gpr2 entryWin_gpr4 entryWin_gpr8
  entryWin_gpr3 entryWin_gpr5 entryWin_gpr12 entryWin_gpr13 entryWin_gpr14 entryWin_gpr15)
open Hashtree.Proofs.WinShaniSeedAlign (mapState_getG)

theorem entryWin_num (i : Nat) (hi : i ∈ [0, 6, 7, 9, 10, 11]) :
    entryWin.gpr[i]? = some (.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem entryWin_regRel (env : Key → W32) (σ : Nat → Int) : RegRel entryWinRegs (mapState env σ entryWin) := by
  intro r ρ hρ
  have h16 : r < 16 := by
    rcases Nat.lt_or_ge r 16 with h | h
    · exact h
    · exfalso
      have : regOf entryWinRegs r = none := by
        simp only [regOf, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp [entryWinRegs]; omega)]; rfl
      rw [this] at hρ; cases hρ
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨
      r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [regOf, entryWinRegs, List.getD_eq_getElem?_getD] at hρ
  all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Option.some.injEq] at hρ
  all_goals subst hρ
  · rw [mapState_getG (entryWin_num 0 (by simp))]; rfl
  · rw [mapState_getG entryWin_gpr1]; rfl
  · rw [mapState_getG entryWin_gpr2]; rfl
  · rw [mapState_getG entryWin_gpr3]; rfl
  · rw [mapState_getG entryWin_gpr4]; rfl
  · rw [mapState_getG entryWin_gpr5]; rfl
  · rw [mapState_getG (entryWin_num 6 (by simp))]; rfl
  · rw [mapState_getG (entryWin_num 7 (by simp))]; rfl
  · rw [mapState_getG entryWin_gpr8]; rfl
  · rw [mapState_getG (entryWin_num 9 (by simp))]; rfl
  · rw [mapState_getG (entryWin_num 10 (by simp))]; rfl
  · rw [mapState_getG (entryWin_num 11 (by simp))]; rfl
  · rw [mapState_getG entryWin_gpr12]; rfl
  · rw [mapState_getG entryWin_gpr13]; rfl
  · rw [mapState_getG entryWin_gpr14]; rfl
  · rw [mapState_getG entryWin_gpr15]; rfl

section Kernels
variable (env : Key → W32) (σ : Nat → Int) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)

theorem rinv_entry (RT : RSegs) (h0 : atR RT 0 = some entryWinRegs) :
    RInv RT (mapState env σ entryWin) :=
  Or.inl ⟨rfl, entryWinRegs, h0, rfl, entryWin_regRel env σ⟩

theorem regionOk_sse (k : Nat) (hok : (run Hashtree.Kernels.X86Win.SseX1.prog 4 mem0 orc k (mapState env σ entryWin)).err = none) :
    ∀ j, j ≤ k → (run Hashtree.Kernels.X86Win.SseX1.prog 4 mem0 orc j (mapState env σ entryWin)).halted = false →
      Hashtree.Proofs.FrameLift.RegionOk Hashtree.Kernels.X86Win.SseX1.prog
        (run Hashtree.Kernels.X86Win.SseX1.prog 4 mem0 orc j (mapState env σ entryWin)) :=
  regionOk_run (by decide +kernel) sse_regCert (rinv_entry env σ regsSse (by decide +kernel)) (stW_len env σ) k hok

theorem regionOk_avx1 (k : Nat) (hok : (run Hashtree.Kernels.X86Win.AvxX1.prog 4 mem0 orc k (mapState env σ entryWin)).err = none) :
    ∀ j, j ≤ k → (run Hashtree.Kernels.X86Win.AvxX1.prog 4 mem0 orc j (mapState env σ entryWin)).halted = false →
      Hashtree.Proofs.FrameLift.RegionOk Hashtree.Kernels.X86Win.AvxX1.prog
        (run Hashtree.Kernels.X86Win.AvxX1.prog 4 mem0 orc j (mapState env σ entryWin)) :=
  regionOk_run (by decide +kernel) avx1_regCert (rinv_entry env σ regsAvx1 (by decide +kernel)) (stW_len env σ) k hok

theorem regionOk_avx2 (k : Nat) (hok : (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0 orc k (mapState env σ entryWin)).err = none) :
    ∀ j, j ≤ k → (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0 orc j (mapState env σ entryWin)).halted = false →
      Hashtree.Proofs.FrameLift.RegionOk Hashtree.Kernels.X86Win.Avx2X8.prog
        (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0 orc j (mapState env σ entryWin)) :=
  regionOk_run (by decide +kernel) avx2_regCert (rinv_entry env σ regsAvx2 (by decide +kernel)) (stW_len env σ) k hok

end Kernels

end Hashtree.Proofs.WinRegionLift
