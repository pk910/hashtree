import Hashtree.Asm.X86Ren
import Hashtree.Asm.X86Region

/-!
# Region renaming and the region-parametric memory predicate

Step 3 of the region-lifting plan: the chain memory holds each kernel's rodata table in its
own region.  `wfMemAtW_swap` moves a `WfMemAtW r` memory to the region-4 `WfMemAtW` form by
applying the `swap 4 r` lift, which is what lets a region-4 fixed-count theorem consume the
chain memory.
-/

namespace Hashtree.Asm.X86Ren
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Region

variable {α : Type} [Lane α]

theorem rIn_zero : rIn = (1 : Region) := rfl
theorem rStack_zero : rStack = (3 : Region) := rfl

/-- A `WfMemAtW` memory at region `r` becomes a `WfMemW` (region-4) memory after the swap.
The last hypothesis says the swap fixes the cells the prologue pushed; it is vacuous for the
empty push list used by the kernels' entry predicates. -/
theorem wfMemAtW_swap (r : Region) (hrIn : r ≠ rIn) (hrStack : r ≠ rStack)
    (hrRet : r ≠ rRet)
    (rodata : List Nat) (push : List (Int × Cell E Lin))
    (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (hw : WfMemAtW r rodata push env σ m)
    (hcell : ∀ k c, plookup k push = some c →
      (swap 4 r).cell (mapCell env σ c) = mapCell env σ c) :
    WfMemAtW 4 rodata push env σ ((swap 4 r).mem m) := by
  obtain ⟨htab, hret, hin, hpush⟩ := hw
  have hs : (swap 4 r).f rStack = rStack :=
    swap_fixes 4 r rStack (by rw [rStack_zero]; decide) (Ne.symm hrStack)
  have hi : (swap 4 r).f rIn = rIn :=
    swap_fixes 4 r rIn (by rw [rIn_zero]; decide) (Ne.symm hrIn)
  have h5 : (swap 4 r).f rRet = rRet :=
    swap_fixes 4 r rRet (by rw [rRet_zero]; decide) (Ne.symm hrRet)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o
    have h := htab o
    have e : (swap 4 r).addr (⟨4, o⟩ : Addr Int) = ⟨r, o⟩ := by
      simp only [RegionRenaming.addr, swap_ro]
    simp only [RegionRenaming.mem]
    rw [e, h]
    rfl
  · intro k h1 h2
    have h := hret k h1 h2
    have e : (swap 4 r).addr (⟨rStack, σ 9 + k⟩ : Addr Int) = ⟨rStack, σ 9 + k⟩ := by
      simp only [RegionRenaming.addr, hs]
    simp only [RegionRenaming.mem]
    rw [e, h]
    simp only [RegionRenaming.cell, RegionRenaming.addr, h5]
  · intro o
    have h := hin o
    have e : (swap 4 r).addr (⟨rIn, o⟩ : Addr Int) = ⟨rIn, o⟩ := by
      simp only [RegionRenaming.addr, hi]
    simp only [RegionRenaming.mem]
    rw [e, h]
    rfl
  · intro k c hl h8 hok
    have h := hpush k c hl h8 hok
    have e : (swap 4 r).addr (⟨rStack, σ 9 + k⟩ : Addr Int) = ⟨rStack, σ 9 + k⟩ := by
      simp only [RegionRenaming.addr, hs]
    simp only [RegionRenaming.mem]
    rw [e, h]
    exact hcell k c hl

end Hashtree.Asm.X86Ren
