import Hashtree.Asm.ArmShift
import Hashtree.Asm.ArmSym

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The stack shift and the initial memory

`memSh k` shifts the stack region of the initial memory, and `ArmSym.Mem0Rel` constrains only
the non-poison cells of the symbolic memory `mem0s`.  In `mem0s` every non-poison cell is a
`.dat` cell outside `rStack` (input bytes, rodata bytes), so:

* `Mem0Rel_memSh` - the symbolic/concrete memory relation is preserved by `memSh k`
  (provided the rodata region is not `rStack`);
* `memSh_comp` / `memSh_zero` - two shifts compose, and a zero shift is the identity.

Together these let the shifted run be stated against the driver's own initial memory `m0` by
running the base side at `memSh (-sp0) m0`: `memSh sp0 (memSh (-sp0) m0) = m0`, and the base
side's final state is memory independent anyway.
-/

namespace Hashtree.Asm.ArmShift
open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmSym

/-! ## Composing shifts -/

theorem mapAddr_comp (k k' : Int) (a : Addr Int) :
    mapAddr k (mapAddr k' a) = mapAddr (k + k') a := by
  obtain ⟨r, o⟩ := a
  by_cases h : r = rStack
  · subst h
    show (⟨rStack, o + k' + k⟩ : Addr Int) = ⟨rStack, o + (k + k')⟩
    congr 1
    omega
  · rw [mapAddr_of_ne k' _ h, mapAddr_of_ne k _ h, mapAddr_of_ne (k + k') _ h]

theorem mapAddr_zero (a : Addr Int) : mapAddr 0 a = a := by
  obtain ⟨r, o⟩ := a
  by_cases h : r = rStack
  · subst h
    show (⟨rStack, o + 0⟩ : Addr Int) = ⟨rStack, o⟩
    congr 1
    omega
  · rw [mapAddr_of_ne 0 _ h]

theorem shCell_comp (k k' : Int) (c : Cell W32 Int) :
    shCell k (shCell k' c) = shCell (k + k') c := by
  cases c with
  | dat x j => rfl
  | pb a j => simp only [shCell, mapAddr_comp]

theorem shCell_zero (c : Cell W32 Int) : shCell 0 c = c := by
  cases c with
  | dat x j => rfl
  | pb a j => simp only [shCell, mapAddr_zero]

theorem memSh_comp (k k' : Int) (m : Addr Int → Cell W32 Int) :
    memSh k (memSh k' m) = memSh (k + k') m := by
  funext a
  rw [memSh, memSh, memSh, mapAddr_comp, shCell_comp,
    show -k' + -k = -(k + k') by omega]

theorem memSh_zero (m : Addr Int → Cell W32 Int) : memSh 0 m = m := by
  funext a
  simp only [memSh]
  rw [show (-0 : Int) = 0 by omega, mapAddr_zero, shCell_zero]

/-! ## `Mem0Rel` survives a stack shift -/

theorem mem0s_okC_dat {ro : Region} {rodata : List Nat} {a : Addr Lin}
    (ha : Cell.okC (mem0s ro rodata a)) :
    ∃ x j, mem0s ro rodata a = Cell.dat x j := by
  obtain ⟨r, off⟩ := a
  cases hoff : off.asInt with
  | none =>
    by_cases h1 : r = rIn
    · exact ⟨.var (.m r off), 0, by simp [mem0s, h1]⟩
    · simp [mem0s, h1, hoff, poison, Cell.okC] at ha
  | some o =>
    by_cases h1 : r = rIn
    · exact ⟨.var (.m r off), 0, by simp [mem0s, h1]⟩
    · by_cases h2 : r = ro
      · have hri : ro ≠ rIn := fun he => h1 (h2.trans he)
        exact ⟨.const (BitVec.ofNat 32 (rodata.getD o.toNat 0)), 0,
          by simp [mem0s, h1, hoff, h2, hri]⟩
      · simp [mem0s, h1, hoff, h2, poison, Cell.okC] at ha

theorem mem0s_okC_region {ro : Region} {rodata : List Nat} {a : Addr Lin}
    (hro : ro ≠ rStack) (ha : Cell.okC (mem0s ro rodata a)) : a.region ≠ rStack := by
  obtain ⟨r, off⟩ := a
  have hne : r ≠ rStack := by
    cases hoff : off.asInt with
    | none =>
      by_cases h1 : r = rIn
      · subst h1; decide
      · simp [mem0s, h1, hoff, poison, Cell.okC] at ha
    | some o =>
      by_cases h1 : r = rIn
      · subst h1; decide
      · by_cases h2 : r = ro
        · subst h2; exact hro
        · simp [mem0s, h1, hoff, h2, poison, Cell.okC] at ha
  exact hne

theorem Mem0Rel_memSh (ro : Region) (rodata : List Nat) (hro : ro ≠ rStack)
    (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (k : Int)
    (h0 : Mem0Rel env σ (mem0s ro rodata) mem0c) :
    Mem0Rel env σ (mem0s ro rodata) (memSh k mem0c) := by
  intro a ha
  obtain ⟨x, j, hdat⟩ := mem0s_okC_dat (ro := ro) (rodata := rodata) ha
  have hreg := mem0s_okC_region (ro := ro) (rodata := rodata) hro ha
  have h0a := h0 a ha
  simp only [memSh]
  rw [mapAddr_of_ne (-k) (Hashtree.Asm.mapAddr σ a) hreg, h0a, hdat]
  simp [mapCell, shCell]

end Hashtree.Asm.ArmShift
