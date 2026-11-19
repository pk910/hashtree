import Hashtree.Asm.X86SymW

/-!
# Region-parametric memory predicates for the amd64 proofs

The kernel-side predicate `WfMem` already takes the rodata region as a parameter, so the
fixed-count kernel theorems can be stated at an arbitrary region.  The wrapper's call-state
predicate `WfMemW` fixed the rodata region at 4.  `WfMemAtW` is its region-parametric version;
`WfMemW` is the `r = 4` case (`wfMemW_iff_wfMemAtW`), so no existing statement changes.
`mem0RelW_of_wfAt` is the bridge to `Mem0Rel`, the region-parametric analogue of
`mem0RelW_of_wf`.

This is the first piece of the region-lifting plan: a chain has one memory holding each
kernel's rodata in its own region, so each link's fixed-count theorem must be usable at its
own region rather than at region 4.
-/

namespace Hashtree.Asm.X86Region
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW

/-- `WfMemW` with the rodata table at region `ro` instead of region 4. -/
def WfMemAtW (ro : Region) (rodata : List Nat) (push : List (Int × Cell E Lin))
    (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) : Prop :=
  (∀ o, m ⟨ro, o⟩ = .dat (BitVec.ofNat 32 (rodata.getD o.toNat 0)) 0) ∧
  (∀ k : Int, 0 ≤ k → k < 8 → m ⟨rStack, σ 9 + k⟩ = .pb ⟨rRet, 0⟩ k.toNat) ∧
  (∀ o, m ⟨rIn, o⟩ = .dat (cellX (m ⟨rIn, o⟩)) 0) ∧
  (∀ k c, plookup k push = some c → ¬ (0 ≤ k ∧ k < 8) → Cell.okC c →
    m ⟨rStack, σ 9 + k⟩ = mapCell env σ c)

/-- The existing predicate is the region-4 case. -/
theorem wfMemW_iff_wfMemAtW (rodata : List Nat) (push : List (Int × Cell E Lin))
    (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) :
    WfMemAtW 4 rodata push env σ m ↔ WfMemW rodata push env σ m :=
  Iff.rfl

/-- `mem0RelW_of_wf` at an arbitrary rodata region. -/
theorem mem0RelW_of_wfAt (ro : Region) (rodata : List Nat) (push : List (Int × Cell E Lin))
    (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (hw : WfMemAtW ro rodata push env σ m) (he : EnvMem env σ m) :
    Mem0Rel env σ (mem0sW ro rodata push) m := by
  obtain ⟨htab, hret, hin, hpush⟩ := hw
  intro a ha
  obtain ⟨r, off⟩ := a
  by_cases hs : r = rStack
  · subst hs
    simp only [mem0sW, ite_true] at ha ⊢
    cases hk : stackRel off with
    | none => simp only [hk] at ha; simp [poison, Cell.okC] at ha
    | some k =>
      simp only [hk] at ha ⊢
      have hev := stackRel_eval σ off k hk
      by_cases h8 : 0 ≤ k ∧ k < 8
      · simp only [h8, and_self, ite_true, mapCell, mapAddr, hev]
        rw [hret k h8.1 h8.2]; rfl
      · simp only [h8, ite_false] at ha ⊢
        cases hl : plookup k push with
        | none => simp only [hl] at ha; simp [poison, Cell.okC] at ha
        | some c =>
          simp only [hl] at ha ⊢
          simp only [mapAddr, hev]
          exact hpush k c hl h8 ha
  · have e : mem0sW ro rodata push ⟨r, off⟩ = mem0s ro rodata 24 ⟨r, off⟩ := by
      simp only [mem0sW, hs, ite_false]
    rw [e] at ha ⊢
    simp only [mem0s] at ha ⊢
    by_cases hi : r = rIn
    · subst hi
      simp only [ite_true, mapCell, E.eval, mapAddr]
      rw [he]; exact hin _
    · simp only [hi, ite_false] at ha ⊢
      cases hk : off.asInt with
      | none => simp only [hk] at ha; simp [poison, Cell.okC] at ha
      | some o =>
        simp only [hk] at ha ⊢
        have hev : off.eval σ = o := Lin.eval_asInt σ off o hk
        by_cases hro : r = ro
        · cases hro
          simp only [ite_true, mapCell, E.eval, mapAddr, hev]
          exact htab o
        · simp only [hro, ite_false] at ha ⊢
          simp only [hs, ite_false] at ha
          simp [poison, Cell.okC] at ha

end Hashtree.Asm.X86Region
