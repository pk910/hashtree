import Hashtree.Asm.X86RenRegion
import Hashtree.Proofs.AvxX1W

/-!
# avx_x1 at an arbitrary rodata region

`AvxX1W.correctW` proves the fixed-count theorem for `avx_x1` at rodata region 4.  A chain
needs every kernel at its own region; this file lifts the theorem to an arbitrary region `r`
using the region-renaming simulation (`Hashtree.Asm.X86Ren`) and the memory bridge
(`Hashtree.Asm.X86RenRegion`).

The symbolic environment is deliberately not transported: `EnvMem` quantifies over all
symbolic regions, so the lifted theorem takes `EnvMem` on the swapped memory as a hypothesis.
In the wrapper the environment is built from the concrete chain memory, where the same table
genuinely sits at region `r`.
-/

namespace Hashtree.Proofs.AvxX1W

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Region
open Hashtree.Asm.X86Ren
open Hashtree.Spec Hashtree.Kernels.X86.AvxX1
open Hashtree.Proofs.ShaniW

/-! ## Environments -/

/-- `envAbs` only redefines the `.n` location variables; every `.m` key falls through to the
caller's environment, so `EnvMem` is inherited unchanged.  This is why no tree/cut agreement
lemma is needed for `EnvMem` itself. -/
theorem envAbs_envMem (env : Key → W32) (R : State E Lin) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (h : EnvMem env σ m) : EnvMem (envAbs env R) σ m := h

/-! ## Generic transport lemmas -/

theorem list_map_self {β : Type} (f : β → β) (l : List β) (h : ∀ x ∈ l, f x = x) :
    l.map f = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- A renaming that fixes every region occurring in a state's registers and memory log
leaves the state unchanged. -/
theorem state_self (ρ : RegionRenaming) (s : State W32 Int)
    (hg : ∀ v ∈ s.gpr, ρ.val v = v)
    (hm : ∀ p ∈ s.mem, ρ.addr p.1 = p.1 ∧ ρ.cell p.2 = p.2) :
    ρ.state s = s := by
  cases s with
  | mk gpr vr flags mem pc halted tail err assume =>
      simp only [RegionRenaming.state]
      rw [list_map_self ρ.val gpr hg,
        list_map_self (fun p : Addr Int × Cell W32 Int => (ρ.addr p.1, ρ.cell p.2)) mem
          (fun p hp => by obtain ⟨h1, h2⟩ := hm p hp; simp only [h1, h2])]

/-- `InRange` transports forward through a renaming that fixes `rOut` and `rStack`. -/
theorem inRange_state (ρ : RegionRenaming) (hOut : ρ.f rOut = rOut)
    (hStack : ρ.f rStack = rStack) {sp ob : Int} {len : Nat} {s : State W32 Int}
    (h : InRange sp ob len s.mem) : InRange sp ob len (ρ.state s).mem := by
  intro p hp
  simp only [RegionRenaming.state_mem, List.mem_map] at hp
  obtain ⟨q, hq, hpq⟩ := hp
  have ho : p.1.off = q.1.off := by rw [← hpq]; rfl
  rcases h q hq with ⟨hr, h1, h2⟩ | ⟨hr, h1, h2⟩
  · left
    refine ⟨?_, ?_, ?_⟩
    · rw [← hpq]; simp only [RegionRenaming.addr, hr, hOut]
    · rw [ho]; exact h1
    · rw [ho]; exact h2
  · right
    refine ⟨?_, ?_, ?_⟩
    · rw [← hpq]; simp only [RegionRenaming.addr, hr, hStack]
    · rw [ho]; exact h1
    · rw [ho]; exact h2

/-- `OutOk` transports forward through a renaming that fixes `rOut`. -/
theorem outOk_state (ρ : RegionRenaming) (hOut : ρ.f rOut = rOut)
    (inp : Nat → Byte) (ob : Int) (nblk : Nat) (s : State W32 Int)
    (h : OutOk inp ob nblk s.mem) : OutOk inp ob nblk (ρ.state s).mem := by
  intro n i b hn hi hb
  obtain ⟨x, hl, htb⟩ := h n i b hn hi hb
  refine ⟨x, ?_, htb⟩
  let a : Addr Int := ⟨rOut, ob + ((32 * n + 4 * i + b : Nat) : Int)⟩
  have e : ρ.addr a = a := by simp only [a, RegionRenaming.addr, hOut]
  have hlr := RegionRenaming.lookup_ren ρ a s.mem
  rw [hl] at hlr
  simp only [RegionRenaming.cell] at hlr
  simpa only [a, RegionRenaming.state_mem, RegionRenaming.cell, e] using hlr

/-- `RegsOk` transports forward through a renaming that fixes `rStack`, `rG` and `rNum`. -/
theorem regsOk_state (ρ : RegionRenaming) (hStack : ρ.f rStack = rStack)
    (hG : ρ.f rG = rG) (hNum : ρ.f rNum = rNum)
    (env0 : Key → W32) (σ : Nat → Int) (s : State W32 Int) (h : RegsOk env0 σ s) :
    RegsOk env0 σ (ρ.state s) := by
  obtain ⟨h3, h5, h12, h14, h13, h15, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [RegionRenaming.state_gpr, List.getElem?_map, h3, h5, h12, h14, h13, h15, h4,
      Option.map_some, RegionRenaming.val, RegionRenaming.addr, hStack, hG, hNum]

/-! ## The entry state is fixed by the swap -/

/-- Every register of `entryW` is a number or a pointer into a fixed region. -/
theorem val_entryW (ρ : RegionRenaming) (hNum : ρ.f rNum = rNum) (hIn : ρ.f rIn = rIn)
    (hOut : ρ.f rOut = rOut) (hStack : ρ.f rStack = rStack) (hG : ρ.f rG = rG)
    (env : Key → W32) (σ : Nat → Int) :
    ∀ v ∈ entryW.gpr, ρ.val (mapVal env σ v) = mapVal env σ v := by
  intro v hv
  simp only [entryW, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
    i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hNum, hIn, hOut, hStack, hG]

theorem state_entryW (ρ : RegionRenaming) (hNum : ρ.f rNum = rNum) (hIn : ρ.f rIn = rIn)
    (hOut : ρ.f rOut = rOut) (hStack : ρ.f rStack = rStack) (hG : ρ.f rG = rG)
    (env : Key → W32) (σ : Nat → Int) :
    ρ.state (mapState env σ entryW) = mapState env σ entryW := by
  have hg : ∀ v ∈ (mapState env σ entryW).gpr, ρ.val v = v := by
    intro v hv
    simp only [mapState, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact val_entryW ρ hNum hIn hOut hStack hG env σ w hw
  have hm : ∀ p ∈ (mapState env σ entryW).mem, ρ.addr p.1 = p.1 ∧ ρ.cell p.2 = p.2 := by
    intro p hp
    simp only [mapState, entryW, List.map_nil, List.not_mem_nil] at hp
  exact state_self ρ _ hg hm

/-! ## The lifted theorem -/

/-- **avx_x1 at an arbitrary rodata region `r`, every count.**  `AvxX1W.correctW` lifted to
`run prog r`, with the initial state `(swap 4 r).state (mapState ... entryW)` (equal to the
unswapped entry state by `state_entryW`). -/
theorem correctWAt (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r : Region)
    (hrNum : r ≠ rNum) (hrIn : r ≠ rIn) (hrOut : r ≠ rOut) (hrStack : r ≠ rStack)
    (hrG : r ≠ rG) (hrRet : r ≠ rRet)
    (hw : WfMemAtW r rodata [] env0 σ mem0c)
    (he : EnvMem env0 σ ((swap 4 r).mem mem0c))
    (hc : σ 2 = c)
    (hin : ∀ o : Nat, (swap 4 r).mem mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let fin := run prog r mem0c orcC (steps c) ((swap 4 r).state (mapState env0 σ entryW))
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (σ 9) (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem ∧
      RegsOk env0 σ fin := by
  have hOut : (swap 4 r).f rOut = rOut :=
    swap_fixes 4 r rOut (by decide) (Ne.symm hrOut)
  have hIn : (swap 4 r).f rIn = rIn :=
    swap_fixes 4 r rIn (by decide) (Ne.symm hrIn)
  have hStack : (swap 4 r).f rStack = rStack :=
    swap_fixes 4 r rStack (by decide) (Ne.symm hrStack)
  have hG : (swap 4 r).f rG = rG :=
    swap_fixes 4 r rG (by decide) (Ne.symm hrG)
  have hNum : (swap 4 r).f rNum = rNum := swap_rNum 4 r (by decide) hrNum
  have hwf : WfMemW rodata [] env0 σ ((swap 4 r).mem mem0c) :=
    wfMemAtW_swap r hrIn hrStack hrRet rodata [] env0 σ mem0c hw
      (by intro k c hk; simp [plookup] at hk)
  have hpost := correctW c inp env0 σ ((swap 4 r).mem mem0c) orcC hwf he hc hin
  dsimp only at hpost
  have hentry : (swap 4 r).state (mapState env0 σ entryW) = mapState env0 σ entryW :=
    state_entryW (swap 4 r) hNum hIn hOut hStack hG env0 σ
  have hrun : run prog r mem0c orcC (steps c) ((swap 4 r).state (mapState env0 σ entryW)) =
      (swap 4 r).state
        (run prog 4 ((swap 4 r).mem mem0c) orcC (steps c) (mapState env0 σ entryW)) :=
    run_swap_chain r hrNum hrRet prog mem0c orcC (steps c) (mapState env0 σ entryW)
  dsimp only
  rw [hrun]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpost
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [RegionRenaming.state_halted] using h1
  · simpa only [RegionRenaming.state_err] using h2
  · simpa only [RegionRenaming.state_tail] using h3
  · exact inRange_state (swap 4 r) hOut hStack h4
  · exact outOk_state (swap 4 r) hOut inp (σ 1) c _ h5
  · exact regsOk_state (swap 4 r) hStack hG hNum env0 σ _ h6

end Hashtree.Proofs.AvxX1W
