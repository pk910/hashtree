import Hashtree.Proofs.WinLinkLift
import Hashtree.Asm.X86Region

/-!
# R5: the chain's hand-over and return conditions under a region swap

A chain link whose rodata lives in its own region `r` runs, by `X86Ren.run_swap_chain`, as the
region-4 run renamed by `swap 4 r`.  The wrapper's regions (number, input, output, stack, the
G region, the return marker) are fixed by such a swap, so the conditions the chain passes
between links — `PreLink` (hand-over on a register set behind a log) and `PostLink` (return) —
are invariant under it: the call state `entryWin` is fixed, `Agree` is preserved by renaming
both sides, and the log facts (`OutLogW`, `Foot`, `OutOk`) read only output and stack addresses
and data cells, which the renaming keeps (`lookup_ren`).  `swap_mem_wf`: a table at region `r`
is a table at region 4 of the swapped memory.  These carry each link's region-4 theorem to its
own region (`WinChainRegions`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinLinkSwap

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.RunAgree
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Proofs.X86Chain (resume)
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.ShaniW (OutLogW)
open Hashtree.Proofs.WinAvx512Bridge (shift PostLink PreLink)

/-- A renaming that fixes the wrapper's regions. -/
structure Fix (ρ : RegionRenaming) : Prop where
  num : ρ.f rNum = rNum
  inn : ρ.f rIn = rIn
  out : ρ.f rOut = rOut
  stk : ρ.f rStack = rStack
  g : ρ.f rG = rG
  ret : ρ.f rRet = rRet

theorem fix_swap (r : Region) (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4)
    (h5 : r ≠ 5) (h6 : r ≠ 6) : Fix (swap 4 r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [swap, swapF, rNum, rIn, rOut, rStack, rG, rRet, Ne.symm h0, Ne.symm h1, Ne.symm h2,
      Ne.symm h3, Ne.symm h5, Ne.symm h6]

variable {ρ : RegionRenaming}

/-! ## The call state is fixed -/

/-- Every general register of the call state is a number or a pointer into a wrapper region. -/
def wrapRegs : List Region := [rNum, rIn, rOut, rStack, rG]

theorem entryWin_regions : entryWin.gpr.all (fun v => match v with
    | .ptr a => decide (a.region ∈ wrapRegs) | .num _ _ => true) = true := by decide +kernel

theorem fix_region (hF : Fix ρ) (x : Region) (hx : x ∈ wrapRegs) : ρ.f x = x := by
  simp only [wrapRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hF.num
  · exact hF.inn
  · exact hF.out
  · exact hF.stk
  · exact hF.g

theorem entryWin_mem : entryWin.mem = [] := rfl

theorem state_entryWin (hF : Fix ρ) (env : Key → W32) (τ : Nat → Int) :
    ρ.state (mapState env τ entryWin) = mapState env τ entryWin := by
  have hg : (entryWin.gpr.map (mapVal env τ)).map ρ.val = entryWin.gpr.map (mapVal env τ) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro v hv
    have h := List.all_eq_true.mp entryWin_regions v hv
    cases v with
    | num lo hi => rfl
    | ptr a =>
      simp only [decide_eq_true_eq] at h
      simp only [Function.comp, mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr,
        fix_region hF _ h]
  have hg' : (mapState env τ entryWin).gpr.map ρ.val = (mapState env τ entryWin).gpr := hg
  have hm : (mapState env τ entryWin).mem = [] := rfl
  show ({ mapState env τ entryWin with
      gpr := (mapState env τ entryWin).gpr.map ρ.val
      mem := (mapState env τ entryWin).mem.map
        (fun p : Addr Int × Cell W32 Int => (ρ.addr p.1, ρ.cell p.2)) } : CState) = _
  rw [hg', hm]
  rfl

/-! ## Agreement, logs -/

theorem agree_ren {R : List Nat} {fl : Bool} {s1 s2 : CState} (h : Agree R fl s1 s2) :
    Agree R fl (ρ.state s1) (ρ.state s2) where
  gpr := fun r hr => by rw [RegionRenaming.getG_ren, RegionRenaming.getG_ren, h.gpr r hr]
  len := by simp [h.len]
  vr := h.vr
  flags := h.flags
  mem := by simp [h.mem]
  pc := h.pc
  halted := h.halted
  tail := h.tail
  err := h.err

def renLog (ρ : RegionRenaming) (M : CLog) : CLog := M.map fun p => (ρ.addr p.1, ρ.cell p.2)

theorem state_fr (M : CLog) (s : CState) : ρ.state (fr M s) = fr (renLog ρ M) (ρ.state s) := by
  simp only [RegionRenaming.state, fr, renLog, List.map_append]

theorem state_vr_upd (s : CState) (V : List (List W32)) :
    ρ.state { s with vr := V } = { ρ.state s with vr := V } := rfl

theorem mem_renLog (M : CLog) (p : Addr Int × Cell W32 Int) (hp : p ∈ renLog ρ M) :
    ∃ q ∈ M, p.1.region = ρ.f q.1.region ∧ p.1.off = q.1.off := by
  simp only [renLog, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨q, hq, rfl, rfl⟩

theorem outLogW_ren (hF : Fix ρ) (sp : Int) (M : CLog) (h : OutLogW sp M) : OutLogW sp (renLog ρ M) := by
  intro p hp
  obtain ⟨q, hq, hr, ho⟩ := mem_renLog M p hp
  rcases h q hq with h1 | ⟨h1, h2⟩
  · left; rw [hr, h1, hF.out]
  · right; rw [hr, h1, hF.stk, ho]; exact ⟨rfl, h2⟩

theorem foot_ren (hF : Fix ρ) (sp : Int) (D : Nat) (ob : Int) (len : Nat) (M : CLog)
    (h : Foot sp D ob len M) : Foot sp D ob len (renLog ρ M) := by
  intro p hp
  obtain ⟨q, hq, hr, ho⟩ := mem_renLog M p hp
  rcases h q hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [hr, h1, hF.out, ho]; exact ⟨rfl, h2⟩
  · right; rw [hr, h1, hF.stk, ho]; exact ⟨rfl, h2⟩

theorem outOk_ren (hF : Fix ρ) (inp : Nat → Byte) (ob : Int) (n : Nat) (M : CLog)
    (h : OutOk inp ob n M) : OutOk inp ob n (renLog ρ M) := by
  intro k i b hk hi hb
  obtain ⟨x, hx, hv⟩ := h k i b hk hi hb
  refine ⟨x, ?_, hv⟩
  have ha : (⟨rOut, ob + ((32 * k + 4 * i + b : Nat) : Int)⟩ : Addr Int) =
      ρ.addr ⟨rOut, ob + ((32 * k + 4 * i + b : Nat) : Int)⟩ := by
    simp only [RegionRenaming.addr, hF.out]
  rw [ha, renLog, RegionRenaming.lookup_ren, hx]
  rfl

theorem getElem?_ren (s : CState) (j : Nat) : (ρ.state s).gpr[j]? = (s.gpr[j]?).map ρ.val := by
  simp only [RegionRenaming.state_gpr, List.getElem?_map]

theorem regsOkW_ren (hF : Fix ρ) (σ : Nat → Int) (s : CState) (h : RegsOkW σ s) : RegsOkW σ (ρ.state s) := by
  obtain ⟨g3, g5, g12, g13, g14, g15, g4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [getElem?_ren, g3]; simp [RegionRenaming.val, RegionRenaming.addr, hF.stk]
  · rw [getElem?_ren, g5]; simp [RegionRenaming.val, RegionRenaming.addr, hF.stk]
  · rw [getElem?_ren, g12]; simp [RegionRenaming.val, RegionRenaming.addr, hF.num]
  · rw [getElem?_ren, g13]; simp [RegionRenaming.val, RegionRenaming.addr, hF.num]
  · rw [getElem?_ren, g14]; simp [RegionRenaming.val, RegionRenaming.addr, hF.g]
  · rw [getElem?_ren, g15]; simp [RegionRenaming.val, RegionRenaming.addr, hF.num]
  · rw [getElem?_ren, g4]; simp [RegionRenaming.val, RegionRenaming.addr, hF.stk]

/-! ## The chain conditions are invariant -/

theorem postLink_ren (hF : Fix ρ) (σ : Nat → Int) (c : Nat) (inp : Nat → Byte) (D : Nat) (f : CState)
    (h : PostLink σ c inp D f) : PostLink σ c inp D (ρ.state f) := by
  obtain ⟨hh, hfoot, hok, hreg⟩ := h
  refine ⟨hh, ?_, ?_, regsOkW_ren hF σ f hreg⟩
  · show Foot (σ 9) D (σ 1) (32 * c) (f.mem.map fun p => (ρ.addr p.1, ρ.cell p.2))
    exact foot_ren hF _ D _ _ f.mem hfoot
  · show OutOk inp (σ 1) c (f.mem.map fun p => (ρ.addr p.1, ρ.cell p.2))
    exact outOk_ren hF inp _ c f.mem hok

theorem preLink_ren (hF : Fix ρ) (env : Key → W32) (σ : Nat → Int) (c d r : Nat) (inp : Nat → Byte)
    (D : Nat) (L : List Nat) (s : CState) (h : PreLink env σ c d r inp D L s) :
    PreLink env σ c d r inp D L (ρ.state s) := by
  obtain ⟨V, M', hV, hA, hlog, hfoot, hok⟩ := h
  refine ⟨V, renLog ρ M', hV, ?_, outLogW_ren hF _ M' hlog, foot_ren hF _ D _ _ M' hfoot,
    outOk_ren hF inp _ d M' hok⟩
  have h2 := agree_ren (ρ := ρ) hA
  have e : ρ.state (fr M' { mapState env (shift σ d r) entryWin with vr := V }) =
      fr (renLog ρ M') { mapState env (shift σ d r) entryWin with vr := V } := by
    rw [state_fr]
    congr 1
    rw [state_vr_upd, state_entryWin hF]
  rw [e] at h2
  exact h2

theorem resume_ren (f : CState) : resume (ρ.state f) = ρ.state (resume f) := rfl

/-! ## Memory -/

/-- The run at region `r` is the renamed region-4 run on the swapped memory. -/
theorem run_at (r : Region) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet) (p : Array Instr)
    (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (n : Nat) (s : CState) :
    run p r m0 orc n s = (swap 4 r).state (run p 4 ((swap 4 r).mem m0) orc n ((swap 4 r).state s)) := by
  have h := run_swap_chain (α := W32) r hrNum hrRet p m0 orc n ((swap 4 r).state s)
  rwa [RegionRenaming.state_invol] at h

theorem swap_mem_at (r : Region) (m0 : Addr Int → Cell W32 Int) (a : Addr Int) :
    (swap 4 r).mem m0 a = (swap 4 r).cell (m0 ((swap 4 r).addr a)) := rfl

/-- A table at region `r` is a table at region 4 of the swapped memory. -/
theorem swap_mem_wf (r : Region) (hF : Fix (swap 4 r)) (rodata : List Nat) (env : Key → W32)
    (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (hw : WfMemAtW r rodata [] env σ m0) :
    WfMemW rodata [] env σ ((swap 4 r).mem m0) := by
  obtain ⟨h1, h2, h3, _⟩ := hw
  refine ⟨fun o => ?_, fun k a b => ?_, fun o => ?_, fun k c h _ _ => by simp [plookup] at h⟩
  · rw [swap_mem_at]
    have : (swap 4 r).addr (⟨4, o⟩ : Addr Int) = ⟨r, o⟩ := by
      simp [RegionRenaming.addr]
    rw [this, h1 o]; rfl
  · rw [swap_mem_at]
    have : (swap 4 r).addr (⟨rStack, σ 9 + k⟩ : Addr Int) = ⟨rStack, σ 9 + k⟩ := by
      simp [RegionRenaming.addr, hF.stk]
    rw [this, h2 k a b]
    simp [RegionRenaming.cell, RegionRenaming.addr, hF.ret]
  · rw [swap_mem_at]
    have : (swap 4 r).addr (⟨rIn, o⟩ : Addr Int) = ⟨rIn, o⟩ := by
      simp [RegionRenaming.addr, hF.inn]
    rw [this, h3 o]; rfl

theorem swap_mem_in (r : Region) (hF : Fix (swap 4 r)) (m0 : Addr Int → Cell W32 Int) (σ : Nat → Int)
    (inp : Nat → Byte) (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ o : Nat, (swap 4 r).mem m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
  intro o
  rw [swap_mem_at]
  have : (swap 4 r).addr (⟨rIn, σ 0 + o⟩ : Addr Int) = ⟨rIn, σ 0 + o⟩ := by
    simp [RegionRenaming.addr, hF.inn]
  rw [this, hin o]; rfl

theorem entryWin_nOnly' : entryWin.nOnly = true := by decide +kernel

/-- An environment for the swapped memory: `env` on the numbered symbols. -/
def envSwap (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) : Key → W32
  | .n i => env (.n i)
  | .m rr off => cellX (m ⟨rr, off.eval σ⟩)

theorem envSwap_mem (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) :
    EnvMem (envSwap env σ m) σ m := fun _ _ => rfl

theorem mapState_envSwap (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) :
    mapState (envSwap env σ m) σ entryWin = mapState env σ entryWin :=
  mapState_nOnly _ _ σ (fun _ => rfl) entryWin entryWin_nOnly'

theorem wf_env' (ro : List Nat) (e e' : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (h : WfMemW ro [] e σ m) : WfMemW ro [] e' σ m := by
  obtain ⟨h1, h2, h3, _⟩ := h
  exact ⟨h1, h2, h3, fun k c h _ _ => by simp [plookup] at h⟩

end Hashtree.Proofs.WinLinkSwap
