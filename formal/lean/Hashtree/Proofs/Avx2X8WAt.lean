import Hashtree.Proofs.Avx2X8WAll
import Hashtree.Proofs.AvxX1WAt
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Kernels.X86.Avx2X8
open Hashtree.Proofs.AvxX4W (upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW)
open Hashtree.Proofs.Avx2X8WShift (KTE BODYLEN)
open Hashtree.Proofs.Avx2X8WStrip (KTEs)
open Hashtree.Proofs.Avx2X8WLoop (sIt8 TURNLEN)
open Hashtree.Proofs.Avx2X8WAll
open Hashtree.Proofs.AvxX1W (state_entryW list_map_self)

/-!
# The avx2_x8 W-mode runs with the x8 table at a fresh region

`Avx2X8WAll` places the x8 table at region `4`, as every kernel's own contract does.  In the
chain `x8 -> x4 -> x1` the memory is shared and each table has its own region; the x4 link is
stated at region `4` (`AvxX4LoopWAll.x4_runW`), so here the x8 run is moved to a region `r8`
by the swap renaming (`X86Ren.run_swap_chain`), as `AvxX1WAt.correctWAt` does for x1.

The entry state is fixed by the renaming (`AvxX1WAt.state_entryW`: every register of `entryW`
is a number or a pointer into a region the swap leaves alone); the caller's log `M` and the
final cut are renamed.  The renamed log is still a W-mode log (`outLogW_ren`: the swap fixes
`rOut` and `rStack`).
-/

namespace Hashtree.Proofs.Avx2X8WAt

/-- A log under the renaming. -/
def renLog (ρ : RegionRenaming) (M : CLog) : CLog :=
  M.map (fun p => (ρ.addr p.1, ρ.cell p.2))

theorem renLog_invol (ρ : RegionRenaming) (M : CLog) : renLog ρ (renLog ρ M) = M := by
  simp only [renLog, List.map_map]
  apply list_map_self
  intro p _
  simp only [Function.comp_def, RegionRenaming.addr_invol, RegionRenaming.cell_invol]

/-- The renaming moves through a log frame. -/
theorem state_fr (ρ : RegionRenaming) (L : CLog) (s : CState) :
    ρ.state (fr L s) = fr (renLog ρ L) (ρ.state s) := by
  simp only [RegionRenaming.state, fr, renLog, List.map_append]

/-- A W-mode log stays one under a renaming fixing the output and stack regions. -/
theorem outLogW_ren (ρ : RegionRenaming) (hOut : ρ.f rOut = rOut) (hStk : ρ.f rStack = rStack)
    (σ : Nat → Int) (M : CLog) (hM : OutLogW σ M) : OutLogW σ (renLog ρ M) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases hM q hq with h | ⟨h1, h2⟩
  · left
    show ρ.f q.1.region = rOut
    rw [h, hOut]
  · right
    refine ⟨?_, h2⟩
    show ρ.f q.1.region = rStack
    rw [h1, hStk]

/-- The swap's fixed regions, from the freshness of `r8`. -/
theorem swap_fix (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut)
    (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) :
    (swap 4 r8).f rNum = rNum ∧ (swap 4 r8).f rIn = rIn ∧ (swap 4 r8).f rOut = rOut ∧
      (swap 4 r8).f rStack = rStack ∧ (swap 4 r8).f rG = rG :=
  ⟨swap_fixes 4 r8 rNum (by decide) (Ne.symm hrNum),
   swap_fixes 4 r8 rIn (by decide) (Ne.symm hrIn),
   swap_fixes 4 r8 rOut (by decide) (Ne.symm hrOut),
   swap_fixes 4 r8 rStack (by decide) (Ne.symm hrStack),
   swap_fixes 4 r8 rG (by decide) (Ne.symm hrG)⟩

/-- The framed entry state is the swap image of the framed entry state with the renamed log. -/
theorem entry_swap (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut)
    (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) (env0 : Key → W32) (σ : Nat → Int) (M : CLog) :
    fr M (mapState env0 σ entryW) =
      (swap 4 r8).state (fr (renLog (swap 4 r8) M) (mapState env0 σ entryW)) := by
  obtain ⟨h0, h1, h2, h3, h6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  rw [state_fr, state_entryW (swap 4 r8) h0 h1 h2 h3 h6 env0 σ, renLog_invol]

/-- The W-mode memory shape of the x8 table at `r8`, moved to region 4 by the swap. -/
theorem wf_swap (r8 : Region) (hrIn : r8 ≠ rIn) (hrStack : r8 ≠ rStack) (hrRet : r8 ≠ rRet)
    (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (hw : WfMemAtW r8 rodata [] env0 σ mem0c) :
    WfMemW rodata [] env0 σ ((swap 4 r8).mem mem0c) :=
  wfMemAtW_swap r8 hrIn hrStack hrRet rodata [] env0 σ mem0c hw
    (fun k c hk => by simp [plookup] at hk)

/-- **`avx2_x8` for `8 ≤ c < 16` with its table at `r8`.** -/
theorem x8_runW_last_at (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut)
    (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemAtW r8 rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run prog r8 mem0c orcC (16 + (BODYLEN + 31)) (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r))) ∧
      OutLogW (upd15 σ) ((KTE r).mem.map (fun p =>
        (mapAddr (upd15 σ) p.1, mapCell e' (upd15 σ) p.2)) ++ M') := by
  obtain ⟨h0, h1, h2, h3, h6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  have hw' := wf_swap r8 hrIn hrStack hrRet env0 σ mem0c hw
  have hM' := outLogW_ren (swap 4 r8) h2 h3 σ M hM
  obtain ⟨r, e', M', hr, hrun, hlog⟩ :=
    x8_runW_last_abi env0 σ ((swap 4 r8).mem mem0c) orcC (renLog (swap 4 r8) M) hw' hM'
      hge hlt habi
  refine ⟨r, e', M', hr, ?_, hlog⟩
  rw [entry_swap r8 hrNum hrIn hrOut hrStack hrG env0 σ M, run_swap_chain r8 hrNum hrRet, hrun]

/-- **`avx2_x8` for `c = 8 (j + 1) + s`, `8 ≤ s < 16`, with its table at `r8`.** -/
theorem x8_runW_at (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut)
    (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemAtW r8 rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (j s : Nat) (hs : 8 ≤ s) (hs16 : s < 16)
    (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int)) (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run prog r8 mem0c orcC (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31))))
          (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r))) ∧
      OutLogW (sIt8 (j + 1) (upd15 σ)) ((KTEs r).mem.map (fun p =>
        (mapAddr (sIt8 (j + 1) (upd15 σ)) p.1, mapCell e' (sIt8 (j + 1) (upd15 σ)) p.2)) ++ M') := by
  obtain ⟨h0, h1, h2, h3, h6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  have hw' := wf_swap r8 hrIn hrStack hrRet env0 σ mem0c hw
  have hM' := outLogW_ren (swap 4 r8) h2 h3 σ M hM
  obtain ⟨r, e', M', hr, hrun, hlog⟩ :=
    x8_runW_abi env0 σ ((swap 4 r8).mem mem0c) orcC (renLog (swap 4 r8) M) hw' hM'
      j s hs hs16 hc habi
  refine ⟨r, e', M', hr, ?_, hlog⟩
  rw [entry_swap r8 hrNum hrIn hrOut hrStack hrG env0 σ M, run_swap_chain r8 hrNum hrRet, hrun]

end Hashtree.Proofs.Avx2X8WAt
