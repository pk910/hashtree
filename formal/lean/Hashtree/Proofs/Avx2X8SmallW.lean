import Hashtree.Proofs.Avx2X8ChainW

/-!
# avx2_x8 -> avx_x4 -> avx_x1 for the small counts `0 < c < 8`, and every count `c ≥ 1`

The x8 small path (`Avx2X8Align.x8_small_run`: the prologue, the alignment and 14 instructions
to the `jmp avx_x4` with the frame popped) moved to the x8 table region `r8`
(`x8_small_run_at`), and its hand-off: the resumed cut is the x4 entry state `entryW` at the
caller's `σ` up to flags, behind the small path's log (`x8Sm_resume`, `mapState_entryW`: the
dead `rax` of `entryWx` on symbol 15 is the output pointer under `upd15`), so the x4 W-mode
contracts apply after the flag-agreement `run_agree4`: the small path `KSm` (`0 < c < 4`) into
the x1 link at the framed cut (`x1_ksm_framed`), or the W-mode exit `K201W` (`4 ≤ c < 8`) into
the x1 link (`x1cut_framed`).  `x8_chain_W_all` joins this with `Avx2X8ChainW.x8_chain_W`: for
every count `c ≥ 1` the three runs end halted, without error and without a further tail.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.X86Chain (CS resume)
open Hashtree.Proofs.AvxX4W (upd15 envM mapState_entryW)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW outLogW_app sIt_s9)
open Hashtree.Proofs.AvxX4LoopFrame (sIt tau_count)
open Hashtree.Proofs.AvxX4LoopTurn (tau)
open Hashtree.Proofs.AvxX4LoopWExit (K201W K201W_err upd15_9 outLogW_s9)
open Hashtree.Proofs.AvxX4LoopWAll (x4_runW_last)
open Hashtree.Proofs.AvxX4Small (KSm KSm_err KSm_pc orcK small_prefix)
open Hashtree.Proofs.AvxX4Agree (run_agree4 Dsx4_exit)
open Hashtree.Proofs.AvxX4Exit (sigmaOf_tau0)
open Hashtree.Proofs.AvxX4X1WAgree (cutLog wfAt_cut swap_view_in outLogW_congr sigmaOf_s9
  x1cut_framed)
open Hashtree.Proofs.AvxX1W (steps InRange)
open Hashtree.Proofs.ShaniW (OutOk)
open Hashtree.Proofs.AvxX1Agree (Dsx hsound not_mem_Dsx)
open Hashtree.Proofs.Avx2X8WAt (renLog state_fr swap_fix entry_swap wf_swap outLogW_ren)
open Hashtree.Proofs.Avx2X8Align (x8Sm x8_small_run x8Sm_resume x8Sm_outLogW residue_lt)
open Hashtree.Proofs.Avx2X8X4WAgree (x4LastSteps K201W_pc mapState_mem_eq)
open Hashtree.Proofs.Avx2X8X1WAgree (agreeOn_resume x1_ksm_framed resume_fr)
open Hashtree.Proofs.Avx2X8ChainW (x8Steps x4Steps x4Steps_small x4Steps_last x8_chain_W)
open Hashtree.Spec

namespace Hashtree.Proofs.Avx2X8SmallW

/-! ## The small path with the x8 table at `r8` -/

/-- **The x8 small path, table at `r8`.** -/
theorem x8_small_run_at (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut)
    (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (h0 : 0 < σ 2) (h8 : σ 2 < 8) :
    ∃ (r : Nat) (e' : Key → W32), r < 32 ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC 20 (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr (renLog (swap 4 r8) M) (mapState e' (upd15 σ) (x8Sm r))) := by
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  have hw' := wf_swap r8 hrIn hrStack hrRet env0 σ mem0c hw
  have hM' := outLogW_ren (swap 4 r8) f2 f3 σ M hM
  have hr : (((σ 9 - 8) % 32).toNat : Int) = (σ 9 - 8) % 32 := by omega
  obtain ⟨e', hrun⟩ := x8_small_run env0 σ ((swap 4 r8).mem mem0c) orcC (renLog (swap 4 r8) M)
    hw' hM' h0 h8 ((σ 9 - 8) % 32).toNat hr
  refine ⟨((σ 9 - 8) % 32).toNat, e', residue_lt σ _ hr, ?_⟩
  rw [entry_swap r8 hrNum hrIn hrOut hrStack hrG env0 σ M, run_swap_chain r8 hrNum hrRet, hrun]

/-! ## The hand-off state -/

theorem entryWx_nOnly : Hashtree.Proofs.AvxX4W.entryWx.nOnly = true := by decide +kernel

theorem resume_state (ρ : RegionRenaming) (s : CS) : resume (ρ.state s) = ρ.state (resume s) :=
  rfl

theorem state_flags (ρ : RegionRenaming) (s : CS) (f : Option (Int × Int)) :
    ρ.state { s with flags := f } = { ρ.state s with flags := f } := rfl

/-- The resumed small-path cut, renamed: the x4 entry state at `σ` up to flags, behind the
renamed small-path log. -/
theorem handoff (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut)
    (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) (r : Nat) (hr : r < 32) (e' : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (M1 : CLog) :
    resume ((swap 4 r8).state (fr M1 (mapState e' (upd15 σ) (x8Sm r)))) =
      fr (renLog (swap 4 r8) ((mapState e' (upd15 σ) (x8Sm r)).mem ++ M1))
        { mapState e' σ entryW with flags := (mapState e' (upd15 σ) (x8Sm r)).flags } := by
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  rw [resume_state, resume_fr, x8Sm_resume r hr e' (upd15 σ),
    Hashtree.Proofs.ShaniW.fr_fr, state_fr, state_flags,
    mapState_nOnly e' (envM e' mem0c (upd15 σ)) (upd15 σ) (fun _ => rfl) _ entryWx_nOnly,
    mapState_entryW e' mem0c σ,
    Hashtree.Proofs.AvxX1W.state_entryW (swap 4 r8) f0 f1 f2 f3 f6 e' σ]

/-- The flagged entry state agrees with the plain one outside the flags. -/
theorem agree_flags (L : CLog) (s : CS) (f : Option (Int × Int)) :
    AgreeOn [0, 1, 16] (fr L s) (fr L { s with flags := f }) where
  pc := rfl
  halted := rfl
  tail := rfl
  err := rfl
  mem := rfl
  vr := rfl
  assume := rfl
  flags := fun h => absurd (by decide) h
  glen := rfl
  gpr := fun _ _ => rfl
  gpr16 := rfl

/-- `WfMemW` with an empty push list does not depend on the environment, nor on any symbol
but `σ 9`. -/
theorem wf_env (rodata : List Nat) (env env' : Key → W32) (σ σ' : Nat → Int) (h9 : σ' 9 = σ 9)
    (m : Addr Int → Cell W32 Int) (hw : WfMemW rodata [] env σ m) :
    WfMemW rodata [] env' σ' m := by
  obtain ⟨h1, h2, h3, _⟩ := hw
  exact ⟨h1, fun k h0 h8 => by rw [h9]; exact h2 k h0 h8, h3,
    fun k c hk => by simp [plookup] at hk⟩

/-! ## The x4 and x1 links after the small path -/

/-- **`0 < c < 4`.**  The x4 small path from the flagged entry state behind a W-mode log, then
the x1 link: halted, no error, no tail. -/
theorem small_x4_x1 (c : Nat) (inp : Nat → Byte) (e' env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (L : CLog) (r1 : Region)
    (f : Option (Int × Int))
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hL : OutLogW σ L) (hc : σ 2 = (c : Int)) (h0 : 0 < c) (h4 : c < 4)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let g : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps c)
      (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
        (fr L { mapState e' σ entryW with flags := f })))
    g.halted = true ∧ g.err = none ∧ g.tail = none := by
  intro g
  let E := ecomb e' σ (view L mem0c)
  have hwv : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] E σ (view L mem0c) :=
    Hashtree.Proofs.AvxX4LoopWFrame.wfW_view _ env0 E σ mem0c L hL hw4
  have hsp := small_prefix E σ (view L mem0c) orcC hwv (envMem_ecomb E σ (view L mem0c))
    (by rw [hc]; omega) (by rw [hc]; omega)
  have hrun : run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8 (fr L (mapState e' σ entryW)) =
      fr L (mapState (envAbs E (run Hashtree.Kernels.X86.AvxX4.prog 4
        (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW)) σ KSm) := by
    rw [run_fr, mapState_nOnly e' E σ (fun _ => rfl) entryW
      Hashtree.Proofs.WrapperAmd64.entryW_nOnly, hsp]
  have hag := run_agree4 4 mem0c orcC 8 (fr L (mapState e' σ entryW))
    (fr L { mapState e' σ entryW with flags := f }) rfl (agree_flags L (mapState e' σ entryW) f)
    (by rw [hrun]; simp only [fr, mapState, KSm_err])
  rw [hrun] at hag
  have hpc : (fr L (mapState (envAbs E (run Hashtree.Kernels.X86.AvxX4.prog 4
      (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW)) σ KSm)).pc = 4143 := by
    simp only [fr, mapState, KSm_pc]
  rw [hpc, Dsx4_exit] at hag
  have hX := x1_ksm_framed c inp _ σ σ env0 mem0c orcC L r1 _ h1Num h1In h1Out h1Stack h1G h1Ret
    hw1 hL rfl hc hin hag
  dsimp only at hX
  exact ⟨hX.1, hX.2.1, hX.2.2.1⟩

/-- **`4 ≤ c < 8`.**  The x4 W-mode exit from the flagged entry state behind a W-mode log, then
the x1 link for the `c - 4` remaining blocks: halted, no error, no tail. -/
theorem last_x4_x1 (c : Nat) (inp : Nat → Byte) (e' env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (L : CLog) (r1 : Region)
    (f : Option (Int × Int))
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hL : OutLogW σ L) (hc : σ 2 = (c : Int)) (h4 : 4 ≤ c) (h8 : c < 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + 256 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let g : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 4))
      (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
        (fr L { mapState e' σ entryW with flags := f })))
    g.halted = true ∧ g.err = none ∧ g.tail = none := by
  intro g
  obtain ⟨e4, M4, hrun, hlog⟩ := x4_runW_last e' σ mem0c orcC L
    (wf_env _ env0 e' σ σ rfl mem0c hw4) hL c h4 h8 hc
  have hag := run_agree4 4 mem0c orcC x4LastSteps (fr L (mapState e' σ entryW))
    (fr L { mapState e' σ entryW with flags := f }) rfl (agree_flags L (mapState e' σ entryW) f)
    (by unfold x4LastSteps; rw [hrun]; simp only [fr, mapState, K201W_err])
  have hrun' : run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
      (fr L (mapState e' σ entryW)) = fr M4 (mapState e4 (sIt 0 (upd15 σ)) K201W) := by
    unfold x4LastSteps; exact hrun
  rw [hrun'] at hag
  have hpc : (fr M4 (mapState e4 (sIt 0 (upd15 σ)) K201W)).pc = 4143 := by
    simp only [fr, mapState, K201W_pc]
  rw [hpc, Dsx4_exit] at hag
  -- the x1 link at the framed cut
  let τ : Nat → Int := sIt 0 (upd15 σ)
  have hτ9 : τ 9 = σ 9 := by show sIt 0 (upd15 σ) 9 = σ 9; rw [sIt_s9, upd15_9]
  have h9 : sigmaOf tau τ 9 = σ 9 := by rw [sigmaOf_s9]; exact hτ9
  have hlog' : OutLogW (sigmaOf tau τ) (cutLog e4 τ M4) :=
    outLogW_congr _ _ (sigmaOf_s9 _) _ (by rw [cutLog, mapState_mem_eq]; exact hlog)
  have hτ0 : τ 0 = σ 0 := by show sIt 0 (upd15 σ) 0 = σ 0; simp [sIt, upd15]
  have hτ2 : τ 2 = σ 2 := by show sIt 0 (upd15 σ) 2 = σ 2; simp [sIt, upd15]
  have hX := x1cut_framed (c - 4) inp e4 τ mem0c M4 orcC r1 h1Num h1In h1Out h1Stack h1G h1Ret
    (wfAt_cut r1 _ env0 _ σ (sigmaOf tau τ) h9 mem0c _ hlog' h1Out h1Stack hw1)
    (fun _ _ => rfl) (by rw [tau_count, hτ2, hc]; omega)
    (fun o => by
      rw [sigmaOf_tau0, hτ0]
      exact swap_view_in r1 h1In mem0c _ _ hlog' _ _ (hin o))
  dsimp only at hX
  obtain ⟨hrunX, hhalt, herr, htail, _⟩ := hX
  have hag' := agreeOn_resume hag
  have hpre : AgreeOn (Dsx (resume (fr M4 (mapState e4 τ K201W))).pc)
      (resume (fr M4 (mapState e4 τ K201W)))
      (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
        (fr L { mapState e' σ entryW with flags := f }))) :=
    hag'.mono (fun i hi => by
      show i ∈ Dsx 0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> decide)
  have herr1 : (run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 4))
      (resume (fr M4 (mapState e4 τ K201W)))).err = none :=
    (congrArg State.err hrunX).trans herr
  have hA := run_agree Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC Dsx hsound
    (steps (c - 4)) _ _ hpre herr1
  rw [hrunX] at hA
  exact ⟨hA.halted ▸ hhalt, hA.err ▸ herr, hA.tail ▸ htail⟩

/-! ## The chain for `0 < c < 8` and for every count -/

/-- **x8 -> x4 -> x1 for `0 < c < 8`.** -/
theorem x8_chain_small (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hc : σ 2 = (c : Int)) (h0 : 0 < c) (h8 : c < 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let g8 : CS := run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC 20
      (fr M (mapState env0 σ entryW))
    let g4 : CS := run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4Steps c) (resume g8)
    let g1 : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 4)) (resume g4)
    g1.halted = true ∧ g1.err = none ∧ g1.tail = none := by
  intro g8 g4 g1
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  obtain ⟨r, e', hr, hrun⟩ := x8_small_run_at r8 hrNum hrIn hrOut hrStack hrG hrRet env0 σ mem0c
    orcC M hw8 hM (by rw [hc]; omega) (by rw [hc]; omega)
  let L : CLog := renLog (swap 4 r8) ((mapState e' (upd15 σ) (x8Sm r)).mem ++ renLog (swap 4 r8) M)
  have hL : OutLogW σ L :=
    outLogW_ren (swap 4 r8) f2 f3 σ _ (outLogW_app σ
      (outLogW_s9 _ (upd15_9 σ).symm (x8Sm_outLogW r hr e' (upd15 σ)))
      (outLogW_ren (swap 4 r8) f2 f3 σ M hM))
  have hg8 : resume g8 = fr L { mapState e' σ entryW with
      flags := (mapState e' (upd15 σ) (x8Sm r)).flags } := by
    show resume (run _ r8 mem0c orcC 20 _) = _
    rw [hrun]
    exact handoff r8 hrNum hrIn hrOut hrStack hrG r hr e' σ mem0c _
  by_cases h4 : c < 4
  · have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps c)
        (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
          (fr L { mapState e' σ entryW with flags := (mapState e' (upd15 σ) (x8Sm r)).flags }))) := by
      show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps c) (resume g8)))
        = _
      rw [hg8, x4Steps_small c (by omega) h4, Nat.mod_eq_of_lt h4]
    rw [hg1]
    exact small_x4_x1 c inp e' env0 σ mem0c orcC L r1 _ h1Num h1In h1Out h1Stack h1G h1Ret hw4
      hw1 hL hc h0 h4 hin
  · have hc4 : c % 4 = c - 4 := by omega
    have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 4))
        (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
          (fr L { mapState e' σ entryW with flags := (mapState e' (upd15 σ) (x8Sm r)).flags }))) := by
      show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps c) (resume g8)))
        = _
      rw [hg8, x4Steps_last c (by omega) h4, hc4]
    rw [hg1]
    exact last_x4_x1 c (fun o => inp (256 + o)) e' env0 σ mem0c orcC L r1 _ h1Num h1In h1Out
      h1Stack h1G h1Ret hw4 hw1 hL hc (by omega) h8
      (fun o => by
        have h := hin (256 + o)
        rw [show σ 0 + 256 + (o : Int) = σ 0 + ((256 + o : Nat) : Int) from by omega]
        exact h)

/-- The x8 run's step count at any count `c ≥ 1`: the small path below 8. -/
def x8StepsAll (c : Nat) : Nat := if c < 8 then 20 else x8Steps c

/-- **x8 -> x4 -> x1 at the wrapper call state, every count `c ≥ 1`.**  The x8 run for
`x8StepsAll c` steps, the x4 run for `x4Steps (c % 8)` from the resumed x8 state and, when
`c % 8 ≠ 0`, the x1 run for `steps (c % 4)` from the resumed x4 state end halted, without error
and without a further tail. -/
theorem x8_chain_W_all (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hc : σ 2 = (c : Int)) (h1 : 1 ≤ c) (habi : σ 9 % 16 = 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let g8 : CS := run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8StepsAll c)
      (fr M (mapState env0 σ entryW))
    let g4 : CS := run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4Steps (c % 8)) (resume g8)
    let g1 : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 4)) (resume g4)
    (c % 8 = 0 → g4.halted = true ∧ g4.err = none ∧ g4.tail = none) ∧
    (c % 8 ≠ 0 → g1.halted = true ∧ g1.err = none ∧ g1.tail = none) := by
  intro g8 g4 g1
  by_cases hlt : c < 8
  · have hs : x8StepsAll c = 20 := by simp only [x8StepsAll, if_pos hlt]
    have hm : c % 8 = c := Nat.mod_eq_of_lt hlt
    refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
    have H := x8_chain_small c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack hrG hrRet
      h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc (by omega) hlt hin
    dsimp only at H
    have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 4))
        (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4Steps c)
          (resume (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC 20
            (fr M (mapState env0 σ entryW)))))) := by
      show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
        (resume (run _ r8 mem0c orcC (x8StepsAll c) _)))) = _
      rw [hs, hm]
    rw [hg1]
    exact H
  · have hs : x8StepsAll c = x8Steps c := by simp only [x8StepsAll, if_neg hlt]
    have H := x8_chain_W c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack hrG hrRet
      h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc (by omega) habi hin
    dsimp only at H
    have hg8 : g8 = run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8Steps c)
        (fr M (mapState env0 σ entryW)) := by
      show run _ r8 mem0c orcC (x8StepsAll c) _ = _
      rw [hs]
    have hg4 : g4 = run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4Steps (c % 8))
        (resume (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8Steps c)
          (fr M (mapState env0 σ entryW)))) := by
      show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume g8) = _
      rw [hg8]
    have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 4))
        (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4Steps (c % 8))
          (resume (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8Steps c)
            (fr M (mapState env0 σ entryW)))))) := by
      show run _ r1 mem0c orcC (steps (c % 4)) (resume g4) = _
      rw [hg4]
    rw [hg4, hg1]
    exact H

end Hashtree.Proofs.Avx2X8SmallW
