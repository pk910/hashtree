import Hashtree.Proofs.Avx2X8ChainOut
import Hashtree.Proofs.Avx2X8ChainC

/-!
# avx2_x8 -> avx_x4 -> avx_x1: the output clause for every count `c ≥ 1`, in the chain form

* `x8_chain_small_out` (`0 < c < 8`): the x8 small path writes only its 40 pointer bytes below the
  return marker (`smallLog`, one kernel `decide` over the 32 residues); then the x4 small path
  (no write) and the x1 link (`small_x4_x1_out`), or the x4 W-mode exit (`TurnOut4Last`) and the
  x1 link (`last_x4_x1_out`).
* `x8_chain_out_all`: with `Avx2X8ChainOut.x8_chain_W_out`, every count `c ≥ 1`.
* `x8SpecsO`, `x8KSpecC_out`, `x8_callChain_out`: the chain form (`X86Chain.KSpecC`, `callChain`)
  with the output clause in the returning links' post-condition: the wrapper's chain call returns
  normally and its log holds all `c` blocks (`OutOk inp (σ 1) c`) inside the footprint `FootC`.

Hypotheses: R2c's `TurnOut8`, `TurnOut8Last` (proved on research/formal-r2c-x16out, 7151bbd) and
`TurnOut4Last` (statement `Avx2X8OutLink`, for R2c).
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.X86Chain
open Hashtree.Proofs.AvxX4W (upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW outLogW_app sIt_s9)
open Hashtree.Proofs.AvxX4LoopFrame (sIt tau_count)
open Hashtree.Proofs.AvxX4LoopTurn (tau)
open Hashtree.Proofs.AvxX4LoopWExit (K201W K201W_err upd15_9 outLogW_s9)
open Hashtree.Proofs.AvxX4LoopWAll (x4_runW_last)
open Hashtree.Proofs.AvxX4Small (KSm KSm_err KSm_pc orcK small_prefix)
open Hashtree.Proofs.AvxX4Agree (run_agree4 Dsx4_exit)
open Hashtree.Proofs.AvxX4Exit (sigmaOf_tau0)
open Hashtree.Proofs.AvxX4X1WAgree (cutLog cutBare wfAt_cut swap_view_in outLogW_congr sigmaOf_s9
  x1cut_framed view_in)
open Hashtree.Proofs.AvxX1W (steps InRange)
open Hashtree.Proofs.ShaniW (OutOk)
open Hashtree.Proofs.AvxX1Agree (Dsx hsound not_mem_Dsx)
open Hashtree.Proofs.Avx2X8WAt (renLog renLog_invol swap_fix outLogW_ren)
open Hashtree.Proofs.Avx2X8Align (x8Sm)
open Hashtree.Proofs.Avx2X8X4WAgree (x4LastSteps K201W_pc fr_nil)
open Hashtree.Proofs.Avx2X8X1WAgree (agreeOn_resume x1_ksm_framed resume_fr)
open Hashtree.Proofs.Avx2X8ChainW (x8Steps x4Steps x4Steps_small x4Steps_last)
open Hashtree.Proofs.Avx2X8SmallW (x8StepsAll x8_small_run_at handoff agree_flags wf_env)
open Hashtree.Proofs.Avx2X8ChainC (link8 link4 link1 Ret x8_tails)
open Hashtree.Proofs.Avx2X8OutLink
open Hashtree.Proofs.Avx2X8ChainOut
open Hashtree.Spec

namespace Hashtree.Proofs.Avx2X8ChainOutAll

theorem mem_fr (L : CLog) (s : CS) : (fr L s).mem = s.mem ++ L := rfl
theorem cutLog_eq (e : Key → W32) (τ : Nat → Int) (M : CLog) :
    cutLog e τ M = (fr M (mapState e τ K201W)).mem := rfl

/-! ## The x8 small path's log -/

def smallCell (p : Addr Lin × Cell E Lin) : Bool :=
  decide (p.1.region = rStack ∧ p.1.off.c = stkC ∧ -984 ≤ p.1.off.k ∧ p.1.off.k < 0)

theorem smallLog_all : (List.range 32).all (fun r => (x8Sm r).mem.all smallCell) = true := by
  decide +kernel

/-- The small path writes only stack bytes of the frame below the return marker. -/
theorem smallLog (r : Nat) (hr : r < 32) (e : Key → W32) (σ : Nat → Int) :
    ∀ p ∈ (mapState e σ (x8Sm r)).mem, p.1.region = rStack ∧ σ 9 - 984 ≤ p.1.off ∧ p.1.off < σ 9 := by
  have hf : (x8Sm r).mem.all smallCell = true :=
    List.all_eq_true.mp smallLog_all r (List.mem_range.mpr hr)
  intro p hp
  simp only [mapState, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have h : smallCell q = true := List.all_eq_true.mp hf q hq
  obtain ⟨h1, hc, hk1, hk2⟩ := of_decide_eq_true h
  simp only [mapAddr, h1]
  rw [Hashtree.Proofs.AvxX4LoopWFrame.eval_stk σ q.1.off hc]
  exact ⟨trivial, by omega, by omega⟩

/-! ## The x4 and x1 links after the small path, with their writes -/

/-- **`0 < c < 4`** with the x1 link's writes `F` over the caller's log. -/
theorem small_x4_x1_out (c : Nat) (inp : Nat → Byte) (e' env0 : Key → W32) (σ : Nat → Int)
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
    ∃ F : CLog, g.mem = F ++ L ∧ InRange (σ 9) (σ 1) (32 * c) F ∧ OutOk inp (σ 1) c F := by
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
  exact ⟨_, hX.2.2.2.1, hX.2.2.2.2.1, hX.2.2.2.2.2.1⟩

theorem tauS_1 (σ : Nat → Int) : sigmaOf tau (sIt 0 (upd15 σ)) 1 = σ 1 + 128 := by
  rw [Hashtree.Proofs.AvxX4Exit.sigmaOf_tau1, Hashtree.Proofs.AvxX4Exit.sIt_1, upd15_1]; omega

/-- **`4 ≤ c < 8`** with the x4 link's writes `A` (4 blocks, `TurnOut4Last`) and the x1 link's
writes `F` over the caller's log. -/
theorem last_x4_x1_out (hT : TurnOut4Last) (c : Nat) (inp inp4 : Nat → Byte) (e' env0 : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (L : CLog) (r1 : Region)
    (f : Option (Int × Int))
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hL : OutLogW σ L) (hc : σ 2 = (c : Int)) (h4 : 4 ≤ c) (h8 : c < 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + 256 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hin4 : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp4 o).zeroExtend 32) 0) :
    let g : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 4))
      (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
        (fr L { mapState e' σ entryW with flags := f })))
    ∃ A F : CLog, g.mem = F ++ (A ++ L) ∧
      (∀ p ∈ A, (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 128) ∨
        (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
      OutOk inp4 (σ 1) 4 A ∧
      InRange (σ 9) (σ 1 + 128) (32 * (c - 4)) F ∧ OutOk inp (σ 1 + 128) (c - 4) F := by
  intro g
  obtain ⟨e4, M4, hrun, hlog⟩ := x4_runW_last e' σ mem0c orcC L
    (wf_env _ env0 e' σ σ rfl mem0c hw4) hL c h4 h8 hc
  have hrun' : run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
      (fr L (mapState e' σ entryW)) = fr M4 (mapState e4 (sIt 0 (upd15 σ)) K201W) := by
    unfold x4LastSteps; exact hrun
  have hag := run_agree4 4 mem0c orcC x4LastSteps (fr L (mapState e' σ entryW))
    (fr L { mapState e' σ entryW with flags := f }) rfl (agree_flags L (mapState e' σ entryW) f)
    (by rw [hrun']; simp only [fr, mapState, K201W_err])
  have hmem4 := hag.mem
  rw [hrun'] at hag
  have hpc : (fr M4 (mapState e4 (sIt 0 (upd15 σ)) K201W)).pc = 4143 := by
    simp only [fr, mapState, K201W_pc]
  rw [hpc, Dsx4_exit] at hag
  -- the x1 link at the framed cut
  let τ : Nat → Int := sIt 0 (upd15 σ)
  have hτ9 : τ 9 = σ 9 := by show sIt 0 (upd15 σ) 9 = σ 9; rw [sIt_s9, upd15_9]
  have h9 : sigmaOf tau τ 9 = σ 9 := by rw [sigmaOf_s9]; exact hτ9
  have hlog' : OutLogW (sigmaOf tau τ) (cutLog e4 τ M4) :=
    outLogW_congr _ _ (sigmaOf_s9 _) _ (by
      rw [cutLog, Hashtree.Proofs.Avx2X8X4WAgree.mapState_mem_eq]; exact hlog)
  have hτ0 : τ 0 = σ 0 := by show sIt 0 (upd15 σ) 0 = σ 0; simp [sIt, upd15]
  have hτ2 : τ 2 = σ 2 := by show sIt 0 (upd15 σ) 2 = σ 2; simp [sIt, upd15]
  have hX := x1cut_framed (c - 4) inp e4 τ mem0c M4 orcC r1 h1Num h1In h1Out h1Stack h1G h1Ret
    (wfAt_cut r1 _ env0 _ σ (sigmaOf tau τ) h9 mem0c _ hlog' h1Out h1Stack hw1)
    (fun _ _ => rfl) (by rw [tau_count, hτ2, hc]; omega)
    (fun o => by
      rw [sigmaOf_tau0, hτ0]
      exact swap_view_in r1 h1In mem0c _ _ hlog' _ _ (hin o))
  dsimp only at hX
  obtain ⟨hrunX, hhalt, herr, htail, hR, hO, _⟩ := hX
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
  have hgm := hA.mem
  rw [mem_fr] at hgm
  -- the x4 link's own writes
  have hcl : cutLog e4 τ M4 = (run Hashtree.Kernels.X86.AvxX4.prog 4 (view L mem0c) orcC x4LastSteps
      (mapState e' σ entryW)).mem ++ L := by
    rw [cutLog_eq, ← hrun', run_fr, mem_fr]
  have hgm2 := hgm.symm.trans (congrArg (fun t => _ ++ t) hcl)
  have hwv : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] e' σ (view L mem0c) :=
    Hashtree.Proofs.AvxX4LoopWFrame.wfW_view _ env0 e' σ mem0c L hL hw4
  obtain ⟨hF4, hO4⟩ := hT e' σ (view L mem0c) orcC [] inp4 hwv (fun p hp => by cases hp)
    (by rw [hc]; exact_mod_cast h4) (by rw [hc]; exact_mod_cast h8)
    (fun o => by rw [view_in mem0c L σ hL]; exact hin4 o)
  rw [fr_nil] at hF4 hO4
  have h1x : sigmaOf tau τ 1 = σ 1 + 128 := tauS_1 σ
  rw [h9, h1x] at hR
  rw [h1x] at hO
  refine ⟨_, _, hgm2, fun p hp => ?_, hO4, hR, hO⟩
  rcases hF4 p hp with h | h | h
  · cases h
  · exact Or.inl h
  · exact Or.inr h

theorem foot1' (σ : Nat → Int) (c k n : Nat) (hkn : k + n ≤ c) (sp ob : Int) (h9 : sp = σ 9)
    (h1 : ob = σ 1 + 32 * (k : Int)) (F : CLog) (h : InRange sp ob (32 * n) F) :
    ∀ p ∈ F, (p.1.region = rOut ∧ σ 1 + 32 * (k : Int) ≤ p.1.off ∧ p.1.off < σ 1 + 32 * (c : Int)) ∨
      (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9) := by
  subst h9 h1
  intro p hp
  rcases h p hp with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · left; refine ⟨a, b, ?_⟩; push_cast at d; omega
  · right; refine ⟨a, ?_, d⟩; unfold D8L; omega

/-! ## `0 < c < 8` -/

theorem outOk_zero_shift (inp : Nat → Byte) (ob : Int) (n : Nat) (F : CLog) (h : OutOk inp ob n F) :
    OutOk (fun o => inp (64 * 0 + o)) (ob + 32 * ((0 : Nat) : Int)) n F := by
  have h1 : (fun o => inp (64 * 0 + o)) = inp := by funext o; simp
  have h2 : ob + 32 * ((0 : Nat) : Int) = ob := by simp
  rw [h1, h2]; exact h

/-- **The output clause for `0 < c < 8`.** -/
theorem x8_chain_small_out (hT4L : TurnOut4Last)
    (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    OutOk inp (σ 1) c g1.mem ∧ FootC σ c M g1.mem := by
  intro g8 g4 g1
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  obtain ⟨r, e', hr, hrun⟩ := x8_small_run_at r8 hrNum hrIn hrOut hrStack hrG hrRet env0 σ mem0c
    orcC M hw8 hM (by rw [hc]; omega) (by rw [hc]; omega)
  let L : CLog := renLog (swap 4 r8) ((mapState e' (upd15 σ) (x8Sm r)).mem ++ renLog (swap 4 r8) M)
  have hL : OutLogW σ L :=
    outLogW_ren (swap 4 r8) f2 f3 σ _ (outLogW_app σ
      (outLogW_s9 _ (upd15_9 σ).symm (Hashtree.Proofs.Avx2X8Align.x8Sm_outLogW r hr e' (upd15 σ)))
      (outLogW_ren (swap 4 r8) f2 f3 σ M hM))
  have hLf : FootC σ c M L := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨a, b, d⟩ := smallLog r hr e' (upd15 σ) q h
      rw [upd15_9] at b d
      right; right
      refine ⟨by show (swap 4 r8).f q.1.region = rStack; rw [a, f3], ?_, d⟩
      unfold D8L; exact b
    · left
      rw [← renLog_invol (swap 4 r8) M]
      exact List.mem_map_of_mem h
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
    obtain ⟨F, hgm, hR, hO⟩ := small_x4_x1_out c inp e' env0 σ mem0c orcC L r1 _ h1Num h1In h1Out
      h1Stack h1G h1Ret hw4 hw1 hL hc h0 h4 hin
    rw [hg1, hgm]
    have H := layer inp σ c M 0 c F L (outOk_zero_shift inp _ c F hO)
      (foot1 σ σ c 0 c (by omega) rfl (by simp) F hR) (outOk_zero inp _ L) hLf
    rw [Nat.zero_add] at H
    exact H
  · have hc4 : c % 4 = c - 4 := by omega
    have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 4))
        (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
          (fr L { mapState e' σ entryW with flags := (mapState e' (upd15 σ) (x8Sm r)).flags }))) := by
      show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps c) (resume g8)))
        = _
      rw [hg8, x4Steps_last c (by omega) h4, hc4]
    obtain ⟨A, F, hgm, hAf, hAO, hR, hO⟩ := last_x4_x1_out hT4L c (fun o => inp (64 * 4 + o)) inp
      e' env0 σ mem0c orcC L r1 _ h1Num h1In h1Out h1Stack h1G h1Ret hw4 hw1 hL hc (by omega) h8
      (fun o => by
        have h := hin (64 * 4 + o)
        rw [show σ 0 + 256 + (o : Int) = σ 0 + ((64 * 4 + o : Nat) : Int) from by omega]
        exact h) hin
    rw [hg1, hgm]
    have H4 := layer inp σ c M 0 4 A L (outOk_zero_shift inp _ 4 A hAO)
      (foot4 σ σ c 0 (by omega) rfl (by simp) A hAf) (outOk_zero inp _ L) hLf
    rw [Nat.zero_add] at H4
    have H := layer inp σ c M 4 (c - 4) F (A ++ L)
      (outOk_cast _ _ _ _ _ _ _ rfl (by push_cast; omega) rfl hO)
      (foot1' σ c 4 (c - 4) (by omega) (σ 9) (σ 1 + 128) rfl (by push_cast; omega) F hR) H4.1 H4.2
    rw [show 4 + (c - 4) = c by omega] at H
    exact H

/-! ## Every count -/

/-- **The avx2_x8 -> avx_x4 -> avx_x1 chain's output clause, every count `c ≥ 1`.** -/
theorem x8_chain_out_all (hT8 : TurnOut8) (hT8L : TurnOut8Last) (hT4L : TurnOut4Last)
    (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    (c % 8 = 0 → OutOk inp (σ 1) c g4.mem ∧ FootC σ c M g4.mem) ∧
    (c % 8 ≠ 0 → OutOk inp (σ 1) c g1.mem ∧ FootC σ c M g1.mem) := by
  intro g8 g4 g1
  by_cases hlt : c < 8
  · have hs : x8StepsAll c = 20 := by simp only [x8StepsAll, if_pos hlt]
    have hm : c % 8 = c := Nat.mod_eq_of_lt hlt
    refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
    have H := x8_chain_small_out hT4L c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack hrG
      hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc (by omega) hlt hin
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
    have H := x8_chain_W_out hT8 hT8L hT4L c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut
      hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc (by omega) habi hin
    dsimp only at H
    have hg8 : g8 = run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8Steps c)
        (fr M (mapState env0 σ entryW)) := by
      show run _ r8 mem0c orcC (x8StepsAll c) _ = _
      rw [hs]
    have hg4 : g4 = run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4Steps (c % 8))
        (resume (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8Steps c)
          (fr M (mapState env0 σ entryW)))) := by
      show run _ 4 mem0c orcC _ (resume g8) = _
      rw [hg8]
    have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 4))
        (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4Steps (c % 8))
          (resume (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8Steps c)
            (fr M (mapState env0 σ entryW)))))) := by
      show run _ r1 mem0c orcC _ (resume g4) = _
      rw [hg4]
    rw [hg4, hg1]
    exact H

/-! ## The chain form -/

/-- The run-level post plus the output clause. -/
def RetO (inp : Nat → Byte) (σ : Nat → Int) (c : Nat) (M : CLog) (f : CS) : Prop :=
  Ret f ∧ OutOk inp (σ 1) c f.mem ∧ FootC σ c M f.mem

/-- `x8Specs` with the output clause in the returning links' post-condition. -/
def x8SpecsO (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region) : List Spec :=
  let s0 : CS := fr M (mapState env0 σ entryW)
  let g8 : CS := step mem0c orcC c (link8 r8) s0
  let g4 : CS := step mem0c orcC c link4 (resume g8)
  [ ⟨link8 r8, (· = s0), RetO inp σ c M⟩, ⟨link4, (· = resume g8), RetO inp σ c M⟩,
    ⟨link1 r1, (fun s => c % 8 ≠ 0 ∧ s = resume g4), RetO inp σ c M⟩ ]

/-- **The x8 chain as `KSpecC`, with the output clause.** -/
theorem x8KSpecC_out (hT8 : TurnOut8) (hT8L : TurnOut8Last) (hT4L : TurnOut4Last)
    (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    KSpecC mem0c orcC c (x8SpecsO c inp env0 σ mem0c orcC M r8 r1) := by
  have T := x8_tails c env0 σ mem0c orcC M r8 hrNum hrIn hrOut hrStack hrG hrRet hw8 hw4 hM hc h1 habi
  have H := Hashtree.Proofs.Avx2X8SmallW.x8_chain_W_all c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn
    hrOut hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc h1 habi hin
  have O := x8_chain_out_all hT8 hT8L hT4L c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut
    hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc h1 habi hin
  dsimp only at T H O
  obtain ⟨t8e, t8t, t4⟩ := T
  obtain ⟨H0, H1⟩ := H
  obtain ⟨O0, O1⟩ := O
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    subst hs
    exact ⟨t8e, Or.inr ⟨t8t, rfl⟩⟩
  · intro s hs
    subst hs
    by_cases hz : c % 8 = 0
    · obtain ⟨hh, he, ht⟩ := H0 hz
      exact ⟨he, Or.inl ⟨ht, ⟨hh, he, ht⟩, O0 hz⟩⟩
    · obtain ⟨he, ht⟩ := t4 hz
      exact ⟨he, Or.inr ⟨ht, hz, rfl⟩⟩
  · intro s ⟨hz, hs⟩
    subst hs
    obtain ⟨hh, he, ht⟩ := H1 hz
    exact ⟨he, ht, ⟨hh, he, ht⟩, O1 hz⟩

/-- **The wrapper's chain call for the x8 chain, with the output clause**: `callChain` from the
wrapper call state behind a W-mode log returns normally, and its log holds all `c` output
blocks with their SHA-256 bytes, every cell inside the caller's log, the `c` output blocks or
the 984-byte frame below the return marker. -/
theorem x8_callChain_out (hT8 : TurnOut8) (hT8L : TurnOut8Last) (hT4L : TurnOut4Last)
    (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    let fin : CS := callChain mem0c orcC c (x8SpecsO c inp env0 σ mem0c orcC M r8 r1)
      (fr M (mapState env0 σ entryW))
    fin.err = none ∧ fin.tail = none ∧ fin.halted = false ∧ fin.pc = 0 ∧
      OutOk inp (σ 1) c fin.mem ∧ FootC σ c M fin.mem := by
  have hok := x8KSpecC_out hT8 hT8L hT4L c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack
    hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc h1 habi hin
  have hpc : ({ fr M (mapState env0 σ entryW) with pc := 0 } : CS) = fr M (mapState env0 σ entryW) := by
    simp [fr, mapState, entryW]
  have h := chain_sound mem0c orcC c (x8SpecsO c inp env0 σ mem0c orcC M r8 r1)
    { fr M (mapState env0 σ entryW) with pc := 0 } hok (by rw [hpc]; rfl)
  dsimp only at h
  obtain ⟨he, _, hpost⟩ := h
  have hO : OutOk inp (σ 1) c (chainRun mem0c orcC c (x8SpecsO c inp env0 σ mem0c orcC M r8 r1)
      { fr M (mapState env0 σ entryW) with pc := 0 }).mem ∧
      FootC σ c M (chainRun mem0c orcC c (x8SpecsO c inp env0 σ mem0c orcC M r8 r1)
      { fr M (mapState env0 σ entryW) with pc := 0 }).mem := by
    rcases hpost with h | h | h <;> exact h.2
  exact ⟨he, rfl, rfl, rfl, hO.1, hO.2⟩

end Hashtree.Proofs.Avx2X8ChainOutAll
