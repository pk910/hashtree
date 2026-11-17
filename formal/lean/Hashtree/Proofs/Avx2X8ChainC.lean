import Hashtree.Proofs.Avx2X8SmallW

/-!
# avx2_x8 -> avx_x4 -> avx_x1 in the chain form (`X86Chain.KSpecC`, `callChain`)

`Avx2X8SmallW.x8_chain_W_all` is run-level: the x8 run, the x4 run from the resumed x8 state and
the x1 run from the resumed x4 state end halted without error or tail.  The wrapper calls the
chain through `X86Chain.callChain`, which follows a tail only when the run names the next link;
this module supplies the tail facts of the first two runs (`x8_tails`: the x8 run always ends
on the tail call into `hashtree_sha256_avx_x4`; the x4 run ends on the tail call into
`hashtree_sha256_avx_x1` when `c % 8 ≠ 0`), restates the chain as `KSpecC` for the three links
with the tables at `r8`, region 4 and `r1` (`x8KSpecC`), and composes it (`x8_callChain`).

Pre-conditions are the exact hand-over states (the x8 run from the wrapper call state, the x4
run from the resumed x8 state, the x1 run from the resumed x4 state); the post-condition is
run-level (`halted`, no error, no tail).  The output clause (`OutOk` of all `c` blocks over the
chain's log) plugs in R2c's `TurnOut8` (and `turnOut4`) and is the next increment.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.X86Chain
open Hashtree.Proofs.AvxX4W (upd15 mapState_entryW)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW outLogW_app)
open Hashtree.Proofs.AvxX4LoopWExit (K201W K201W_err K201W_tail upd15_9 outLogW_s9)
open Hashtree.Proofs.AvxX4LoopWAll (x4_runW_last)
open Hashtree.Proofs.AvxX4Small (KSm KSm_err KSm_tail orcK small_prefix)
open Hashtree.Proofs.AvxX4Agree (run_agree4)
open Hashtree.Proofs.AvxX1W (steps)
open Hashtree.Proofs.Avx2X8WAt (renLog outLogW_ren swap_fix)
open Hashtree.Proofs.Avx2X8Align (x8Sm x8Sm_facts x8Sm_outLogW)
open Hashtree.Proofs.Avx2X8X4WAgree (x4LastSteps x8_x4_W_small x8_x4_W_last x8_x4_W_zero
  x8_x4_W1_small x8_x4_W1_last x8_x4_W1_zero)
open Hashtree.Proofs.Avx2X8ChainW (x8Steps x4Steps x4Steps_small x4Steps_last x8Steps_lt x8Steps_ge)
open Hashtree.Proofs.Avx2X8SmallW (x8StepsAll x8_small_run_at handoff agree_flags wf_env x8_chain_W_all)
open Hashtree.Proofs.Avx2X8WLoop (sIt8)
open Hashtree.Spec

namespace Hashtree.Proofs.Avx2X8ChainC

/-! ## Projections through the renamed, framed, mapped cut -/

theorem cut_tail (ρ : RegionRenaming) (M : CLog) (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (ρ.state (fr M (mapState e τ K))).tail = K.tail := rfl
theorem cut_err (ρ : RegionRenaming) (M : CLog) (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (ρ.state (fr M (mapState e τ K))).err = K.err := rfl
theorem frm_tail (M : CLog) (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (fr M (mapState e τ K)).tail = K.tail := rfl
theorem frm_err (M : CLog) (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (fr M (mapState e τ K)).err = K.err := rfl
theorem frfrm_tail (L M : CLog) (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (fr L (fr M (mapState e τ K))).tail = K.tail := rfl
theorem frfrm_err (L M : CLog) (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (fr L (fr M (mapState e τ K))).err = K.err := rfl

theorem KTE_ok (r : Nat) (hr : r = 0 ∨ r = 16) :
    (Hashtree.Proofs.Avx2X8WShift.KTE r).err = none ∧
      (Hashtree.Proofs.Avx2X8WShift.KTE r).tail = some "hashtree_sha256_avx_x4" := by
  rcases hr with rfl | rfl
  · exact ⟨Hashtree.Proofs.Avx2X8WShift.KTE_err_0, Hashtree.Proofs.Avx2X8WShift.KTE_tail_0⟩
  · exact ⟨Hashtree.Proofs.Avx2X8WShift.KTE_err_16, Hashtree.Proofs.Avx2X8WShift.KTE_tail_16⟩

theorem KTEs_ok (r : Nat) (hr : r = 0 ∨ r = 16) :
    (Hashtree.Proofs.Avx2X8WStrip.KTEs r).err = none ∧
      (Hashtree.Proofs.Avx2X8WStrip.KTEs r).tail = some "hashtree_sha256_avx_x4" := by
  rcases hr with rfl | rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, t, e, _⟩ :=
      Hashtree.Proofs.Avx2X8WStrip.stripFacts 0 Hashtree.Proofs.Avx2X8WStrip.stripOk_0
    exact ⟨e, t⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, t, e, _⟩ :=
      Hashtree.Proofs.Avx2X8WStrip.stripFacts 16 Hashtree.Proofs.Avx2X8WStrip.stripOk_16
    exact ⟨e, t⟩

/-! ## The tail facts -/

/-- **The tails of the x8 and x4 runs.**  Under the hypotheses of `x8_chain_W_all`, the x8 run
ends without error on the tail call into avx_x4, and, when `c % 8 ≠ 0`, the x4 run from the
resumed x8 state ends without error on the tail call into avx_x1. -/
theorem x8_tails (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hc : σ 2 = (c : Int)) (h1 : 1 ≤ c) (habi : σ 9 % 16 = 8) :
    let g8 : CS := run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8StepsAll c)
      (fr M (mapState env0 σ entryW))
    let g4 : CS := run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4Steps (c % 8)) (resume g8)
    g8.err = none ∧ g8.tail = some "hashtree_sha256_avx_x4" ∧
      (c % 8 ≠ 0 → g4.err = none ∧ g4.tail = some "hashtree_sha256_avx_x1") := by
  intro g8 g4
  by_cases hlt : c < 8
  · -- the small path
    have hs : x8StepsAll c = 20 := by simp only [x8StepsAll, if_pos hlt]
    have hm : c % 8 = c := Nat.mod_eq_of_lt hlt
    obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
    obtain ⟨r, e', hr, hrun⟩ := x8_small_run_at r8 hrNum hrIn hrOut hrStack hrG hrRet env0 σ mem0c
      orcC M hw8 hM (by rw [hc]; omega) (by rw [hc]; omega)
    have hf8 : g8 = (swap 4 r8).state (fr (renLog (swap 4 r8) M) (mapState e' (upd15 σ) (x8Sm r))) := by
      show run _ r8 mem0c orcC (x8StepsAll c) _ = _
      rw [hs, hrun]
    obtain ⟨_, ht8, he8, _⟩ := x8Sm_facts r hr
    refine ⟨by rw [hf8, cut_err]; exact he8, by rw [hf8, cut_tail]; exact ht8, fun _ => ?_⟩
    let L : CLog := renLog (swap 4 r8) ((mapState e' (upd15 σ) (x8Sm r)).mem ++ renLog (swap 4 r8) M)
    have hL : OutLogW σ L :=
      outLogW_ren (swap 4 r8) f2 f3 σ _ (outLogW_app σ
        (outLogW_s9 _ (upd15_9 σ).symm (x8Sm_outLogW r hr e' (upd15 σ)))
        (outLogW_ren (swap 4 r8) f2 f3 σ M hM))
    have hg8 : resume g8 = fr L { mapState e' σ entryW with
        flags := (mapState e' (upd15 σ) (x8Sm r)).flags } := by
      rw [hf8]
      exact handoff r8 hrNum hrIn hrOut hrStack hrG r hr e' σ mem0c _
    by_cases h4 : c < 4
    · -- the x4 small path
      have hg4 : g4 = run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
          (fr L { mapState e' σ entryW with flags := (mapState e' (upd15 σ) (x8Sm r)).flags }) := by
        show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume g8) = _
        rw [hg8, hm, x4Steps_small c (by omega) h4]
      let E := ecomb e' σ (view L mem0c)
      have hwv : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] E σ (view L mem0c) :=
        Hashtree.Proofs.AvxX4LoopWFrame.wfW_view _ env0 E σ mem0c L hL hw4
      have hsp := small_prefix E σ (view L mem0c) orcC hwv (envMem_ecomb E σ (view L mem0c))
        (by rw [hc]; omega) (by rw [hc]; omega)
      have hrun4 : run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8 (fr L (mapState e' σ entryW)) =
          fr L (mapState (envAbs E (run Hashtree.Kernels.X86.AvxX4.prog 4
            (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW)) σ KSm) := by
        rw [run_fr, mapState_nOnly e' E σ (fun _ => rfl) entryW
          Hashtree.Proofs.WrapperAmd64.entryW_nOnly, hsp]
      have hag := run_agree4 4 mem0c orcC 8 (fr L (mapState e' σ entryW))
        (fr L { mapState e' σ entryW with flags := (mapState e' (upd15 σ) (x8Sm r)).flags }) rfl
        (agree_flags L (mapState e' σ entryW) _)
        (by rw [hrun4]; simp only [fr, mapState, KSm_err])
      rw [hrun4] at hag
      rw [hg4]
      exact ⟨hag.err ▸ (frm_err _ _ _ _).trans KSm_err, hag.tail ▸ (frm_tail _ _ _ _).trans KSm_tail⟩
    · -- the x4 W-mode exit
      have hg4 : g4 = run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
          (fr L { mapState e' σ entryW with flags := (mapState e' (upd15 σ) (x8Sm r)).flags }) := by
        show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume g8) = _
        rw [hg8, hm, x4Steps_last c (by omega) h4]
      obtain ⟨e4, M4, hrun4, _⟩ := x4_runW_last e' σ mem0c orcC L
        (wf_env _ env0 e' σ σ rfl mem0c hw4) hL c (by omega) hlt hc
      have hrun' : run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
          (fr L (mapState e' σ entryW)) = fr M4 (mapState e4 (Hashtree.Proofs.AvxX4LoopFrame.sIt 0 (upd15 σ)) K201W) := by
        unfold x4LastSteps; exact hrun4
      have hag := run_agree4 4 mem0c orcC x4LastSteps (fr L (mapState e' σ entryW))
        (fr L { mapState e' σ entryW with flags := (mapState e' (upd15 σ) (x8Sm r)).flags }) rfl
        (agree_flags L (mapState e' σ entryW) _)
        (by rw [hrun']; simp only [fr, mapState, K201W_err])
      rw [hrun'] at hag
      rw [hg4]
      exact ⟨hag.err ▸ (frm_err _ _ _ _).trans K201W_err, hag.tail ▸ (frm_tail _ _ _ _).trans K201W_tail⟩
  have hs : x8StepsAll c = x8Steps c := by simp only [x8StepsAll, if_neg hlt]
  by_cases h16 : c < 16
  · -- the single pass
    have hn8 : x8Steps c = 16 + (Hashtree.Proofs.Avx2X8WShift.BODYLEN + 31) := x8Steps_lt c h16
    by_cases hz : c % 8 = 0
    · obtain ⟨r, e', M', hr, hrun, _⟩ := x8_x4_W1_zero env0 σ mem0c orcC M r8 hrNum hrIn hrOut
        hrStack hrG hrRet hw8 hw4 hM (by rw [hc]; omega) habi
      have hf8 : g8 = _ := (show run _ r8 mem0c orcC (x8StepsAll c) _ = _ by rw [hs, hn8, hrun])
      obtain ⟨he, ht⟩ := KTE_ok r hr
      exact ⟨by rw [hf8, cut_err]; exact he, by rw [hf8, cut_tail]; exact ht, fun h => absurd hz h⟩
    by_cases h4 : c % 8 < 4
    · obtain ⟨r, e', M', hr, hrun, _, hag⟩ := x8_x4_W1_small env0 σ mem0c orcC M r8 hrNum hrIn hrOut
        hrStack hrG hrRet hw8 hw4 hM (by rw [hc]; omega) (by rw [hc]; omega) habi
      dsimp only at hag
      have hf8 : g8 = _ := (show run _ r8 mem0c orcC (x8StepsAll c) _ = _ by rw [hs, hn8, hrun])
      obtain ⟨he, ht⟩ := KTE_ok r hr
      refine ⟨by rw [hf8, cut_err]; exact he, by rw [hf8, cut_tail]; exact ht, fun _ => ?_⟩
      have hg4 : g4 = _ := (show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume g8) = _ by
        rw [x4Steps_small (c % 8) hz h4, hf8])
      rw [hg4]
      exact ⟨hag.err ▸ (frm_err _ _ _ _).trans KSm_err, hag.tail ▸ (frm_tail _ _ _ _).trans KSm_tail⟩
    · obtain ⟨r, e', M', hr, hrun, _, e4, M4, hag, _⟩ := x8_x4_W1_last env0 σ mem0c orcC M r8 hrNum hrIn
        hrOut hrStack hrG hrRet hw8 hw4 hM (c - 8) (by omega) (by omega) (by rw [hc]; omega) habi
      have hf8 : g8 = _ := (show run _ r8 mem0c orcC (x8StepsAll c) _ = _ by rw [hs, hn8, hrun])
      obtain ⟨he, ht⟩ := KTE_ok r hr
      refine ⟨by rw [hf8, cut_err]; exact he, by rw [hf8, cut_tail]; exact ht, fun _ => ?_⟩
      have hg4 : g4 = _ := (show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume g8) = _ by
        rw [x4Steps_last (c % 8) hz h4, hf8])
      rw [hg4]
      exact ⟨hag.err ▸ (frfrm_err _ _ _ _ _).trans K201W_err, hag.tail ▸ (frfrm_tail _ _ _ _ _).trans K201W_tail⟩
  · -- two or more passes: c = 8 (j + 1) + s, j = c / 8 - 2, s = c % 8 + 8
    have hn8 := x8Steps_ge c h16
    have hcj : σ 2 = 8 * (((c / 8 - 2 : Nat) : Int) + 1) + ((c % 8 + 8 : Nat) : Int) := by
      rw [hc]; omega
    by_cases hz : c % 8 = 0
    · obtain ⟨r, e', M', hr, hrun, _⟩ := x8_x4_W_zero (c / 8 - 2) env0 σ mem0c orcC M r8 hrNum
        hrIn hrOut hrStack hrG hrRet hw8 hw4 hM (by rw [hc]; omega) habi
      have hf8 : g8 = _ := (show run _ r8 mem0c orcC (x8StepsAll c) _ = _ by rw [hs, hn8, hrun])
      obtain ⟨he, ht⟩ := KTEs_ok r hr
      exact ⟨by rw [hf8, cut_err]; exact he, by rw [hf8, cut_tail]; exact ht, fun h => absurd hz h⟩
    by_cases h4 : c % 8 < 4
    · obtain ⟨r, e', M', hr, hrun, _, hag⟩ := x8_x4_W_small (c / 8 - 2) (c % 8 + 8) env0 σ mem0c orcC M
        r8 hrNum hrIn hrOut hrStack hrG hrRet hw8 hw4 hM (by omega) (by omega) hcj habi
      dsimp only at hag
      have hf8 : g8 = _ := (show run _ r8 mem0c orcC (x8StepsAll c) _ = _ by rw [hs, hn8, hrun])
      obtain ⟨he, ht⟩ := KTEs_ok r hr
      refine ⟨by rw [hf8, cut_err]; exact he, by rw [hf8, cut_tail]; exact ht, fun _ => ?_⟩
      have hg4 : g4 = _ := (show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume g8) = _ by
        rw [x4Steps_small (c % 8) hz h4, hf8])
      rw [hg4]
      exact ⟨hag.err ▸ (frm_err _ _ _ _).trans KSm_err, hag.tail ▸ (frm_tail _ _ _ _).trans KSm_tail⟩
    · obtain ⟨r, e', M', hr, hrun, _, e4, M4, hag, _⟩ := x8_x4_W_last (c / 8 - 2) (c % 8 + 8) env0 σ mem0c
        orcC M r8 hrNum hrIn hrOut hrStack hrG hrRet hw8 hw4 hM (by omega) (by omega) hcj habi
      have hf8 : g8 = _ := (show run _ r8 mem0c orcC (x8StepsAll c) _ = _ by rw [hs, hn8, hrun])
      obtain ⟨he, ht⟩ := KTEs_ok r hr
      refine ⟨by rw [hf8, cut_err]; exact he, by rw [hf8, cut_tail]; exact ht, fun _ => ?_⟩
      have hg4 : g4 = _ := (show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume g8) = _ by
        rw [x4Steps_last (c % 8) hz h4, hf8])
      rw [hg4]
      exact ⟨hag.err ▸ (frfrm_err _ _ _ _ _).trans K201W_err, hag.tail ▸ (frfrm_tail _ _ _ _ _).trans K201W_tail⟩

/-! ## The chain form -/

/-- The run-level post-condition of a returning link. -/
def Ret (f : CS) : Prop := f.halted = true ∧ f.err = none ∧ f.tail = none

/-- The x8 link with its table at `r8`. -/
def link8 (r8 : Region) : Link :=
  { name := "hashtree_sha256_avx2_x8", prog := Hashtree.Kernels.X86.Avx2X8.prog, ro := r8, steps := x8StepsAll }

/-- The x4 link (table at region 4) for the `c % 8` blocks the x8 link leaves. -/
def link4 : Link :=
  { name := "hashtree_sha256_avx_x4", prog := Hashtree.Kernels.X86.AvxX4.prog, ro := 4,
    steps := fun c => x4Steps (c % 8) }

/-- The x1 link (table at `r1`) for the `c % 4` blocks the x4 link leaves. -/
def link1 (r1 : Region) : Link :=
  { name := "hashtree_sha256_avx_x1", prog := Hashtree.Kernels.X86.AvxX1.prog, ro := r1,
    steps := fun c => steps (c % 4) }

/-- The three links with their exact hand-over states as pre-conditions (the x1 link is
entered only when `c % 8 ≠ 0`). -/
def x8Specs (c : Nat) (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region) : List Spec :=
  let s0 : CS := fr M (mapState env0 σ entryW)
  let g8 : CS := step mem0c orcC c (link8 r8) s0
  let g4 : CS := step mem0c orcC c link4 (resume g8)
  [ ⟨link8 r8, (· = s0), Ret⟩, ⟨link4, (· = resume g8), Ret⟩, ⟨link1 r1, (fun s => c % 8 ≠ 0 ∧ s = resume g4), Ret⟩ ]

/-- **The x8 chain as `KSpecC`**: every link meets its obligation. -/
theorem x8KSpecC (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    KSpecC mem0c orcC c (x8Specs c env0 σ mem0c orcC M r8 r1) := by
  have T := x8_tails c env0 σ mem0c orcC M r8 hrNum hrIn hrOut hrStack hrG hrRet hw8 hw4 hM hc h1 habi
  have H := x8_chain_W_all c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack hrG hrRet
    h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc h1 habi hin
  dsimp only at T H
  obtain ⟨t8e, t8t, t4⟩ := T
  obtain ⟨H0, H1⟩ := H
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    subst hs
    exact ⟨t8e, Or.inr ⟨t8t, rfl⟩⟩
  · intro s hs
    subst hs
    by_cases hz : c % 8 = 0
    · obtain ⟨hh, he, ht⟩ := H0 hz
      exact ⟨he, Or.inl ⟨ht, hh, he, ht⟩⟩
    · obtain ⟨he, ht⟩ := t4 hz
      exact ⟨he, Or.inr ⟨ht, hz, rfl⟩⟩
  · intro s ⟨hz, hs⟩
    subst hs
    obtain ⟨hh, he, ht⟩ := H1 hz
    exact ⟨he, ht, hh, he, ht⟩

/-- **The wrapper's chain call for the x8 chain**: `callChain` from the wrapper call state behind
a W-mode log returns normally (no error, no tail, unhalted at pc 0) after a link ended halted
without error or tail. -/
theorem x8_callChain (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    let fin : CS := callChain mem0c orcC c (x8Specs c env0 σ mem0c orcC M r8 r1)
      (fr M (mapState env0 σ entryW))
    fin.err = none ∧ fin.tail = none ∧ fin.halted = false ∧ fin.pc = 0 := by
  have hok := x8KSpecC c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack hrG hrRet
    h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc h1 habi hin
  have hpc : ({ fr M (mapState env0 σ entryW) with pc := 0 } : CS) = fr M (mapState env0 σ entryW) := by
    simp [fr, mapState, entryW]
  have h := chain_sound mem0c orcC c (x8Specs c env0 σ mem0c orcC M r8 r1)
    { fr M (mapState env0 σ entryW) with pc := 0 } hok (by rw [hpc]; rfl)
  dsimp only at h
  refine ⟨?_, ?_, rfl, rfl⟩
  · show (chainRun mem0c orcC c _ { fr M (mapState env0 σ entryW) with pc := 0 }).err = none
    exact h.1
  · rfl

end Hashtree.Proofs.Avx2X8ChainC
