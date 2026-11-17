import Hashtree.Proofs.Avx2X8ChainOutAll

/-!
# avx2_x8 -> avx_x4 -> avx_x1: the restored registers, every count, and count 0

The run-level chain theorems (`Avx2X8ChainW`, `Avx2X8SmallW`) dropped the register facts of
their per-case theorems.  This module carries them to the end of the chain:

* `x8_chain_W_regs` (`c ≥ 8`, six cases) and `x8_chain_small_regs` (`0 < c < 8`): the state the
  chain returns in has the callee-saved registers and `rsp` of the wrapper call state
  (`ShaniW.RegsOk env0 σ`).  The per-case facts are stated at the shifted cut symbols
  (`sigmaOf tau8 …`, `sigmaOf tau (tau48 …)`); every shift fixes the symbols 5..12
  (`regsOk_congr`).  On the count-0 x4 returns the register facts come from `link_zero` across
  the `{rax, rcx, flags}` agreement; on the x1 returns from `x1cut_framed`/`x1_ksm_framed`.
* `x8_zero_at` (`c = 0`): the x8 kernel returns after `nop; cmp rdx,0; jne; ret` (one slice,
  table region irrelevant, moved to `r8` by the swap), no write, registers restored.
* `x8SpecsR`, `x8KSpecC_full`: the chain form with run-level post, all `c` outputs, the
  footprint and the registers in the returning links' post-condition (`RetR`), `c ≥ 1`;
  `x8Specs0`, `x8KSpecC_zero`: the same post for `c = 0`.

Hypotheses: R2c's `TurnOut8`, `TurnOut8Last` (proved on research/formal-r2c-x16out) and
`TurnOut4Last` (statement `Avx2X8OutLink`, for R2c), only through the output clause.
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
open Hashtree.Proofs.AvxX4X1WAgree (cutLog wfAt_cut swap_view_in outLogW_congr sigmaOf_s9
  sigmaOf_hi x1cut_framed)
open Hashtree.Proofs.AvxX1W (steps InRange regsOk_state state_entryW)
open Hashtree.Proofs.ShaniW (OutOk RegsOk)
open Hashtree.Proofs.AvxX1Agree (Dsx hsound not_mem_Dsx regsOk_agree gpr_get_of_getG)
open Hashtree.Proofs.Avx2X8WAt (renLog swap_fix wf_swap outLogW_ren)
open Hashtree.Proofs.Avx2X8Align (x8Sm x8Sm_outLogW)
open Hashtree.Proofs.Avx2X8WShift (tau8 BODYLEN)
open Hashtree.Proofs.Avx2X8WLoop (sIt8 TURNLEN tau8_hi sIt8_hi tau8_in sIt8_in)
open Hashtree.Proofs.Avx2X8X4WAgree (x4LastSteps K201W_pc mapState_mem_eq fr_nil x8_x4_W_zero
  x8_x4_W1_zero)
open Hashtree.Proofs.Avx2X8X1WAgree (agreeOn_resume x1_ksm_framed tau48 tau41 x8_x4_x1_W_last
  x8_x4_x1_W_small x8_x4_x1_W1_last x8_x4_x1_W1_small)
open Hashtree.Proofs.Avx2X8ChainW (x8Steps x4Steps x4Steps_zero x4Steps_small x4Steps_last
  x8Steps_lt x8Steps_ge upd15_0 tau48_0 tau41_0 tau48_2 tau41_2)
open Hashtree.Proofs.Avx2X8SmallW (x8StepsAll x8_small_run_at handoff agree_flags wf_env)
open Hashtree.Proofs.Avx2X8ChainC (link8 link4 link1 Ret x8_tails)
open Hashtree.Proofs.Avx2X8OutLink
open Hashtree.Proofs.Avx2X8ChainOut (FootC)
open Hashtree.Proofs.Avx2X8ChainOutAll (RetO x8SpecsO x8_chain_out_all)
open Hashtree.Spec

namespace Hashtree.Proofs.Avx2X8ChainRegs

/-! ## Symbols -/

/-- `RegsOk` reads only the symbols 5..12 (and not the environment). -/
theorem regsOk_congr {env env' : Key → W32} {σ σ' : Nat → Int} {s : CS}
    (h : ∀ k, 5 ≤ k → k ≤ 12 → σ' k = σ k) (H : RegsOk env σ' s) : RegsOk env' σ s := by
  obtain ⟨h3, h5, h12, h14, h13, h15, h4⟩ := H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h3, h 5 (by omega) (by omega)]
  · rw [h5, h 6 (by omega) (by omega)]
  · rw [h12, h 7 (by omega) (by omega)]
  · rw [h14, h 8 (by omega) (by omega)]
  · rw [h13, h 11 (by omega) (by omega)]
  · rw [h15, h 12 (by omega) (by omega)]
  · rw [h4, h 9 (by omega) (by omega)]

theorem upd15_lo (σ : Nat → Int) (k : Nat) (h : k ≤ 12) : upd15 σ k = σ k := by
  unfold upd15
  rw [if_neg (by omega)]

theorem mid_u (σ : Nat → Int) : ∀ k, 5 ≤ k → k ≤ 12 → sigmaOf tau8 (upd15 σ) k = σ k := by
  intro k h5 h12
  rw [tau8_hi k (by omega), upd15_lo σ k h12]

theorem mid_s8 (j : Nat) (σ : Nat → Int) :
    ∀ k, 5 ≤ k → k ≤ 12 → sigmaOf tau8 (sIt8 j (upd15 σ)) k = σ k := by
  intro k h5 h12
  rw [tau8_hi k (by omega), sIt8_hi k (by omega), upd15_lo σ k h12]

theorem mid_48 (j : Nat) (σ : Nat → Int) :
    ∀ k, 5 ≤ k → k ≤ 12 → sigmaOf tau (tau48 j σ) k = σ k := by
  intro k h5 h12
  rw [sigmaOf_hi k h5]
  show upd15 (sigmaOf tau8 (sIt8 (j + 1) (upd15 σ))) k = σ k
  rw [upd15_lo _ k h12, tau8_hi k (by omega), sIt8_hi k (by omega), upd15_lo σ k h12]

theorem mid_41 (σ : Nat → Int) : ∀ k, 5 ≤ k → k ≤ 12 → sigmaOf tau (tau41 σ) k = σ k := by
  intro k h5 h12
  rw [sigmaOf_hi k h5]
  show upd15 (sigmaOf tau8 (upd15 σ)) k = σ k
  rw [upd15_lo _ k h12, tau8_hi k (by omega), upd15_lo σ k h12]

theorem mid_sm4 (σ : Nat → Int) : ∀ k, 5 ≤ k → k ≤ 12 → sigmaOf tau (sIt 0 (upd15 σ)) k = σ k := by
  intro k h5 h12
  rw [sigmaOf_hi k h5]
  show upd15 σ k = σ k
  exact upd15_lo σ k h12

theorem not_D3 : ∀ i, i ∈ [3, 4, 5, 12, 13, 14, 15] → i ∉ [0, 1, 16] := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
  omega

/-- The register facts of an x4 count-0 return (`link_zero`'s `getG` form) as `RegsOk`. -/
theorem regsOk_of_getG (env : Key → W32) (σ : Nat → Int) (L : CLog) (s : CS)
    (q4 : s.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩) (q3 : s.getG 3 = .ptr ⟨rStack, σ 5⟩)
    (q5 : s.getG 5 = .ptr ⟨rStack, σ 6⟩) (q12 : s.getG 12 = .ptr ⟨rStack, σ 7⟩)
    (q14 : s.getG 14 = .ptr ⟨rG, σ 8⟩) (q13 : s.getG 13 = .ptr ⟨rNum, σ 11⟩)
    (q15 : s.getG 15 = .ptr ⟨rNum, σ 12⟩) : RegsOk env σ (fr L s) :=
  ⟨gpr_get_of_getG q3 (by intro hv; cases hv), gpr_get_of_getG q5 (by intro hv; cases hv),
   gpr_get_of_getG q12 (by intro hv; cases hv), gpr_get_of_getG q14 (by intro hv; cases hv),
   gpr_get_of_getG q13 (by intro hv; cases hv), gpr_get_of_getG q15 (by intro hv; cases hv),
   gpr_get_of_getG q4 (by intro hv; cases hv)⟩

/-! ## `c ≥ 8` -/

/-- **The restored registers at the end of the chain, every count `c ≥ 8`** (the six cases of
`Avx2X8ChainW.x8_chain_W`). -/
theorem x8_chain_W_regs (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hc : σ 2 = (c : Int)) (h8 : 8 ≤ c) (habi : σ 9 % 16 = 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let g8 : CS := run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8Steps c)
      (fr M (mapState env0 σ entryW))
    let g4 : CS := run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4Steps (c % 8)) (resume g8)
    let g1 : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 4)) (resume g4)
    (c % 8 = 0 → RegsOk env0 σ g4) ∧ (c % 8 ≠ 0 → RegsOk env0 σ g1) := by
  intro g8 g4 g1
  let inp1 : Nat → Byte := fun o => inp (64 * (c - c % 4) + o)
  by_cases hlt : c < 16
  · have hn8 : x8Steps c = 16 + (BODYLEN + 31) := x8Steps_lt c hlt
    by_cases hz : c % 8 = 0
    · obtain ⟨r, e', M', _, hrun, _, H⟩ := x8_x4_W1_zero env0 σ mem0c orcC M r8 hrNum hrIn hrOut
        hrStack hrG hrRet hw8 hw4 hM (by rw [hc]; omega) habi
      dsimp only at H
      obtain ⟨hag, _, _, _, _, q4, q3, q5, q12, q14, q13, q15⟩ := H
      refine ⟨fun _ => ?_, fun h => absurd hz h⟩
      have hg4 : g4 = run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 4
          (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (Hashtree.Proofs.Avx2X8WShift.KTE r))))) := by
        show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume (run _ r8 mem0c orcC (x8Steps c) _)) = _
        rw [hz, x4Steps_zero, hn8, hrun]
      rw [hg4]
      exact regsOk_congr (mid_u σ) (regsOk_agree hag not_D3
        (regsOk_of_getG env0 _ _ _ q4 q3 q5 q12 q14 q13 q15))
    · refine ⟨fun h => absurd h hz, fun _ => ?_⟩
      by_cases h4 : c % 8 < 4
      · have hs : c - 8 = c % 4 := by omega
        obtain ⟨r, e', M', _, hrun, H⟩ := x8_x4_x1_W1_small (c - 8) inp1 env0 σ mem0c orcC M r8 r1
          hrNum hrIn hrOut hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM
          (by omega) (by omega) (by rw [hc]; omega) habi
          (fun o => by
            have h := hin (64 * (c - c % 4) + o)
            rw [show sigmaOf tau8 (upd15 σ) 0 + (o : Int) = σ 0 + ((64 * (c - c % 4) + o : Nat) : Int)
              from by rw [tau8_in, upd15_0]; omega]
            exact h)
        dsimp only at H
        obtain ⟨_, _, _, _, _, _, hR⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 8))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
              (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (Hashtree.Proofs.Avx2X8WShift.KTE r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_small (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1]
        exact regsOk_congr (mid_u σ) hR
      · have hs : c - 8 - 4 = c % 4 := by omega
        obtain ⟨r, e', M', _, hrun, e4, M4, H⟩ := x8_x4_x1_W1_last (c - 8) inp1 env0 σ mem0c orcC M
          r8 r1 hrNum hrIn hrOut hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1
          hM (by omega) (by omega) (by rw [hc]; omega) habi
          (fun o => by
            have h := hin (64 * (c - c % 4) + o)
            rw [show tau41 σ 0 + 256 + (o : Int) = σ 0 + ((64 * (c - c % 4) + o : Nat) : Int)
              from by rw [tau41_0]; omega]
            exact h)
          (by rw [tau_count, tau41_2, hc]; omega)
        dsimp only at H
        obtain ⟨_, _, _, _, _, _, hR, _⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 8 - 4))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
              (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (Hashtree.Proofs.Avx2X8WShift.KTE r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_last (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1]
        exact regsOk_congr (mid_41 σ) hR
  · have hn8 := x8Steps_ge c hlt
    have hcj : σ 2 = 8 * (((c / 8 - 2 : Nat) : Int) + 1) + ((c % 8 + 8 : Nat) : Int) := by
      rw [hc]; omega
    by_cases hz : c % 8 = 0
    · obtain ⟨r, e', M', _, hrun, _, H⟩ := x8_x4_W_zero (c / 8 - 2) env0 σ mem0c orcC M r8 hrNum
        hrIn hrOut hrStack hrG hrRet hw8 hw4 hM (by rw [hc]; omega) habi
      dsimp only at H
      obtain ⟨hag, _, _, _, _, q4, q3, q5, q12, q14, q13, q15⟩ := H
      refine ⟨fun _ => ?_, fun h => absurd hz h⟩
      have hg4 : g4 = run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 4
          (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (c / 8 - 2 + 1) (upd15 σ))
            (Hashtree.Proofs.Avx2X8WStrip.KTEs r))))) := by
        show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume (run _ r8 mem0c orcC (x8Steps c) _)) = _
        rw [hz, x4Steps_zero, hn8, hrun]
      rw [hg4]
      exact regsOk_congr (mid_s8 (c / 8 - 2 + 1) σ) (regsOk_agree hag not_D3
        (regsOk_of_getG env0 _ _ _ q4 q3 q5 q12 q14 q13 q15))
    · refine ⟨fun h => absurd h hz, fun _ => ?_⟩
      by_cases h4 : c % 8 < 4
      · have hs : c % 8 + 8 - 8 = c % 4 := by omega
        obtain ⟨r, e', M', _, hrun, H⟩ := x8_x4_x1_W_small (c / 8 - 2) (c % 8 + 8) inp1 env0 σ
          mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G
          h1Ret hw8 hw4 hw1 hM (by omega) (by omega) hcj habi
          (fun o => by
            have h := hin (64 * (c - c % 4) + o)
            rw [show sigmaOf tau8 (sIt8 (c / 8 - 2 + 1) (upd15 σ)) 0 + (o : Int) =
                σ 0 + ((64 * (c - c % 4) + o : Nat) : Int)
              from by rw [tau8_in, sIt8_in, upd15_0]; omega]
            exact h)
        dsimp only at H
        obtain ⟨_, _, _, _, _, _, hR⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 8 + 8 - 8))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
              (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (c / 8 - 2 + 1) (upd15 σ))
                (Hashtree.Proofs.Avx2X8WStrip.KTEs r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_small (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1]
        exact regsOk_congr (mid_s8 (c / 8 - 2 + 1) σ) hR
      · have hs : c % 8 + 8 - 12 = c % 4 := by omega
        obtain ⟨r, e', M', _, hrun, e4, M4, H⟩ := x8_x4_x1_W_last (c / 8 - 2) (c % 8 + 8) inp1 env0 σ
          mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G
          h1Ret hw8 hw4 hw1 hM (by omega) (by omega) hcj habi
          (fun o => by
            have h := hin (64 * (c - c % 4) + o)
            rw [show tau48 (c / 8 - 2) σ 0 + 256 + (o : Int) =
                σ 0 + ((64 * (c - c % 4) + o : Nat) : Int)
              from by rw [tau48_0]; omega]
            exact h)
          (by rw [tau_count, tau48_2, hc]; omega)
        dsimp only at H
        obtain ⟨_, _, _, _, _, _, hR, _⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 8 + 8 - 12))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
              (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (c / 8 - 2 + 1) (upd15 σ))
                (Hashtree.Proofs.Avx2X8WStrip.KTEs r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_last (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1]
        exact regsOk_congr (mid_48 (c / 8 - 2) σ) hR

/-! ## `0 < c < 8` -/

/-- **`0 < c < 4`**: the x4 small path, then x1, with the registers. -/
theorem small_x4_x1_regs (c : Nat) (inp : Nat → Byte) (e' env0 : Key → W32) (σ : Nat → Int)
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
    RegsOk env0 σ g := by
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
  exact regsOk_congr (fun _ _ _ => rfl) hX.2.2.2.2.2.2

/-- **`4 ≤ c < 8`**: the x4 W-mode exit, then x1, with the registers. -/
theorem last_x4_x1_regs (c : Nat) (inp : Nat → Byte) (e' env0 : Key → W32) (σ : Nat → Int)
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
    RegsOk env0 σ g := by
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
  obtain ⟨hrunX, hhalt, herr, htail, _, _, hRegs⟩ := hX
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
  exact regsOk_congr (env := env0) (mid_sm4 σ)
    (regsOk_agree (env0 := env0) hA (fun i hi => not_mem_Dsx i _ hi) hRegs)

/-- **The restored registers for `0 < c < 8`.** -/
theorem x8_chain_small_regs (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    RegsOk env0 σ g1 := by
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
    exact small_x4_x1_regs c inp e' env0 σ mem0c orcC L r1 _ h1Num h1In h1Out h1Stack h1G h1Ret
      hw4 hw1 hL hc h0 h4 hin
  · have hc4 : c % 4 = c - 4 := by omega
    have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 4))
        (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
          (fr L { mapState e' σ entryW with flags := (mapState e' (upd15 σ) (x8Sm r)).flags }))) := by
      show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps c) (resume g8)))
        = _
      rw [hg8, x4Steps_last c (by omega) h4, hc4]
    rw [hg1]
    exact last_x4_x1_regs c (fun o => inp (256 + o)) e' env0 σ mem0c orcC L r1 _ h1Num h1In h1Out
      h1Stack h1G h1Ret hw4 hw1 hL hc (by omega) h8
      (fun o => by
        have h := hin (256 + o)
        rw [show σ 0 + 256 + (o : Int) = σ 0 + ((256 + o : Nat) : Int) from by omega]
        exact h)

/-! ## Every count `c ≥ 1` -/

/-- **The restored registers at the end of the x8 chain, every count `c ≥ 1`.** -/
theorem x8_chain_regs_all (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    (c % 8 = 0 → RegsOk env0 σ g4) ∧ (c % 8 ≠ 0 → RegsOk env0 σ g1) := by
  intro g8 g4 g1
  by_cases hlt : c < 8
  · have hs : x8StepsAll c = 20 := by simp only [x8StepsAll, if_pos hlt]
    have hm : c % 8 = c := Nat.mod_eq_of_lt hlt
    refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
    have H := x8_chain_small_regs c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack hrG
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
    have H := x8_chain_W_regs c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut hrStack hrG hrRet
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

/-! ## Count 0 -/

def orc0 : Nat → Bool := fun _ => false

/-- The x8 cut after the count-0 path (`nop; cmp rdx,0; jne; ret`). -/
def K0 : State E Lin :=
  abstract (run Hashtree.Kernels.X86.Avx2X8.prog 4 (mem0sW 4 Hashtree.Kernels.X86.Avx2X8.rodata [])
    orc0 4 entryW)

theorem slice0 : sliceCheck Hashtree.Kernels.X86.Avx2X8.prog 4
    (mem0sW 4 Hashtree.Kernels.X86.Avx2X8.rodata []) orc0 4 entryW K0 [] = true := by
  decide +kernel
theorem K0_halted : K0.halted = true := by decide +kernel
theorem K0_tail : K0.tail = none := by decide +kernel
theorem K0_mem : K0.mem = [] := by decide +kernel
theorem K0_err : K0.err = none := by decide +kernel
theorem K0_g4 : K0.gpr[4]? = some (.ptr ⟨rStack, sAt 8⟩) := by decide +kernel
theorem K0_g3 : K0.gpr[3]? = some (.ptr ⟨rStack, Lin.sym 5⟩) := by decide +kernel
theorem K0_g5 : K0.gpr[5]? = some (.ptr ⟨rStack, Lin.sym 6⟩) := by decide +kernel
theorem K0_g12 : K0.gpr[12]? = some (.ptr ⟨rStack, Lin.sym 7⟩) := by decide +kernel
theorem K0_g14 : K0.gpr[14]? = some (.ptr ⟨rG, Lin.sym 8⟩) := by decide +kernel
theorem K0_g13 : K0.gpr[13]? = some (.ptr ⟨rNum, Lin.sym 11⟩) := by decide +kernel
theorem K0_g15 : K0.gpr[15]? = some (.ptr ⟨rNum, Lin.sym 12⟩) := by decide +kernel
theorem K0_assume : K0.assume =
    [((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), false)] := by decide +kernel

theorem K0_assumeOk (σ : Nat → Int) (hc : σ 2 = 0) : AssumeOk σ K0 := by
  unfold AssumeOk
  intro p hp
  rw [K0_assume] at hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  simp [mapCond, Cond.decideC, Lin.eval, dotC, hc, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]

theorem K0_regs (e : Key → W32) (env0 : Key → W32) (σ : Nat → Int) :
    RegsOk env0 σ (mapState e σ K0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mapState, List.getElem?_map, K0_g3, Option.map_some, mapVal, mapAddr, Lin.eval_sym]
  · simp only [mapState, List.getElem?_map, K0_g5, Option.map_some, mapVal, mapAddr, Lin.eval_sym]
  · simp only [mapState, List.getElem?_map, K0_g12, Option.map_some, mapVal, mapAddr, Lin.eval_sym]
  · simp only [mapState, List.getElem?_map, K0_g14, Option.map_some, mapVal, mapAddr, Lin.eval_sym]
  · simp only [mapState, List.getElem?_map, K0_g13, Option.map_some, mapVal, mapAddr, Lin.eval_sym]
  · simp only [mapState, List.getElem?_map, K0_g15, Option.map_some, mapVal, mapAddr, Lin.eval_sym]
  · simp only [mapState, List.getElem?_map, K0_g4, Option.map_some, mapVal, mapAddr,
      Hashtree.Proofs.WrapperAmd64.sAt_eval]
    congr 3
    omega

/-- **Count 0, table at `r8`**: the x8 kernel returns after four instructions (the remaining
fuel of the chain's step count is idle), with no write and the registers restored. -/
theorem x8_zero_at (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut)
    (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c) (hc : σ 2 = 0) :
    let f : CS := run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC 20 (mapState env0 σ entryW)
    f.halted = true ∧ f.err = none ∧ f.tail = none ∧ f.mem = [] ∧ RegsOk env0 σ f := by
  intro f
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  have hw' := wf_swap r8 hrIn hrStack hrRet env0 σ mem0c hw8
  let E := ecomb env0 σ ((swap 4 r8).mem mem0c)
  have hwE : WfMemW Hashtree.Kernels.X86.Avx2X8.rodata [] E σ ((swap 4 r8).mem mem0c) :=
    wf_env _ env0 E σ σ rfl _ hw'
  have h0 := mem0RelW_of_wf Hashtree.Kernels.X86.Avx2X8.rodata [] E σ _ hwE (envMem_ecomb _ _ _)
  have hPr := (slice_sound E σ (mem0sW 4 Hashtree.Kernels.X86.Avx2X8.rodata [])
    ((swap 4 r8).mem mem0c) h0 Hashtree.Kernels.X86.Avx2X8.prog 4 orc0 orcC 4 entryW K0 [] slice0
    Hashtree.Proofs.AvxX4Small.entryW_err (K0_assumeOk σ hc)).1
  generalize hE' : envAbs E (run Hashtree.Kernels.X86.Avx2X8.prog 4
    (mem0sW 4 Hashtree.Kernels.X86.Avx2X8.rodata []) orc0 4 entryW) = E' at hPr
  have hrun : f = (swap 4 r8).state (mapState E' σ K0) := by
    show run _ r8 mem0c orcC 20 (mapState env0 σ entryW) = _
    rw [← state_entryW (swap 4 r8) f0 f1 f2 f3 f6 env0 σ, run_swap_chain r8 hrNum hrRet,
      mapState_nOnly env0 E σ (fun _ => rfl) entryW Hashtree.Proofs.WrapperAmd64.entryW_nOnly,
      show (20 : Nat) = 4 + 16 from rfl, run_add, hPr,
      run_halted _ _ _ _ 16 _ (by simp only [mapState, K0_halted])]
  rw [hrun]
  refine ⟨?_, ?_, ?_, ?_, regsOk_state (swap 4 r8) f3 f6 f0 env0 σ _ (K0_regs E' env0 σ)⟩
  · simp only [RegionRenaming.state_halted, mapState, K0_halted]
  · simp only [RegionRenaming.state_err, mapState, K0_err]
  · simp only [RegionRenaming.state_tail, mapState, K0_tail]
  · simp only [RegionRenaming.state_mem, mapState, K0_mem, List.map_nil]

/-! ## The chain form -/

/-- The returning links' full post: run-level, all `c` outputs, the footprint, the registers. -/
def RetR (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int) (c : Nat) (M : CLog) (f : CS) :
    Prop :=
  RetO inp σ c M f ∧ RegsOk env0 σ f

/-- `x8SpecsO` with the registers in the returning links' post-condition. -/
def x8SpecsR (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region) : List Spec :=
  let s0 : CS := fr M (mapState env0 σ entryW)
  let g8 : CS := step mem0c orcC c (link8 r8) s0
  let g4 : CS := step mem0c orcC c link4 (resume g8)
  [ ⟨link8 r8, (· = s0), RetR inp env0 σ c M⟩, ⟨link4, (· = resume g8), RetR inp env0 σ c M⟩,
    ⟨link1 r1, (fun s => c % 8 ≠ 0 ∧ s = resume g4), RetR inp env0 σ c M⟩ ]

/-- **The x8 chain as `KSpecC`, with outputs, footprint and registers, `c ≥ 1`.** -/
theorem x8KSpecC_full (hT8 : TurnOut8) (hT8L : TurnOut8Last) (hT4L : TurnOut4Last)
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
    KSpecC mem0c orcC c (x8SpecsR c inp env0 σ mem0c orcC M r8 r1) := by
  have T := x8_tails c env0 σ mem0c orcC M r8 hrNum hrIn hrOut hrStack hrG hrRet hw8 hw4 hM hc h1 habi
  have H := Hashtree.Proofs.Avx2X8SmallW.x8_chain_W_all c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn
    hrOut hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc h1 habi hin
  have O := x8_chain_out_all hT8 hT8L hT4L c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut
    hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc h1 habi hin
  have R := x8_chain_regs_all c inp env0 σ mem0c orcC M r8 r1 hrNum hrIn hrOut
    hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM hc h1 habi hin
  dsimp only at T H O R
  obtain ⟨t8e, t8t, t4⟩ := T
  obtain ⟨H0, H1⟩ := H
  obtain ⟨O0, O1⟩ := O
  obtain ⟨R0, R1⟩ := R
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    subst hs
    exact ⟨t8e, Or.inr ⟨t8t, rfl⟩⟩
  · intro s hs
    subst hs
    by_cases hz : c % 8 = 0
    · obtain ⟨hh, he, ht⟩ := H0 hz
      exact ⟨he, Or.inl ⟨ht, ⟨⟨hh, he, ht⟩, O0 hz⟩, R0 hz⟩⟩
    · obtain ⟨he, ht⟩ := t4 hz
      exact ⟨he, Or.inr ⟨ht, hz, rfl⟩⟩
  · intro s ⟨hz, hs⟩
    subst hs
    obtain ⟨hh, he, ht⟩ := H1 hz
    exact ⟨he, ht, ⟨⟨hh, he, ht⟩, O1 hz⟩, R1 hz⟩

/-- The count-0 chain: the x8 link returns at once; the other links are never entered. -/
def x8Specs0 (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int) (r8 r1 : Region) : List Spec :=
  [ ⟨link8 r8, (· = mapState env0 σ entryW), RetR inp env0 σ 0 []⟩,
    ⟨link4, (fun _ => False), RetR inp env0 σ 0 []⟩,
    ⟨link1 r1, (fun _ => False), RetR inp env0 σ 0 []⟩ ]

theorem x8StepsAll_zero : x8StepsAll 0 = 20 := by simp only [x8StepsAll]; rfl

/-- **The x8 chain as `KSpecC` at count 0.** -/
theorem x8KSpecC_zero (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r8 r1 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c) (hc : σ 2 = 0) :
    KSpecC mem0c orcC 0 (x8Specs0 inp env0 σ r8 r1) := by
  have Z := x8_zero_at r8 hrNum hrIn hrOut hrStack hrG hrRet env0 σ mem0c orcC hw8 hc
  dsimp only at Z
  obtain ⟨hh, he, ht, hm, hR⟩ := Z
  refine ⟨?_, fun _ h => h.elim, fun _ h => h.elim⟩
  intro s hs
  subst hs
  have hstep : step mem0c orcC 0 (link8 r8) (mapState env0 σ entryW) =
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC 20 (mapState env0 σ entryW) := by
    show run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (x8StepsAll 0) _ = _
    rw [x8StepsAll_zero]
  change (step mem0c orcC 0 (link8 r8) (mapState env0 σ entryW)).err = none ∧
    (((step mem0c orcC 0 (link8 r8) (mapState env0 σ entryW)).tail = none ∧
      RetR inp env0 σ 0 [] (step mem0c orcC 0 (link8 r8) (mapState env0 σ entryW))) ∨ _)
  rw [hstep]
  refine ⟨he, Or.inl ⟨ht, ⟨⟨hh, he, ht⟩, fun n i b hn => absurd hn (Nat.not_lt_zero n), ?_⟩, hR⟩⟩
  intro p hp
  rw [hm] at hp
  cases hp

end Hashtree.Proofs.Avx2X8ChainRegs
