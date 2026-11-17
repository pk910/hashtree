import Hashtree.Proofs.Avx2X8X1WAgree

/-!
# avx2_x8 -> avx_x4 -> avx_x1 at the W-mode exit cuts, every count `c ≥ 8`

The case split over the count of the six x8 -> x4 (-> x1) theorems of `Avx2X8X4WAgree` and
`Avx2X8X1WAgree`, as one statement: from the wrapper call state behind a W-mode log, the x8
run (table at `r8`) for `x8Steps c` steps, the x4 run (table at region 4) for
`x4Steps (c % 8)` steps from the resumed x8 state, and, when `c % 8 ≠ 0`, the x1 run (table at
`r1`) for `steps (c % 4)` steps from the resumed x4 state end halted, without error and without
a further tail.  The x1 run's own post (`InRange`, `OutOk` of the last `c % 4` blocks against the
caller's input `inp`) is the per-case theorems'; here it is restated against the input bytes
at block `c - c % 4` of the caller's input.

* `c ≥ 16`: `c = 8 (j + 1) + s` with `j = c / 8 - 2`, `s = c % 8 + 8` (`x8_x4_W_zero`,
  `x8_x4_x1_W_small`, `x8_x4_x1_W_last`);
* `8 ≤ c < 16`: the single pass (`x8_x4_W1_zero`, `x8_x4_x1_W1_small`, `x8_x4_x1_W1_last`).
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.X86Chain (CS resume)
open Hashtree.Proofs.AvxX4W (upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW)
open Hashtree.Proofs.AvxX4LoopFrame (sIt tau_count)
open Hashtree.Proofs.AvxX4LoopTurn (tau)
open Hashtree.Proofs.AvxX4Exit (sigmaOf_tau0)
open Hashtree.Proofs.AvxX1W (steps InRange)
open Hashtree.Proofs.ShaniW (OutOk)
open Hashtree.Proofs.Avx2X8WShift (tau8 BODYLEN)
open Hashtree.Proofs.Avx2X8WLoop (sIt8 TURNLEN tau8_count tau8_in sIt8_count sIt8_in)
open Hashtree.Proofs.Avx2X8X4WAgree (x8_x4_W_zero x8_x4_W1_zero x4LastSteps)
open Hashtree.Proofs.Avx2X8X1WAgree (x8_x4_x1_W_last x8_x4_x1_W_small x8_x4_x1_W1_last
  x8_x4_x1_W1_small tau48 tau41)
open Hashtree.Spec

namespace Hashtree.Proofs.Avx2X8ChainW

/-- The x8 run's step count at count `c ≥ 8`. -/
def x8Steps (c : Nat) : Nat :=
  if c < 16 then 16 + (BODYLEN + 31)
  else 16 + (TURNLEN + ((c / 8 - 2) * TURNLEN + (BODYLEN + 31)))

/-- The x4 run's step count at the residual count `c' < 8`. -/
def x4Steps (c' : Nat) : Nat :=
  if c' = 0 then 4 else if c' < 4 then 8 else x4LastSteps

theorem x8Steps_lt (c : Nat) (h : c < 16) : x8Steps c = 16 + (BODYLEN + 31) := by
  simp only [x8Steps, if_pos h]

theorem x8Steps_ge (c : Nat) (h : ¬ c < 16) :
    x8Steps c = 16 + (TURNLEN + ((c / 8 - 2) * TURNLEN + (BODYLEN + 31))) := by
  simp only [x8Steps, if_neg h]

theorem x4Steps_zero : x4Steps 0 = 4 := by simp only [x4Steps, if_pos]

theorem x4Steps_small (c' : Nat) (h0 : c' ≠ 0) (h4 : c' < 4) : x4Steps c' = 8 := by
  simp only [x4Steps, if_neg h0, if_pos h4]

theorem x4Steps_last (c' : Nat) (h0 : c' ≠ 0) (h4 : ¬ c' < 4) : x4Steps c' = x4LastSteps := by
  simp only [x4Steps, if_neg h0, if_neg h4]

theorem upd15_0 (σ : Nat → Int) : upd15 σ 0 = σ 0 := by simp [upd15]
theorem upd15_2 (σ : Nat → Int) : upd15 σ 2 = σ 2 := by simp [upd15]

theorem tau48_0 (j : Nat) (σ : Nat → Int) : tau48 j σ 0 = σ 0 + 512 * ((j : Int) + 2) := by
  simp only [tau48]
  rw [Hashtree.Proofs.AvxX4Exit.sIt_0, upd15_0, tau8_in, sIt8_in, upd15_0]
  omega

theorem tau41_0 (σ : Nat → Int) : tau41 σ 0 = σ 0 + 512 := by
  simp only [tau41]
  rw [Hashtree.Proofs.AvxX4Exit.sIt_0, upd15_0, tau8_in, upd15_0]
  omega

theorem tau48_2 (j : Nat) (σ : Nat → Int) : tau48 j σ 2 = σ 2 - 8 * ((j : Int) + 2) := by
  simp only [tau48]
  rw [Hashtree.Proofs.AvxX4Exit.sIt_2, upd15_2, tau8_count, sIt8_count, upd15_2]
  omega

theorem tau41_2 (σ : Nat → Int) : tau41 σ 2 = σ 2 - 8 := by
  simp only [tau41]
  rw [Hashtree.Proofs.AvxX4Exit.sIt_2, upd15_2, tau8_count, upd15_2]
  omega

/-- **x8 -> x4 -> x1 at the W-mode exit cuts, every count `c ≥ 8`.** -/
theorem x8_chain_W (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    (c % 8 = 0 → g4.halted = true ∧ g4.err = none ∧ g4.tail = none) ∧
    (c % 8 ≠ 0 → g1.halted = true ∧ g1.err = none ∧ g1.tail = none) := by
  intro g8 g4 g1
  -- the x1 run's input, at block `c - c % 4` of the caller's
  let inp1 : Nat → Byte := fun o => inp (64 * (c - c % 4) + o)
  by_cases hlt : c < 16
  · -- the single pass
    have hn8 : x8Steps c = 16 + (BODYLEN + 31) := x8Steps_lt c hlt
    by_cases hz : c % 8 = 0
    · have hc8 : c = 8 := by omega
      obtain ⟨r, e', M', _, hrun, _, H⟩ := x8_x4_W1_zero env0 σ mem0c orcC M r8 hrNum hrIn hrOut
        hrStack hrG hrRet hw8 hw4 hM (by rw [hc]; omega) habi
      dsimp only at H
      obtain ⟨hag, hh, he, ht, _⟩ := H
      refine ⟨fun _ => ?_, fun h => absurd hz h⟩
      have hg4 : g4 = run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 4
          (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (Hashtree.Proofs.Avx2X8WShift.KTE r))))) := by
        show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume (run _ r8 mem0c orcC (x8Steps c) _)) = _
        rw [hz, x4Steps_zero, hn8, hrun]
      rw [hg4]
      exact ⟨hag.halted ▸ hh, hag.err ▸ he, hag.tail ▸ ht⟩
    · refine ⟨fun h => absurd h hz, fun _ => ?_⟩
      by_cases h4 : c % 8 < 4
      · -- 9 ≤ c < 12: the x4 small path
        have hs : c - 8 = c % 4 := by omega
        obtain ⟨r, e', M', _, hrun, H⟩ := x8_x4_x1_W1_small (c - 8) inp1 env0 σ mem0c orcC M r8 r1
          hrNum hrIn hrOut hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1 hM
          (by omega) (by omega) (by rw [hc]; omega) habi
          (fun o => by
            have h := hin (64 * (c - c % 4) + o)
            rw [show sigmaOf tau8 (upd15 σ) 0 + (o : Int) = σ 0 + ((64 * (c - c % 4) + o : Nat) : Int)
              from by rw [tau8_in, upd15_0]; omega]
            exact h)
        dsimp only at H
        obtain ⟨hh, he, ht, _⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 8))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
              (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (Hashtree.Proofs.Avx2X8WShift.KTE r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_small (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1]
        exact ⟨hh, he, ht⟩
      · -- 12 ≤ c < 16: the x4 W-mode exit, then x1
        have hs : c - 8 - 4 = c % 4 := by omega
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
        obtain ⟨hh, he, ht, _⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 8 - 4))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
              (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (Hashtree.Proofs.Avx2X8WShift.KTE r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_last (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1]
        exact ⟨hh, he, ht⟩
  · -- two or more passes: c = 8 (j + 1) + s, j = c / 8 - 2, s = c % 8 + 8
    have hn8 := x8Steps_ge c hlt
    have hcj : σ 2 = 8 * (((c / 8 - 2 : Nat) : Int) + 1) + ((c % 8 + 8 : Nat) : Int) := by
      rw [hc]; omega
    by_cases hz : c % 8 = 0
    · obtain ⟨r, e', M', _, hrun, _, H⟩ := x8_x4_W_zero (c / 8 - 2) env0 σ mem0c orcC M r8 hrNum
        hrIn hrOut hrStack hrG hrRet hw8 hw4 hM (by rw [hc]; omega) habi
      dsimp only at H
      obtain ⟨hag, hh, he, ht, _⟩ := H
      refine ⟨fun _ => ?_, fun h => absurd hz h⟩
      have hg4 : g4 = run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 4
          (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (c / 8 - 2 + 1) (upd15 σ))
            (Hashtree.Proofs.Avx2X8WStrip.KTEs r))))) := by
        show run _ 4 mem0c orcC (x4Steps (c % 8)) (resume (run _ r8 mem0c orcC (x8Steps c) _)) = _
        rw [hz, x4Steps_zero, hn8, hrun]
      rw [hg4]
      exact ⟨hag.halted ▸ hh, hag.err ▸ he, hag.tail ▸ ht⟩
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
        obtain ⟨hh, he, ht, _⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 8 + 8 - 8))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
              (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (c / 8 - 2 + 1) (upd15 σ))
                (Hashtree.Proofs.Avx2X8WStrip.KTEs r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_small (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1]
        exact ⟨hh, he, ht⟩
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
        obtain ⟨hh, he, ht, _⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 8 + 8 - 12))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
              (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (c / 8 - 2 + 1) (upd15 σ))
                (Hashtree.Proofs.Avx2X8WStrip.KTEs r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_last (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1]
        exact ⟨hh, he, ht⟩

end Hashtree.Proofs.Avx2X8ChainW
