import Hashtree.Proofs.Avx2X8OutLink
import Hashtree.Proofs.Avx2X8ChainW

/-!
# avx2_x8 -> avx_x4 -> avx_x1: the output clause, every count `c ≥ 8`

`Avx2X8ChainW.x8_chain_W` is run-level.  Here the same case split gives the chain's output
clause: the final log (the x4 run's when `c % 8 = 0`, else the x1 run's) holds all `c` output
blocks with their SHA-256 bytes (`OutOk inp (σ 1) c`), and every cell of it is a cell of the
caller's log `M`, an output byte of the `c` blocks, or a stack byte of the 984-byte frame below
the return marker (`FootC`).  Hypotheses: R2c's `TurnOut8`/`TurnOut8Last` (proved on r2c,
7151bbd) and the new `TurnOut4Last` (`Avx2X8OutLink`).

Per case the final log is the x1 run's own writes (`InRange`/`OutOk` of the per-case
theorems), over the x4 run's log, over the x8 run's log: the x8 blocks come from `x8_out_at` /
`x8_out_last_at`, the x4 blocks (`4 ≤ c % 8`) from `x4_last_out`, the x4 small path and count-0
return write nothing, and the layers are stacked by `outOk_glue` (`layer`).
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
open Hashtree.Proofs.AvxX4LoopWExit (upd15_9)
open Hashtree.Proofs.AvxX4X1WAgree (outLogW_congr sigmaOf_s9)
open Hashtree.Proofs.AvxX1W (steps InRange)
open Hashtree.Proofs.ShaniW (OutOk)
open Hashtree.Proofs.Avx2X8WShift (tau8 BODYLEN)
open Hashtree.Proofs.Avx2X8WLoop (sIt8 TURNLEN tau8_count tau8_in tau8_out tau8_s9 sIt8_count
  sIt8_in sIt8_out sIt8_s9)
open Hashtree.Proofs.Avx2X8X4WAgree (x8_x4_W_zero x8_x4_W1_zero x4LastSteps cutLog8 exitCut_KTE
  exitCut_KTEs sIt8_count8 upd15_count8)
open Hashtree.Proofs.Avx2X8X1WAgree (x8_x4_x1_W_last x8_x4_x1_W_small x8_x4_x1_W1_last
  x8_x4_x1_W1_small tau48 tau41 tau48_9 tau41_9)
open Hashtree.Proofs.Avx2X8ChainW (x8Steps x4Steps x4Steps_small x4Steps_last x4Steps_zero
  x8Steps_lt x8Steps_ge upd15_0 upd15_2 tau48_0 tau41_0 tau48_2 tau41_2)
open Hashtree.Proofs.Avx2X8WAt (renLog renLog_invol swap_fix outLogW_ren)
open Hashtree.Proofs.Avx2X8OutLink
open Hashtree.Spec

namespace Hashtree.Proofs.Avx2X8ChainOut

/-- The chain's footprint: cells of the caller's log `M`, output bytes of the `c` blocks, or the
984-byte frame below the return marker. -/
def FootC (σ : Nat → Int) (c : Nat) (M F : CLog) : Prop :=
  ∀ p ∈ F, p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * (c : Int)) ∨
    (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)

/-! ## Symbols -/

theorem upd15_1 (σ : Nat → Int) : upd15 σ 1 = σ 1 := by simp [upd15]

theorem tau48_1 (j : Nat) (σ : Nat → Int) : tau48 j σ 1 = σ 1 + 256 * ((j : Int) + 2) := by
  simp only [tau48]
  rw [Hashtree.Proofs.AvxX4Exit.sIt_1, upd15_1, tau8_out, sIt8_out, upd15_1]
  omega

theorem tau41_1 (σ : Nat → Int) : tau41 σ 1 = σ 1 + 256 := by
  simp only [tau41]
  rw [Hashtree.Proofs.AvxX4Exit.sIt_1, upd15_1, tau8_out, upd15_1]
  omega

theorem s8_1 (j : Nat) (σ : Nat → Int) :
    sigmaOf tau8 (sIt8 (j + 1) (upd15 σ)) 1 = σ 1 + 256 * ((j : Int) + 2) := by
  rw [tau8_out, sIt8_out, upd15_1]; omega

theorem s8_0 (j : Nat) (σ : Nat → Int) :
    sigmaOf tau8 (sIt8 (j + 1) (upd15 σ)) 0 = σ 0 + 512 * ((j : Int) + 2) := by
  rw [tau8_in, sIt8_in, upd15_0]; omega

theorem s8_9 (j : Nat) (σ : Nat → Int) : sigmaOf tau8 (sIt8 (j + 1) (upd15 σ)) 9 = σ 9 := by
  rw [tau8_s9, sIt8_s9, upd15_9]

theorem s1_1 (σ : Nat → Int) : sigmaOf tau8 (upd15 σ) 1 = σ 1 + 256 := by
  rw [tau8_out, upd15_1]

theorem s1_0 (σ : Nat → Int) : sigmaOf tau8 (upd15 σ) 0 = σ 0 + 512 := by
  rw [tau8_in, upd15_0]

theorem s1_9 (σ : Nat → Int) : sigmaOf tau8 (upd15 σ) 9 = σ 9 := by
  rw [tau8_s9, upd15_9]

/-! ## Logs -/

theorem cutLog8_eq (ρ : RegionRenaming) (K : State E Lin) (e' : Key → W32) (σ' : Nat → Int)
    (M' : CLog) (X : CS) (hX : X = mapState e' σ' K) :
    cutLog8 ρ K e' σ' M' = (ρ.state (fr M' X)).mem := by
  subst hX; rfl

/-- The x8 exit cut's own log is a W-mode log, read off the renamed run's footprint. -/
theorem hlog_of_foot (ρ : RegionRenaming) (hOut : ρ.f rOut = rOut) (hStk : ρ.f rStack = rStack)
    (σ σ' : Nat → Int) (h9 : σ' 9 = σ 9) (M X : CLog) (hM : OutLogW σ M) (lo hi slo : Int)
    (hF : ∀ p ∈ renLog ρ X, p ∈ M ∨ (p.1.region = rOut ∧ lo ≤ p.1.off ∧ p.1.off < hi) ∨
      (p.1.region = rStack ∧ slo ≤ p.1.off ∧ p.1.off < σ 9)) : OutLogW σ' X := by
  have h1 : OutLogW σ (renLog ρ X) := by
    intro p hp
    rcases hF p hp with h | ⟨h, _⟩ | ⟨h, _, h'⟩
    · exact hM p h
    · exact Or.inl h
    · exact Or.inr ⟨h, h'⟩
  have h2 := outLogW_ren ρ hOut hStk σ _ h1
  rw [renLog_invol] at h2
  exact outLogW_congr σ σ' h9 X h2

/-- **One layer**: a later link's own writes `A`, holding blocks `[k, k + n)` at their output
offset and writing only inside the chain's footprint, on top of a log holding blocks `[0, k)`. -/
theorem layer (inp : Nat → Byte) (σ : Nat → Int) (c : Nat) (M : CLog) (k n : Nat) (A B : CLog)
    (hA : OutOk (fun o => inp (64 * k + o)) (σ 1 + 32 * (k : Int)) n A)
    (hAf : ∀ p ∈ A, (p.1.region = rOut ∧ σ 1 + 32 * (k : Int) ≤ p.1.off ∧ p.1.off < σ 1 + 32 * (c : Int)) ∨
      (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9))
    (hB : OutOk inp (σ 1) k B) (hBf : FootC σ c M B) :
    OutOk inp (σ 1) (k + n) (A ++ B) ∧ FootC σ c M (A ++ B) := by
  refine ⟨outOk_glue inp (σ 1) k n A B hA (fun p hp hr => ?_) hB, fun p hp => ?_⟩
  · rcases hAf p hp with ⟨_, h, _⟩ | ⟨h, _⟩
    · exact h
    · rw [hr] at h; exact absurd h (by decide)
  · rcases List.mem_append.mp hp with h | h
    · rcases hAf p h with ⟨a, b, d⟩ | h'
      · exact Or.inr (Or.inl ⟨a, by omega, d⟩)
      · exact Or.inr (Or.inr h')
    · exact hBf p h

/-- The x8 log's footprint, from its link contract. -/
theorem foot8 (σ : Nat → Int) (c n : Nat) (hn : n ≤ c) (M F : CLog)
    (h : ∀ p ∈ F, p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * (n : Int)) ∨
      (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)) : FootC σ c M F := by
  intro p hp
  rcases h p hp with h | ⟨a, b, d⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨a, b, by omega⟩)
  · exact Or.inr (Or.inr h)

/-- The x1 layer's footprint, from its `InRange`. -/
theorem foot1 (σ σ1 : Nat → Int) (c k n : Nat) (hkn : k + n ≤ c) (h9 : σ1 9 = σ 9)
    (h1 : σ1 1 = σ 1 + 32 * (k : Int)) (F : CLog) (h : InRange (σ1 9) (σ1 1) (32 * n) F) :
    ∀ p ∈ F, (p.1.region = rOut ∧ σ 1 + 32 * (k : Int) ≤ p.1.off ∧ p.1.off < σ 1 + 32 * (c : Int)) ∨
      (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9) := by
  intro p hp
  rcases h p hp with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · left; refine ⟨a, by omega, ?_⟩; push_cast at d; omega
  · right; refine ⟨a, ?_, by omega⟩; unfold D8L; omega

/-- The x4 layer's footprint, from `x4_last_out`. -/
theorem foot4 (σ σ4 : Nat → Int) (c k : Nat) (hkn : k + 4 ≤ c) (h9 : σ4 9 = σ 9)
    (h1 : σ4 1 = σ 1 + 32 * (k : Int)) (F : CLog)
    (h : ∀ p ∈ F, (p.1.region = rOut ∧ σ4 1 ≤ p.1.off ∧ p.1.off < σ4 1 + 128) ∨
        (p.1.region = rStack ∧ σ4 9 - 568 ≤ p.1.off ∧ p.1.off < σ4 9)) :
    ∀ p ∈ F, (p.1.region = rOut ∧ σ 1 + 32 * (k : Int) ≤ p.1.off ∧ p.1.off < σ 1 + 32 * (c : Int)) ∨
      (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9) := by
  intro p hp
  rcases h p hp with ⟨a, b, d⟩ | ⟨a, b, d⟩
  · left; exact ⟨a, by omega, by omega⟩
  · right; refine ⟨a, ?_, by omega⟩; unfold D8L; omega

theorem outOk_cast (inp inp' : Nat → Byte) (ob ob' : Int) (n n' : Nat) (F : CLog)
    (hi : inp = inp') (ho : ob = ob') (hn : n = n') (h : OutOk inp ob n F) : OutOk inp' ob' n' F := by
  subst hi ho hn; exact h

/-! ## The output clause -/

/-- **The avx2_x8 -> avx_x4 -> avx_x1 chain's output clause, every count `c ≥ 8`.** -/
theorem x8_chain_W_out (hT8 : TurnOut8) (hT8L : TurnOut8Last) (hT4L : TurnOut4Last)
    (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
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
    (c % 8 = 0 → OutOk inp (σ 1) c g4.mem ∧ FootC σ c M g4.mem) ∧
    (c % 8 ≠ 0 → OutOk inp (σ 1) c g1.mem ∧ FootC σ c M g1.mem) := by
  intro g8 g4 g1
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  let inp1 : Nat → Byte := fun o => inp (64 * (c - c % 4) + o)
  by_cases hlt : c < 16
  · -- the single pass
    have hn8 : x8Steps c = 16 + (BODYLEN + 31) := x8Steps_lt c hlt
    obtain ⟨hF8, hO8⟩ := x8_out_last_at hT8L r8 hrNum hrIn hrOut hrStack hrG hrRet env0 σ mem0c
      orcC M inp hw8 hM (by rw [hc]; omega) (by rw [hc]; omega) habi hin
    have hB8 : FootC σ c M (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
        (fr M (mapState env0 σ entryW))).mem :=
      foot8 σ c 8 h8 M _ (fun p hp => by
        rcases hF8 p hp with h | ⟨a, b, d⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨a, b, by omega⟩)
        · exact Or.inr (Or.inr h))
    by_cases hz : c % 8 = 0
    · have hc8 : c = 8 := by omega
      obtain ⟨r, e', M', _, hrun, _, H⟩ := x8_x4_W1_zero env0 σ mem0c orcC M r8 hrNum hrIn hrOut
        hrStack hrG hrRet hw8 hw4 hM (by rw [hc]; omega) habi
      dsimp only at H
      obtain ⟨hag, _, _, _, hm, _⟩ := H
      refine ⟨fun _ => ?_, fun h => absurd hz h⟩
      have hg4 : g4.mem = (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
          (fr M (mapState env0 σ entryW))).mem := by
        show (run _ 4 mem0c orcC (x4Steps (c % 8)) (resume (run _ r8 mem0c orcC (x8Steps c) _))).mem = _
        rw [hz, x4Steps_zero, hn8, hrun, ← hag.mem]
        show _ ++ _ = _
        rw [hm, List.nil_append]
        exact cutLog8_eq _ _ _ _ _ _ rfl
      rw [hg4]
      exact ⟨outOk_cast _ _ _ _ _ _ _ rfl rfl hc8.symm hO8, hB8⟩
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
        obtain ⟨_, _, _, hgm, hR, hO, _⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 8))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
              (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (Hashtree.Proofs.Avx2X8WShift.KTE r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_small (c % 8) hz h4, hn8, hrun, ← hs]
        have hL8 : cutLog8 (swap 4 r8) (Hashtree.Proofs.Avx2X8WShift.KTE r) e' (upd15 σ) M' =
            (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
              (fr M (mapState env0 σ entryW))).mem := by
          rw [cutLog8_eq _ _ _ _ _ _ rfl, ← hrun]
        rw [hg1, hgm]
        rw [← hL8] at hO8 hB8
        have hk : c - c % 4 = 8 := by omega
        have L := layer inp σ c M 8 (c - 8) _ _
          (outOk_cast _ _ _ _ _ _ _ (by simp only [inp1, hk]) (by rw [s1_1]; push_cast; omega) rfl hO)
          (foot1 σ _ c 8 (c - 8) (by omega) (s1_9 σ) (by rw [s1_1]; push_cast; omega) _ hR) hO8 hB8
        rw [show 8 + (c - 8) = c by omega] at L
        exact L
      · -- 12 ≤ c < 16: the x4 W-mode exit, then x1
        have hs : c - 8 - 4 = c % 4 := by omega
        obtain ⟨r, e', M', hr, hrun, e4, M4, H⟩ := x8_x4_x1_W1_last (c - 8) inp1 env0 σ mem0c orcC M
          r8 r1 hrNum hrIn hrOut hrStack hrG hrRet h1Num h1In h1Out h1Stack h1G h1Ret hw8 hw4 hw1
          hM (by omega) (by omega) (by rw [hc]; omega) habi
          (fun o => by
            have h := hin (64 * (c - c % 4) + o)
            rw [show tau41 σ 0 + 256 + (o : Int) = σ 0 + ((64 * (c - c % 4) + o : Nat) : Int)
              from by rw [tau41_0]; omega]
            exact h)
          (by rw [tau_count, tau41_2, hc]; omega)
        dsimp only at H
        obtain ⟨_, _, _, hgm, hR, hO, _, hL1⟩ := H
        have hL8 : cutLog8 (swap 4 r8) (Hashtree.Proofs.Avx2X8WShift.KTE r) e' (upd15 σ) M' =
            (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
              (fr M (mapState env0 σ entryW))).mem := by
          rw [cutLog8_eq _ _ _ _ _ _ rfl, ← hrun]
        have hlog : OutLogW (upd15 σ) ((mapState e' (upd15 σ) (Hashtree.Proofs.Avx2X8WShift.KTE r)).mem ++ M') := by
          have hF := hF8
          rw [← hL8] at hF
          exact hlog_of_foot (swap 4 r8) f2 f3 σ _ (upd15_9 σ) M _ hM _ _ _ hF
        obtain ⟨A, hA4, hAf4, hAO4⟩ := x4_last_out hT4L (swap 4 r8) f0 f1 f2 f3 f6 (exitCut_KTE r hr) e'
          (upd15 σ) M' mem0c orcC env0 σ hw4 (upd15_9 σ).symm hlog (c - 8) (by omega) (by omega)
          (by rw [upd15_count8, hc]; omega) (fun o => inp (64 * 8 + o))
          (fun o => by
            have h := hin (64 * 8 + o)
            rw [show sigmaOf tau8 (upd15 σ) 0 + (o : Int) = σ 0 + ((64 * 8 + o : Nat) : Int)
              from by rw [s1_0]; omega]
            exact h)
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c - 8 - 4))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
              (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (Hashtree.Proofs.Avx2X8WShift.KTE r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_last (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1, hgm]
        have L4 := layer inp σ c M 8 4 _ _
          (outOk_cast _ _ _ _ _ _ _ rfl (by rw [s1_1]; push_cast; omega) rfl hAO4)
          (foot4 σ _ c 8 (by omega) (s1_9 σ) (by rw [s1_1]; push_cast; omega) _ hAf4) hO8 hB8
        rw [← hL8, ← hA4, ← hL1] at L4
        have hk : c - c % 4 = 8 + 4 := by omega
        have h9x : sigmaOf tau (tau41 σ) 9 = σ 9 := by rw [sigmaOf_s9, tau41_9]
        have h1x : sigmaOf tau (tau41 σ) 1 = σ 1 + 32 * ((8 + 4 : Nat) : Int) := by
          rw [Hashtree.Proofs.AvxX4Exit.sigmaOf_tau1, tau41_1]; push_cast; omega
        have L := layer inp σ c M (8 + 4) (c - 8 - 4) _ _
          (outOk_cast _ _ _ _ _ _ _ (by simp only [inp1, hk]) h1x rfl hO)
          (foot1 σ _ c (8 + 4) (c - 8 - 4) (by omega) h9x h1x _ hR) L4.1 L4.2
        rw [show 8 + 4 + (c - 8 - 4) = c by omega] at L
        exact L
  · -- two or more passes: c = 8 (j + 1) + s, j = c / 8 - 2, s = c % 8 + 8
    have hn8 := x8Steps_ge c hlt
    have hcj : σ 2 = 8 * (((c / 8 - 2 : Nat) : Int) + 1) + ((c % 8 + 8 : Nat) : Int) := by
      rw [hc]; omega
    have hn : 8 * (c / 8 - 2 + 2) = c - c % 8 := by omega
    obtain ⟨hF8, hO8⟩ := x8_out_at hT8 r8 hrNum hrIn hrOut hrStack hrG hrRet env0 σ mem0c
      orcC M (c / 8 - 2) (c % 8 + 8) inp hw8 hM (by omega) (by omega) hcj habi hin
    rw [hn] at hO8
    have hB8 : FootC σ c M (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
        (16 + (TURNLEN + ((c / 8 - 2) * TURNLEN + (BODYLEN + 31))))
        (fr M (mapState env0 σ entryW))).mem :=
      foot8 σ c (c - c % 8) (by omega) M _ (fun p hp => by
        rcases hF8 p hp with h | ⟨a, b, d⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨a, b, by omega⟩)
        · exact Or.inr (Or.inr h))
    by_cases hz : c % 8 = 0
    · obtain ⟨r, e', M', _, hrun, _, H⟩ := x8_x4_W_zero (c / 8 - 2) env0 σ mem0c orcC M r8 hrNum
        hrIn hrOut hrStack hrG hrRet hw8 hw4 hM (by rw [hc]; omega) habi
      dsimp only at H
      obtain ⟨hag, _, _, _, hm, _⟩ := H
      refine ⟨fun _ => ?_, fun h => absurd hz h⟩
      have hg4 : g4.mem = (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
          (16 + (TURNLEN + ((c / 8 - 2) * TURNLEN + (BODYLEN + 31))))
          (fr M (mapState env0 σ entryW))).mem := by
        show (run _ 4 mem0c orcC (x4Steps (c % 8)) (resume (run _ r8 mem0c orcC (x8Steps c) _))).mem = _
        rw [hz, x4Steps_zero, hn8, hrun, ← hag.mem]
        show _ ++ _ = _
        rw [hm, List.nil_append]
        exact cutLog8_eq _ _ _ _ _ _ rfl
      rw [hg4]
      exact ⟨outOk_cast _ _ _ _ _ _ _ rfl rfl (by omega) hO8, hB8⟩
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
        obtain ⟨_, _, _, hgm, hR, hO, _⟩ := H
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 8 + 8 - 8))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
              (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (c / 8 - 2 + 1) (upd15 σ))
                (Hashtree.Proofs.Avx2X8WStrip.KTEs r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_small (c % 8) hz h4, hn8, hrun, ← hs]
        have hL8 : cutLog8 (swap 4 r8) (Hashtree.Proofs.Avx2X8WStrip.KTEs r) e'
            (sIt8 (c / 8 - 2 + 1) (upd15 σ)) M' =
            (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
              (16 + (TURNLEN + ((c / 8 - 2) * TURNLEN + (BODYLEN + 31))))
              (fr M (mapState env0 σ entryW))).mem := by
          rw [cutLog8_eq _ _ _ _ _ _ rfl, ← hrun]
        rw [hg1, hgm]
        rw [← hL8] at hO8 hB8
        have hk : c - c % 4 = c - c % 8 := by omega
        have h1x : sigmaOf tau8 (sIt8 (c / 8 - 2 + 1) (upd15 σ)) 1 = σ 1 + 32 * ((c - c % 8 : Nat) : Int) := by
          rw [s8_1]; omega
        have L := layer inp σ c M (c - c % 8) (c % 8 + 8 - 8) _ _
          (outOk_cast _ _ _ _ _ _ _ (by simp only [inp1, hk]) h1x rfl hO)
          (foot1 σ _ c (c - c % 8) (c % 8 + 8 - 8) (by omega) (s8_9 _ σ) h1x _ hR) hO8 hB8
        rw [show c - c % 8 + (c % 8 + 8 - 8) = c by omega] at L
        exact L
      · have hs : c % 8 + 8 - 12 = c % 4 := by omega
        obtain ⟨r, e', M', hr, hrun, e4, M4, H⟩ := x8_x4_x1_W_last (c / 8 - 2) (c % 8 + 8) inp1 env0 σ
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
        obtain ⟨_, _, _, hgm, hR, hO, _, hL1⟩ := H
        have hL8 : cutLog8 (swap 4 r8) (Hashtree.Proofs.Avx2X8WStrip.KTEs r) e'
            (sIt8 (c / 8 - 2 + 1) (upd15 σ)) M' =
            (run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
              (16 + (TURNLEN + ((c / 8 - 2) * TURNLEN + (BODYLEN + 31))))
              (fr M (mapState env0 σ entryW))).mem := by
          rw [cutLog8_eq _ _ _ _ _ _ rfl, ← hrun]
        have hlog : OutLogW (sIt8 (c / 8 - 2 + 1) (upd15 σ))
            ((mapState e' (sIt8 (c / 8 - 2 + 1) (upd15 σ)) (Hashtree.Proofs.Avx2X8WStrip.KTEs r)).mem ++ M') := by
          have hF := hF8
          rw [← hL8] at hF
          exact hlog_of_foot (swap 4 r8) f2 f3 σ _ (by rw [sIt8_s9, upd15_9]) M _ hM _ _ _ hF
        have h1x4 : sigmaOf tau8 (sIt8 (c / 8 - 2 + 1) (upd15 σ)) 1 =
            σ 1 + 32 * ((c - c % 8 : Nat) : Int) := by
          rw [s8_1]; omega
        obtain ⟨A, hA4, hAf4, hAO4⟩ := x4_last_out hT4L (swap 4 r8) f0 f1 f2 f3 f6 (exitCut_KTEs r hr) e'
          (sIt8 (c / 8 - 2 + 1) (upd15 σ)) M' mem0c orcC env0 σ hw4 (by rw [sIt8_s9, upd15_9])
          hlog (c % 8 + 8 - 8) (by omega) (by omega)
          (by rw [sIt8_count8 (c / 8 - 2) (c % 8 + 8) σ hcj]; omega) (fun o => inp (64 * (c - c % 8) + o))
          (fun o => by
            have h := hin (64 * (c - c % 8) + o)
            rw [show sigmaOf tau8 (sIt8 (c / 8 - 2 + 1) (upd15 σ)) 0 + (o : Int) =
                σ 0 + ((64 * (c - c % 8) + o : Nat) : Int)
              from by rw [s8_0]; omega]
            exact h)
        have hg1 : g1 = run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (c % 8 + 8 - 12))
            (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
              (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (c / 8 - 2 + 1) (upd15 σ))
                (Hashtree.Proofs.Avx2X8WStrip.KTEs r))))))) := by
          show run _ r1 mem0c orcC (steps (c % 4)) (resume (run _ 4 mem0c orcC (x4Steps (c % 8))
            (resume (run _ r8 mem0c orcC (x8Steps c) _)))) = _
          rw [x4Steps_last (c % 8) hz h4, hn8, hrun, ← hs]
        rw [hg1, hgm]
        have L4 := layer inp σ c M (c - c % 8) 4 _ _
          (outOk_cast _ _ _ _ _ _ _ rfl h1x4 rfl hAO4)
          (foot4 σ _ c (c - c % 8) (by omega) (s8_9 _ σ) h1x4 _ hAf4) hO8 hB8
        rw [← hL8, ← hA4, ← hL1] at L4
        have hk : c - c % 4 = c - c % 8 + 4 := by omega
        have h9x : sigmaOf tau (tau48 (c / 8 - 2) σ) 9 = σ 9 := by rw [sigmaOf_s9, tau48_9]
        have h1x : sigmaOf tau (tau48 (c / 8 - 2) σ) 1 = σ 1 + 32 * ((c - c % 8 + 4 : Nat) : Int) := by
          rw [Hashtree.Proofs.AvxX4Exit.sigmaOf_tau1, tau48_1]
          omega
        have L := layer inp σ c M (c - c % 8 + 4) (c % 8 + 8 - 12) _ _
          (outOk_cast _ _ _ _ _ _ _ (by simp only [inp1, hk]) h1x rfl hO)
          (foot1 σ _ c (c - c % 8 + 4) (c % 8 + 8 - 12) (by omega) h9x h1x _ hR) L4.1 L4.2
        rw [show c - c % 8 + 4 + (c % 8 + 8 - 12) = c by omega] at L
        exact L

end Hashtree.Proofs.Avx2X8ChainOut
