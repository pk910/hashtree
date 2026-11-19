import Hashtree.Proofs.Avx2X8X4WAgree

/-!
# avx2_x8 -> avx_x4: the output contracts each link contributes to the chain's log

The chain's output clause (`OutOk` of all `c` blocks over the final log) is assembled from one
output fact per link, each about that link's own writes on top of the log it received:

* `TurnOut8` / `TurnOut8Last` — R2c's output contracts of the W-mode avx2_x8 loop (R5's text,
  `WinAvx2X8Bridge`; proved on research/formal-r2c-x16out, `Avx2X8WOut.turnOut8`/`turnOut8Last`,
  commit 7151bbd — cited, not merged; `OutOk` is `ShaniW.OutOk`, the same definition);
* `TurnOut4Last` — NEW statement (for R2c): the output contract of the one-pass x4 W-mode exit
  (`AvxX4LoopWAll.x4_runW_last`, `4 ≤ c < 8`), in the shape of R2c's `TurnOut4` /
  windows `TurnOut4WLast`: the run's log is the caller's log, output cells of its 4 blocks and
  its own 568-byte frame; the 4 blocks hold their SHA-256 bytes.

Here they are moved to where the chain runs them: `x8_out_at` / `x8_out_last_at` (the x8 run
with its table at a fresh region `r8`, by the swap), and `x4_last_out` (the x4 W-mode exit
entered at the resumed x8 exit cut: its log is own writes `A` over the x8 log, `A` holds the
next 4 blocks).  `outOk_glue` stacks a later link's blocks on an earlier link's.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.X86Chain (CS resume)
open Hashtree.Proofs.AvxX4W (upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW)
open Hashtree.Proofs.AvxX4LoopWExit (K201W K201W_err)
open Hashtree.Proofs.AvxX4LoopWAll (x4_runW_last)
open Hashtree.Proofs.AvxX4Agree (run_agree4)
open Hashtree.Proofs.AvxX4X1WAgree (view_in)
open Hashtree.Proofs.ShaniW (OutOk)
open Hashtree.Proofs.Avx2X8WShift (BODYLEN tau8)
open Hashtree.Proofs.Avx2X8WLoop (TURNLEN tau8_count tau8_in tau8_out tau8_s9)
open Hashtree.Proofs.Avx2X8X4WAgree (x4LastSteps cutLog8 cutBare8 refCut8 cutEnv8 resume_cut8
  x4cut_agree wf_cut8 fr_nil)
open Hashtree.Proofs.Avx2X8X4WAgree (ExitCut)
open Hashtree.Asm.SpecQ (blk)
open Hashtree.Proofs.Avx2X8WAt (renLog renLog_invol swap_fix entry_swap wf_swap outLogW_ren)
open Hashtree.Spec

namespace Hashtree.Proofs.Avx2X8OutLink

/-! ## The statements -/

/-- The step count of `Avx2X8WAll.x8_runW_abi` for `j` further turns (R5's literal). -/
def x8RunSteps (j : Nat) : Nat := 16 + (6062 + (j * 6062 + (6035 + 31)))

/-- The step count of `Avx2X8WAll.x8_runW_last_abi` (`8 ≤ c < 16`). -/
def x8LastSteps : Nat := 16 + (6035 + 31)

/-- The linux avx2_x8 frame below the return marker (generous bound). -/
def D8L : Nat := 984

/-- **`TurnOut8`** (R5's `WinAvx2X8Bridge.TurnOut8`, verbatim; proved by R2c, `Avx2X8WOut.turnOut8`). -/
def TurnOut8 : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (j s : Nat) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.AvxX4LoopWFrame.OutLogW σ M → 8 ≤ s → s < 16 →
    σ 2 = 8 * ((j : Int) + 1) + (s : Int) → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC (x8RunSteps j)
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (8 * (j + 2))
      (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC (x8RunSteps j)
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem

/-- **`TurnOut8Last`** (R5's text, verbatim; proved by R2c, `Avx2X8WOut.turnOut8Last`). -/
def TurnOut8Last : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.AvxX4LoopWFrame.OutLogW σ M → 8 ≤ σ 2 → σ 2 < 16 → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC x8LastSteps
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
        (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 8
      (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC x8LastSteps
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem

/-- **`TurnOut4Last` (new; to be proved by R2c, same route as `turnOut4` / `turnOut4WLast`):**
under the hypotheses of `AvxX4LoopWAll.x4_runW_last` and the input bytes, the final write log of
the one-pass linux avx_x4 W-mode run (`4 ≤ c < 8`) over the caller log `M` holds only cells of
`M`, output cells of its 4 blocks, or the kernel's own frame below `σ 9`, and the 4 blocks hold
their SHA-256 bytes.  The run is `x4_runW_last`'s (`x4LastSteps` is its literal). -/
def TurnOut4Last : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c →
    Hashtree.Proofs.AvxX4LoopWFrame.OutLogW σ M → 4 ≤ σ 2 → σ 2 < 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC
        Hashtree.Proofs.Avx2X8X4WAgree.x4LastSteps (fr M (mapState env0 σ entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 128) ∨
        (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 4
      (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC
        Hashtree.Proofs.Avx2X8X4WAgree.x4LastSteps (fr M (mapState env0 σ entryW))).mem

theorem x8RunSteps_eq (j : Nat) :
    x8RunSteps j = 16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31))) := by
  unfold x8RunSteps TURNLEN BODYLEN
  omega

theorem x8LastSteps_eq : x8LastSteps = 16 + (BODYLEN + 31) := by
  unfold x8LastSteps BODYLEN
  omega

/-! ## Output blocks over stacked logs -/

theorem blk_shift (inp : Nat → Byte) (k n : Nat) :
    blk (fun o => inp (64 * k + o)) n = blk inp (k + n) := by
  funext i
  simp only [blk]
  congr 1
  omega

/-- **Stacking**: a later log `A` holding blocks `[k, k + n)` (relative to its own input and
output pointers) and writing no output cell below block `k`, on top of a log `B` holding blocks
`[0, k)`, holds blocks `[0, k + n)`. -/
theorem outOk_glue (inp : Nat → Byte) (ob : Int) (k n : Nat) (A B : CLog)
    (hA : OutOk (fun o => inp (64 * k + o)) (ob + 32 * (k : Int)) n A)
    (hAf : ∀ p ∈ A, p.1.region = rOut → ob + 32 * (k : Int) ≤ p.1.off)
    (hB : OutOk inp ob k B) : OutOk inp ob (k + n) (A ++ B) := by
  intro m i b hm hi hb
  by_cases hk : m < k
  · obtain ⟨x, hx, hv⟩ := hB m i b hk hi hb
    refine ⟨x, ?_, hv⟩
    rw [lookup_app_right _ _ _ (fun p hp heq => by
      have h := hAf p hp (by rw [heq])
      rw [heq] at h
      simp only at h
      omega)]
    exact hx
  · obtain ⟨x, hx, hv⟩ := hA (m - k) i b (by omega) hi hb
    have ha : (⟨rOut, ob + 32 * (k : Int) + ((32 * (m - k) + 4 * i + b : Nat) : Int)⟩ : Addr Int) =
        ⟨rOut, ob + ((32 * m + 4 * i + b : Nat) : Int)⟩ := by
      congr 1
      push_cast [Nat.sub_eq_iff_eq_add (by omega : k ≤ m)]
      omega
    refine ⟨x, lookup_app_left _ _ _ _ (ha ▸ hx), ?_⟩
    rw [hv, blk_shift, show k + (m - k) = m by omega]

/-- No blocks: nothing to hold. -/
theorem outOk_zero (inp : Nat → Byte) (ob : Int) (M : CLog) : OutOk inp ob 0 M :=
  fun _ _ _ h => absurd h (Nat.not_lt_zero _)

/-- Output cells survive a renaming fixing the output region. -/
theorem outOk_ren (ρ : RegionRenaming) (hOut : ρ.f rOut = rOut) (inp : Nat → Byte) (ob : Int)
    (n : Nat) (M : CLog) (h : OutOk inp ob n M) : OutOk inp ob n (renLog ρ M) := by
  intro m i b hm hi hb
  obtain ⟨x, hx, hv⟩ := h m i b hm hi hb
  refine ⟨x, ?_, hv⟩
  have ha : ρ.addr (⟨rOut, ob + ((32 * m + 4 * i + b : Nat) : Int)⟩ : Addr Int) =
      ⟨rOut, ob + ((32 * m + 4 * i + b : Nat) : Int)⟩ := by
    simp only [RegionRenaming.addr, hOut]
  show lookup _ (M.map fun p => (ρ.addr p.1, ρ.cell p.2)) = _
  rw [← ha, RegionRenaming.lookup_ren, hx]
  rfl

/-! ## The x8 run with its table at `r8` -/

/-- The input bytes are untouched by the swap. -/
theorem swap_in (r8 : Region) (hrIn : r8 ≠ rIn) (mem0c : Addr Int → Cell W32 Int) (x : Int)
    (v : W32) (h : mem0c ⟨rIn, x⟩ = .dat v 0) : (swap 4 r8).mem mem0c ⟨rIn, x⟩ = .dat v 0 := by
  have hf : (swap 4 r8).f rIn = rIn := swap_fixes 4 r8 rIn (by decide) (Ne.symm hrIn)
  show (swap 4 r8).cell (mem0c ((swap 4 r8).addr ⟨rIn, x⟩)) = _
  simp only [RegionRenaming.addr, hf, h]
  rfl

theorem foot_ren (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut)
    (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) (M : CLog) (lo hi slo shi : Int) (A : CLog)
    (h : ∀ p ∈ A, p ∈ renLog (swap 4 r8) M ∨ (p.1.region = rOut ∧ lo ≤ p.1.off ∧ p.1.off < hi) ∨
      (p.1.region = rStack ∧ slo ≤ p.1.off ∧ p.1.off < shi)) :
    ∀ p ∈ renLog (swap 4 r8) A, p ∈ M ∨ (p.1.region = rOut ∧ lo ≤ p.1.off ∧ p.1.off < hi) ∨
      (p.1.region = rStack ∧ slo ≤ p.1.off ∧ p.1.off < shi) := by
  obtain ⟨_, _, h2, h3, _⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rcases h q hq with hm | ⟨hr, ha, hb⟩ | ⟨hr, ha, hb⟩
  · left
    rw [← renLog_invol (swap 4 r8) M]
    exact List.mem_map_of_mem hm
  · right; left
    exact ⟨by show (swap 4 r8).f q.1.region = rOut; rw [hr, h2], ha, hb⟩
  · right; right
    exact ⟨by show (swap 4 r8).f q.1.region = rStack; rw [hr, h3], ha, hb⟩

/-- **The x8 W-mode run, `c = 8 (j + 1) + s`, table at `r8`: its output contract.** -/
theorem x8_out_at (hT : TurnOut8) (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn)
    (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (j s : Nat) (inp : Nat → Byte)
    (hw : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (hs : 8 ≤ s) (hs16 : s < 16) (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int))
    (habi : σ 9 % 16 = 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let g : CS := run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
      (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31)))) (fr M (mapState env0 σ entryW))
    (∀ p ∈ g.mem, p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)) ∧
      OutOk inp (σ 1) (8 * (j + 2)) g.mem := by
  intro g
  obtain ⟨_, _, h2, h3, _⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  obtain ⟨hF, hO⟩ := hT env0 σ ((swap 4 r8).mem mem0c) orcC (renLog (swap 4 r8) M) j s inp
    (wf_swap r8 hrIn hrStack hrRet env0 σ mem0c hw) (outLogW_ren (swap 4 r8) h2 h3 σ M hM)
    hs hs16 hc habi (fun o => swap_in r8 hrIn mem0c _ _ (hin o))
  have hg : g.mem = renLog (swap 4 r8) (run Hashtree.Kernels.X86.Avx2X8.prog 4
      ((swap 4 r8).mem mem0c) orcC (x8RunSteps j)
      (fr (renLog (swap 4 r8) M) (mapState env0 σ entryW))).mem := by
    show (run _ r8 mem0c orcC _ _).mem = _
    rw [entry_swap r8 hrNum hrIn hrOut hrStack hrG env0 σ M, run_swap_chain r8 hrNum hrRet,
      x8RunSteps_eq]
    rfl
  rw [hg]
  exact ⟨foot_ren r8 hrNum hrIn hrOut hrStack hrG M _ _ _ _ _ hF, outOk_ren _ h2 inp _ _ _ hO⟩

/-- **The x8 W-mode run, `8 ≤ c < 16`, table at `r8`: its output contract.** -/
theorem x8_out_last_at (hT : TurnOut8Last) (r8 : Region) (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn)
    (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack) (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Byte)
    (hw : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) (habi : σ 9 % 16 = 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let g : CS := run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
      (fr M (mapState env0 σ entryW))
    (∀ p ∈ g.mem, p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
        (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)) ∧
      OutOk inp (σ 1) 8 g.mem := by
  intro g
  obtain ⟨_, _, h2, h3, _⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  obtain ⟨hF, hO⟩ := hT env0 σ ((swap 4 r8).mem mem0c) orcC (renLog (swap 4 r8) M) inp
    (wf_swap r8 hrIn hrStack hrRet env0 σ mem0c hw) (outLogW_ren (swap 4 r8) h2 h3 σ M hM)
    hge hlt habi (fun o => swap_in r8 hrIn mem0c _ _ (hin o))
  have hg : g.mem = renLog (swap 4 r8) (run Hashtree.Kernels.X86.Avx2X8.prog 4
      ((swap 4 r8).mem mem0c) orcC x8LastSteps
      (fr (renLog (swap 4 r8) M) (mapState env0 σ entryW))).mem := by
    show (run _ r8 mem0c orcC _ _).mem = _
    rw [entry_swap r8 hrNum hrIn hrOut hrStack hrG env0 σ M, run_swap_chain r8 hrNum hrRet,
      x8LastSteps_eq]
    rfl
  rw [hg]
  exact ⟨foot_ren r8 hrNum hrIn hrOut hrStack hrG M _ _ _ _ _ hF, outOk_ren _ h2 inp _ _ _ hO⟩

/-! ## The x4 W-mode exit entered at the resumed x8 exit cut -/

/-- **The x4 one-pass W-mode run from the resumed x8 cut (`4 ≤ c - 8 < 8`): its own writes `A`
over the x8 log `L` hold the next 4 blocks.** -/
theorem x4_last_out (hT : TurnOut4Last) (ρ : RegionRenaming) (hNum : ρ.f rNum = rNum)
    (hIn : ρ.f rIn = rIn) (hOut : ρ.f rOut = rOut) (hStack : ρ.f rStack = rStack)
    (hG : ρ.f rG = rG) {K : State E Lin} (hK : ExitCut K) (e' : Key → W32) (σ' : Nat → Int)
    (M' : CLog) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ0 : Nat → Int)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ0 mem0c) (h9 : σ0 9 = σ' 9)
    (hlog : OutLogW σ' ((mapState e' σ' K).mem ++ M'))
    (s : Nat) (hs : 4 ≤ s) (hs8 : s < 8) (hc : σ' 2 - 8 = (s : Int)) (inp4 : Nat → Byte)
    (hin4 : ∀ o : Nat, mem0c ⟨rIn, sigmaOf tau8 σ' 0 + o⟩ = .dat ((inp4 o).zeroExtend 32) 0) :
    let L : CLog := cutLog8 ρ K e' σ' M'
    let σ4 : Nat → Int := sigmaOf tau8 σ'
    ∃ A : CLog,
      (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
        (resume (ρ.state (fr M' (mapState e' σ' K))))).mem = A ++ L ∧
      (∀ p ∈ A, (p.1.region = rOut ∧ σ4 1 ≤ p.1.off ∧ p.1.off < σ4 1 + 128) ∨
        (p.1.region = rStack ∧ σ4 9 - 568 ≤ p.1.off ∧ p.1.off < σ4 9)) ∧
      OutOk inp4 (σ4 1) 4 A := by
  intro L σ4
  have hw' := wf_cut8 ρ hOut hStack K e' σ' M' env0 σ0 mem0c hw4 h9 hlog
  have hL : OutLogW σ4 L :=
    Hashtree.Proofs.Avx2X8X4WAgree.cutLog8_outLogW ρ hOut hStack K e' σ' M' hlog
  have hc4 : σ4 2 = (s : Int) := by show sigmaOf tau8 σ' 2 = (s : Int); rw [tau8_count]; exact hc
  obtain ⟨e4, M4, hrun, _⟩ := x4_runW_last (cutEnv8 K e' σ4 (view L mem0c)) σ4
    (view L mem0c) orcC [] hw' (fun p hp => by cases hp) s hs hs8 hc4
  rw [fr_nil] at hrun
  have hrun' : run Hashtree.Kernels.X86.AvxX4.prog 4 (view L mem0c) orcC x4LastSteps
      (refCut8 K e' σ' (view L mem0c)) = fr M4 (mapState e4 (Hashtree.Proofs.AvxX4LoopFrame.sIt 0 (upd15 σ4)) K201W) :=
    hrun
  have hagree := run_agree4 4 (view L mem0c) orcC x4LastSteps (refCut8 K e' σ' (view L mem0c))
    (ρ.state (cutBare8 K e' σ')) rfl (x4cut_agree ρ hNum hIn hOut hStack hG hK e' σ' (view L mem0c))
    (by rw [hrun']; simp only [fr, mapState, K201W_err])
  obtain ⟨hF, hO⟩ := hT (cutEnv8 K e' σ4 (view L mem0c)) σ4 (view L mem0c) orcC [] inp4 hw'
    (fun p hp => by cases hp) (by rw [hc4]; exact_mod_cast hs) (by rw [hc4]; exact_mod_cast hs8)
    (fun o => by rw [view_in mem0c L σ4 hL]; exact hin4 o)
  rw [fr_nil] at hF hO
  refine ⟨(run Hashtree.Kernels.X86.AvxX4.prog 4 (view L mem0c) orcC x4LastSteps
    (refCut8 K e' σ' (view L mem0c))).mem, ?_, fun p hp => ?_, hO⟩
  · rw [resume_cut8, run_fr]
    show (run _ 4 (view L mem0c) orcC x4LastSteps (ρ.state (cutBare8 K e' σ'))).mem ++ L = _
    rw [← hagree.mem]
  · rcases hF p hp with h | h | h
    · cases h
    · exact Or.inl h
    · exact Or.inr h

end Hashtree.Proofs.Avx2X8OutLink
