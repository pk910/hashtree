import Hashtree.Proofs.Avx512X16WTurn
import Hashtree.Proofs.X86Chain
import Hashtree.Asm.X86Ren
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
  Hashtree.Kernels.X86.Avx512X16

namespace Hashtree.Proofs.Avx512X16WLoop
open Hashtree.Gen.Avx512X16P
open Hashtree.Proofs.Avx512X16WBody
open Hashtree.Proofs.Avx512X16WEntry
open Hashtree.Proofs.Avx512X16WTurn
open Hashtree.Proofs.X86Chain

/-!
# The `avx512_x16` kernel at the wrapper's call state, for every block count

`Avx512X16WTurn` proves one turn of the loop (the 215-slice body plus the 22-instruction
tail) at an arbitrary count `c >= 32`, and the final turn (`jb` taken, `16 <= c < 32`) leading
into the `avx2_x8` tail call.  This file

* iterates the turns (`loop`), lowering the count by 16 per turn;
* proves the three count classes from the wrapper's call state `entryW`:
  `x16_zero` (count 0, four instructions, plain return), `x16_small` (`0 < c < 16`, eight
  instructions, tail call to `avx2_x8`), `x16_loop` (`16 <= c`, `8 + turnSteps * (c / 16)`
  instructions, tail call to `avx2_x8` with the residual `c % 16` blocks);
* packages the kernel as an `X86Chain` `Link`/`Spec` with the step function `steps`;
* states the chain obligation for the link (`x16_chain_head`): from the link's pre-condition
  the run either returns (count 0) or tails into a next link named
  `hashtree_sha256_avx2_x8` whose pre-condition follows from `x8Pre`.

The post-condition of the tail cases is the named predicate `x8Pre`: the state the next link
receives (`resume`) is the exit cut `KTE` under some environment and symbol valuation, behind
the writes of the loop's turns.  In `KTE` the count register `rdx` holds `σ 2 - 16`; `x8Pre`
requires it to be a residual count in `[0, 16)`.
-/

/-! ## The step function -/

/-- One continuing turn: the 215 body slices and the 22-instruction loop tail. -/
def turnSteps : Nat := (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22)

theorem turnSteps_eq : turnSteps = (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 22) := rfl

/-- The step count of the kernel at block count `c`: count 0 returns after `nop; cmp; jne;
ret`; `0 < c < 16` takes the `jb` into `avx2_x8` after the prologue; otherwise each turn
processes 16 blocks. -/
def steps (c : Nat) : Nat := if c = 0 then 4 else if c < 16 then 8 else 8 + turnSteps * (c / 16)

theorem steps_zero : steps 0 = 4 := by simp [steps]

theorem steps_small {c : Nat} (h0 : c ≠ 0) (hlt : c < 16) : steps c = 8 := by
  simp [steps, h0, hlt]

theorem steps_loop {c : Nat} (h : ¬ c < 16) : steps c = 8 + turnSteps * (c / 16) := by
  have h0 : c ≠ 0 := by omega
  simp [steps, h0, h]

/-! ## The turn substitution, iterated -/

/-- `sIt j σ` is the symbol valuation at the start of the `j`-th continuing turn. -/
def sIt : Nat → (Nat → Int) → (Nat → Int)
  | 0, σ => σ
  | j + 1, σ => sIt j (sigmaOf tau σ)

theorem sIt_zero (σ : Nat → Int) : sIt 0 σ = σ := rfl

theorem sIt_succ (j : Nat) (σ : Nat → Int) : sIt (j + 1) σ = sIt j (sigmaOf tau σ) := rfl

theorem sIt_count : ∀ (j : Nat) (σ : Nat → Int), sIt j σ 2 = σ 2 - 16 * (j : Int) := by
  intro j
  induction j with
  | zero => intro σ; simp [sIt]
  | succ j ih =>
    intro σ
    rw [sIt_succ, ih (sigmaOf tau σ), tau_count]
    omega

/-- Symbols past the three renamed ones are untouched by the turn substitution. -/
theorem getD_ge : ∀ (l : List Lin) (i : Nat) (d : Lin), l.length ≤ i → l.getD i d = d
  | [], i, d, _ => rfl
  | a :: as, 0, d, h => by simp at h
  | a :: as, n + 1, d, h => by
    rw [List.getD_cons_succ]
    exact getD_ge as n d (by simpa using h)

theorem sigmaOf_ge (σ : Nat → Int) (i : Nat) (h : tau.length ≤ i) : sigmaOf tau σ i = σ i := by
  have ht : tauAt tau i = Lin.sym i := getD_ge tau i (Lin.sym i) h
  show (tauAt tau i).eval σ = σ i
  rw [ht]
  exact Lin.eval_sym σ i

theorem sIt_9 : ∀ (j : Nat) (σ : Nat → Int), sIt j σ 9 = σ 9 := by
  intro j
  induction j with
  | zero => intro σ; rfl
  | succ j ih =>
    intro σ
    rw [sIt_succ, ih (sigmaOf tau σ), sigmaOf_ge σ 9 (by simp [tau])]

/-! ## Transferring the initial-memory hypothesis -/

/-- The kernel pushes nothing, so `WfMemW` does not depend on the environment, and only
through the stack symbol on the valuation. -/
theorem wfMemW_tr (σ σ' : Nat → Int) (e e' : Key → W32) (m : Addr Int → Cell W32 Int)
    (h9 : σ' 9 = σ 9) (hw : WfMemW rodata [] e σ m) : WfMemW rodata [] e' σ' m := by
  obtain ⟨hro, hret, hin, _⟩ := hw
  refine ⟨hro, ?_, hin, ?_⟩
  · intro k h1 h2
    rw [h9]
    exact hret k h1 h2
  · intro k c hl
    rw [show plookup k ([] : List (Int × Cell E Lin)) = none from rfl] at hl
    cases hl

/-! ## The loop -/

theorem loop (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (s : Nat)
    (hs : 16 ≤ s) (hs32 : s < 32) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog),
      WfMemW rodata [] e σ mem0c → 24 ≤ σ 9 →
      σ 2 = 16 * (j : Int) + (s : Int) → OutLog M →
      ∃ e' M',
        run prog 4 mem0c orcC (j * turnSteps) (fr M (mapState e σ KH)) =
          fr M' (mapState e' (sIt j σ) KH) ∧ OutLog M' := by
  intro j
  induction j with
  | zero =>
    intro e σ M _ _ hσ hM
    exact ⟨e, M, rfl, hM⟩
  | succ j ih =>
    intro e σ M hw hsp hσ hM
    have hge : 32 ≤ σ 2 := by
      rw [hσ]
      have hj : (0 : Int) ≤ (j : Int) := Int.natCast_nonneg j
      have hs' : (16 : Int) ≤ (s : Int) := by exact_mod_cast hs
      have hj : (0 : Int) ≤ (j : Int) := Int.natCast_nonneg j
      omega
    obtain ⟨e1, M1, hrun1, hM1⟩ := iter_step mem0c orcC e σ hw M hM hge hsp
    have hrun1' : run prog 4 mem0c orcC turnSteps (fr M (mapState e σ KH)) =
        fr M1 (mapState e1 (sigmaOf tau σ) KH) := by
      rw [turnSteps_eq]
      exact hrun1
    have h9 : sigmaOf tau σ 9 = σ 9 := sigmaOf_ge σ 9 (by simp [tau])
    have hw1 : WfMemW rodata [] e1 (sigmaOf tau σ) mem0c := wfMemW_tr σ (sigmaOf tau σ) e e1 mem0c h9 hw
    have hsp1 : 24 ≤ sigmaOf tau σ 9 := by rw [h9]; exact hsp
    have hσ1 : sigmaOf tau σ 2 = 16 * (j : Int) + (s : Int) := by
      rw [tau_count, hσ]
      omega
    obtain ⟨e2, M2, hrun2, hM2⟩ := ih e1 (sigmaOf tau σ) M1 hw1 hsp1 hσ1 hM1
    refine ⟨e2, M2, ?_, hM2⟩
    have hlen : (j + 1) * turnSteps = turnSteps + j * turnSteps := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hlen, run_add, hrun1']
    exact hrun2

/-! ## The three count classes -/

/-- Count zero: `nop; cmp rdx,0; jne` not taken; `ret`. -/
theorem x16_zero_run (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ : Nat → Int) (h0 : Mem0Rel env0 σ mW mem0c) (hc : σ 2 = 0) :
    ∃ e', run prog 4 mem0c orcC 4 (mapState env0 σ entryW) = mapState e' σ KZ ∧
      (mapState e' σ KZ).halted = true ∧ (mapState e' σ KZ).tail = none ∧
      (mapState e' σ KZ).err = none := by
  have hA : AssumeOk σ KZ := assumeOk_of σ KZ KZ.assume rfl (asmZero σ hc)
  refine ⟨envAbs env0 (run prog 4 mW orcNone 4 entryW),
    (slice_sound env0 σ mW mem0c h0 prog 4 orcNone orcC 4 entryW KZ [] sliceW_zero KZ_err hA).1,
    ?_, ?_, ?_⟩
  · simp [mapState, KZ_halted]
  · simp [mapState, KZ_tail]
  · simp [mapState, KZ_err]

/-- Counts `0 < c < 16`: the `jne` and the `jb` are taken; the kernel tails into `avx2_x8`
after eight instructions. -/
theorem x16_small_run (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ : Nat → Int) (c : Nat) (h0 : Mem0Rel env0 σ mW mem0c)
    (hc : σ 2 = (c : Int)) (hpos : 0 < c) (hlt : c < 16) :
    ∃ e', run prog 4 mem0c orcC 8 (mapState env0 σ entryW) = mapState e' σ KSm ∧
      (mapState e' σ KSm).halted = true ∧
      (mapState e' σ KSm).tail = some "hashtree_sha256_avx2_x8" ∧
      (mapState e' σ KSm).err = none := by
  have hp : 0 < σ 2 := by rw [hc]; exact_mod_cast hpos
  have hl : σ 2 < 16 := by rw [hc]; exact_mod_cast hlt
  have hA : AssumeOk σ KSm := assumeOk_of σ KSm A0S KSm_assume (asmSmall σ hp hl)
  refine ⟨envAbs env0 (run prog 4 mW orcSmall 8 entryW),
    (slice_sound env0 σ mW mem0c h0 prog 4 orcSmall orcC 8 entryW KSm [] sliceW_small KSm_err hA).1,
    ?_, ?_, ?_⟩
  · simp [mapState, KSm_halted]
  · simp [mapState, KSm_tail]
  · simp [mapState, KSm_err]

/-- The dividend arithmetic of the turn count, with the count split into whole turns and the
residual: `c = 16 * (c / 16 - 2) + ((c % 16) + 32)`, i.e. two turns (`32` blocks) and the
residual. -/
theorem cast_count (c : Nat) (h : 2 ≤ c / 16) :
    (c : Int) = 16 * ((c / 16 - 2 : Nat) : Int) + (((c % 16 : Nat) : Int) + 32) := by
  have hcast : ((c / 16 - 2 : Nat) : Int) = ((c / 16 : Nat) : Int) - 2 := Int.natCast_sub h
  have hmod' : (c : Int) = 16 * ((c / 16 : Nat) : Int) + ((c % 16 : Nat) : Int) := by
    omega
  rw [hmod', hcast]
  omega

/-- The arithmetic of the turn count: with `j = c / 16 - 2` the step count splits into the
entry, the first turn, `j` continuing turns and the exit turn. -/
theorem count_eq (T : Nat) (c j : Nat) (h : c / 16 = j + 2) :
    8 + T * (c / 16) = 8 + (T + (j * T + T)) := by
  rw [h, Nat.mul_add, Nat.mul_comm T 2, Nat.mul_comm j T]
  omega

/-- An empty write log frames nothing. -/
theorem fr_nil (s : CState) : fr ([] : CLog) s = s := by
  simp [fr]

/-- **The loop**, for `c >= 16`: the entry path reaches the body head, one first turn and
`c / 16 - 2` continuing turns go round the loop, and the exit turn tails into `avx2_x8` with
the residual `c % 16` blocks. -/
theorem x16_loop (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ : Nat → Int) (c : Nat) (h0 : Mem0Rel env0 σ mW mem0c)
    (hw : WfMemW rodata [] env0 σ mem0c) (hsp : 24 ≤ σ 9) (h10 : σ 10 = σ 1)
    (hc : σ 2 = (c : Int)) (h16 : 16 ≤ c) :
    ∃ e' M,
      run prog 4 mem0c orcC (steps c) (mapState env0 σ entryW) =
        fr M (mapState e' (sIt (c / 16 - 1) σ) KTE) ∧
      OutLog M ∧ sIt (c / 16 - 1) σ 2 = ((c % 16 : Nat) : Int) + 16 := by
  let E : Key → W32 := envAbs env0 (run prog 4 mW orcEntry 8 entryW)
  have hA : AssumeOk σ (wcutE K1) :=
    assumeOk_of σ (wcutE K1) A0 wcutE_K1_assume (asmge σ (by rw [hc]; omega))
  have hen : run prog 4 mem0c orcC 8 (mapState env0 σ entryW) =
      mapState E σ (wcutH K1) := by
    have h1 := (slice_sound env0 σ mW mem0c h0 prog 4 orcEntry orcC 8 entryW (wcutE K1) T0
      sliceW_entry wcutE_K1_err hA).1
    exact h1.trans (mapState_wcutE E σ h10)
  have hmemE : Mem0Rel E σ mW mem0c :=
    mem0Rel_envAbs env0 σ mW mem0c mW_keyed h0 (run prog 4 mW orcEntry 8 entryW)
  rcases (show c / 16 = 1 ∨ 2 ≤ c / 16 by omega) with hj1 | hj2
  · -- a single turn: the exit
    have hlt : σ 2 < 32 := by rw [hc]; omega
    have hrun := exit1_run E σ mem0c orcC hmemE (by rw [hc]; omega) hlt
    have hs : sIt (c / 16 - 1) σ = σ := by
      rw [show c / 16 - 1 = 0 from by omega]
      rfl
    refine ⟨exitE1 E, [], ?_, ?_, ?_⟩
    · rw [hs, fr_nil]
      rw [steps_loop (by omega), hj1, Nat.mul_one, turnSteps_eq, run_add, hen]
      exact hrun
    · intro q hq
      simp at hq
    · rw [hs, hc]
      have hd := Nat.div_add_mod c 16
      rw [hj1] at hd
      omega
  · -- the first turn, the continuing turns, then the exit
    have hge32 : 32 ≤ σ 2 := by rw [hc]; omega
    have hturn1 := turn1_run E σ mem0c orcC hmemE hge32
    have hstep1 : mapState (turnE1 E) σ KT =
        fr (KT.mem.map (fun p => (mapAddr σ p.1, mapCell (turnE1 E) σ p.2)))
          (mapState (turnE1 E) (sigmaOf tau σ) KH) :=
      turn_step (Hashtree.Proofs.Avx512X16WBody.G216 E) σ
    have h9 : sigmaOf tau σ 9 = σ 9 := sigmaOf_ge σ 9 (by simp [tau])
    have hw1 : WfMemW rodata [] (turnE1 E) (sigmaOf tau σ) mem0c :=
      wfMemW_tr σ (sigmaOf tau σ) env0 (turnE1 E) mem0c h9 hw
    have hsp1 : 24 ≤ sigmaOf tau σ 9 := by rw [h9]; exact hsp
    have hσ1 : sigmaOf tau σ 2 = 16 * ((c / 16 - 2 : Nat) : Int) + (((c % 16 + 16 : Nat)) : Int) := by
      rw [tau_count, hc, cast_count c hj2]
      omega
    obtain ⟨e2, M2, hloop, hM2⟩ :=
      loop mem0c orcC (c % 16 + 16) (by omega) (by omega) (c / 16 - 2) (turnE1 E)
        (sigmaOf tau σ)
        (KT.mem.map (fun p => (mapAddr σ p.1, mapCell (turnE1 E) σ p.2)))
        hw1 hsp1 hσ1 (outLog_map_KT σ (turnE1 E))
    -- the exit turn
    have hσ2 : sIt (c / 16 - 2) (sigmaOf tau σ) 2 = ((c % 16 : Nat) : Int) + 16 := by
      rw [sIt_count, tau_count, hc, cast_count c hj2]
      omega
    have hw2 : WfMemW rodata [] e2 (sIt (c / 16 - 2) (sigmaOf tau σ)) mem0c := by
      have h9' : sIt (c / 16 - 2) (sigmaOf tau σ) 9 = sigmaOf tau σ 9 := sIt_9 _ _
      exact wfMemW_tr (sigmaOf tau σ) _ (turnE1 E) e2 mem0c h9' hw1
    have hsp2 : 24 ≤ sIt (c / 16 - 2) (sigmaOf tau σ) 9 := by
      rw [sIt_9]; exact hsp1
    obtain ⟨e3, M3, hexit, hM3⟩ :=
      exit_step mem0c orcC e2 (sIt (c / 16 - 2) (sigmaOf tau σ)) hw2 M2 hM2
        (by rw [hσ2]; omega) (by rw [hσ2]; omega) hsp2
    refine ⟨e3, M3, ?_, hM3, ?_⟩
    · rw [show c / 16 - 1 = (c / 16 - 2) + 1 from by omega, sIt_succ]
      rw [steps_loop (by omega), count_eq turnSteps c (c / 16 - 2) (by omega)]
      rw [run_add, hen, run_add]
      have hturn1' : run prog 4 mem0c orcC turnSteps (mapState E σ (wcutH K1)) =
          mapState (turnE1 E) σ KT := by
        rw [turnSteps_eq]
        exact hturn1
      have hexit' : run prog 4 mem0c orcC turnSteps
          (fr M2 (mapState e2 (sIt (c / 16 - 2) (sigmaOf tau σ)) KH)) =
          fr M3 (mapState e3 (sIt (c / 16 - 2) (sigmaOf tau σ)) KTE) := by
        rw [turnSteps_eq]
        exact hexit
      rw [hturn1', hstep1, run_add, hloop, hexit']
    · rw [show c / 16 - 1 = (c / 16 - 2) + 1 from by omega, sIt_succ]
      exact hσ2

/-! ## The chain contract -/

/-- The pre-condition of the `avx2_x8` link, as left by the `avx512_x16` tail call: the
`resume`d exit cut `KTE` under some environment and symbol valuation, behind the writes of
the turns.  The count register holds `σ 2 - 16`, the residual number of blocks, which must be
in `[0, 16)`; symbols `0` and `1` (the input and output pointers) have been advanced by the
turns. -/
def x8Pre (f : CState) : Prop :=
  ∃ e σ M, OutLog M ∧ 0 ≤ σ 2 - 16 ∧ σ 2 - 16 < 16 ∧
    f = fr M (resume (mapState e σ KTE))

/-- The post-condition of the `avx512_x16` link at block count `c`. -/
def x16post (c : Nat) (f : CState) : Prop :=
  f.err = none ∧
    ((c = 0 ∧ f.tail = none ∧ ∃ e σ, f = mapState e σ KZ) ∨
     (c ≠ 0 ∧ c < 16 ∧ f.tail = some "hashtree_sha256_avx2_x8" ∧
       ∃ e σ, f = mapState e σ KSm) ∨
     (16 ≤ c ∧ f.tail = some "hashtree_sha256_avx2_x8" ∧ x8Pre (resume f)))

theorem resume_fr (M : CLog) (s : CState) : resume (fr M s) = fr M (resume s) := rfl

/-- **The kernel at every count.** -/
theorem x16_all (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ : Nat → Int) (c : Nat) (h0 : Mem0Rel env0 σ mW mem0c)
    (hw : WfMemW rodata [] env0 σ mem0c) (hsp : 24 ≤ σ 9) (h10 : σ 10 = σ 1)
    (hc : σ 2 = (c : Int)) :
    x16post c (run prog 4 mem0c orcC (steps c) (mapState env0 σ entryW)) := by
  rcases Nat.eq_zero_or_pos c with hc0 | hpos
  · subst hc0
    obtain ⟨e', hrun, hh, htl, he⟩ := x16_zero_run mem0c orcC env0 σ h0 (by simpa using hc)
    refine ⟨?_, Or.inl ⟨rfl, ?_, ⟨e', σ, hrun⟩⟩⟩
    · rw [steps_zero, hrun]
      exact he
    · rw [steps_zero, hrun]
      exact htl
  · rcases (show c < 16 ∨ 16 ≤ c by omega) with hlt | h16
    · obtain ⟨e', hrun, hh, htl, he⟩ := x16_small_run mem0c orcC env0 σ c h0 hc hpos hlt
      refine ⟨?_, Or.inr (Or.inl ⟨by omega, hlt, ?_,
        ⟨e', σ, by rw [steps_small (by omega) hlt]; exact hrun⟩⟩)⟩
      · rw [steps_small (by omega) hlt, hrun]
        exact he
      · rw [steps_small (by omega) hlt, hrun]
        exact htl
    · obtain ⟨e', M, hrun, hM, hσ'⟩ :=
        x16_loop mem0c orcC env0 σ c h0 hw hsp h10 hc h16
      refine ⟨?_, Or.inr (Or.inr ⟨h16, ?_, ⟨e', sIt (c / 16 - 1) σ, M, hM, ?_, ?_, ?_⟩⟩)⟩
      · rw [hrun]
        simp [fr, mapState, KTE_err]
      · rw [hrun]
        simp [fr, mapState, KTE_tail]
      · rw [hσ']
        omega
      · rw [hσ']
        omega
      · rw [hrun, resume_fr]

/-- The link: the kernel image, its rodata region and its step function. -/
def x16link : Link :=
  { name := "hashtree_sha256_avx512_x16", prog := prog, ro := 4, steps := steps }

/-- The kernel's `X86Chain` specification at block count `c`. -/
def x16spec (env0 : Key → W32) (σ : Nat → Int) (c : Nat) : Spec :=
  { link := x16link, pre := fun s => s = mapState env0 σ entryW, post := x16post c }

/-- **The per-link obligation of the chain**, for a next link named `hashtree_sha256_avx2_x8`
whose pre-condition follows from `x8Pre`. -/
theorem x16_chain_head (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ : Nat → Int) (c : Nat) (h0 : Mem0Rel env0 σ mW mem0c)
    (hw : WfMemW rodata [] env0 σ mem0c) (hsp : 24 ≤ σ 9) (h10 : σ 10 = σ 1)
    (hc : σ 2 = (c : Int)) (sp' : Spec) (hname : sp'.link.name = "hashtree_sha256_avx2_x8")
    (hpreS : ∀ (e : Key → W32) (σ' : Nat → Int), sp'.pre (resume (mapState e σ' KSm)))
    (hpre : ∀ f, x8Pre f → sp'.pre f) :
    ∀ s, (x16spec env0 σ c).pre s →
      let f := step mem0c orcC c (x16spec env0 σ c).link s
      f.err = none ∧
        ((f.tail = none ∧ (x16spec env0 σ c).post f) ∨
         (f.tail = some sp'.link.name ∧ sp'.pre (resume f))) := by
  intro s hs
  subst hs
  simp only [step, x16spec, x16link]
  have hall := x16_all mem0c orcC env0 σ c h0 hw hsp h10 hc
  obtain ⟨he, hdisj⟩ := hall
  refine ⟨he, ?_⟩
  rcases hdisj with ⟨hc0, htl, hst⟩ | ⟨-, -, htl, hst⟩ | ⟨-, htl, h8⟩
  · exact Or.inl ⟨htl, he, Or.inl ⟨hc0, htl, hst⟩⟩
  · obtain ⟨e, σ', hf⟩ := hst
    refine Or.inr ⟨by rw [htl, hname], ?_⟩
    rw [hf]
    exact hpreS e σ'
  · exact Or.inr ⟨by rw [htl, hname], hpre _ h8⟩

/-! ## A fresh rodata region -/

/-- The post-condition transported to a fresh rodata region `r`: the region-`r` run is the
region-4 run renamed by `swap 4 r`. -/
def x16postR (r : Region) (c : Nat) (f : CState) : Prop :=
  ∃ g, f = (X86Ren.swap 4 r).state g ∧ x16post c g

/-- **The body at a fresh rodata region** `r`, by `X86Ren.run_swap_chain`: the region-4 body
run, renamed.  This is the form a link whose rodata does not live in region `4` uses. -/
theorem body_runW_region (r : Region) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (env1 : Key → W32) (σ : Nat → Int)
    (h0 : Mem0Rel (G1 env1) σ mW ((X86Ren.swap 4 r).mem mem0c)) (hge : 16 ≤ σ 2) :
    run prog r mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ((X86Ren.swap 4 r).state (mapState (G1 env1) σ (wcutH K1))) =
      (X86Ren.swap 4 r).state (mapState (G216 env1) σ (wcutH K216)) := by
  exact (X86Ren.run_swap_chain r hrNum hrRet prog mem0c orcC (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (59 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (12 + (19 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (20 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (29 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (19 + (2 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (7 + (1 + (7 + (1 + (2 + (2 + (2 + (2 + (7 + (1 + (7 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) _).trans
    (congrArg (X86Ren.swap 4 r).state (body_runW env1 σ ((X86Ren.swap 4 r).mem mem0c) orcC h0 hge))

/-- The body's env/mem side at a fresh rodata region: `Mem0Rel` is region-agnostic, so the
region-4 statement applies verbatim to the renamed memory. -/
theorem body_memW_region (r : Region) (mem0c : Addr Int → Cell W32 Int) (env1 : Key → W32)
    (σ : Nat → Int) (h0 : Mem0Rel (G1 env1) σ mW ((X86Ren.swap 4 r).mem mem0c)) :
    Mem0Rel (G216 env1) σ mW ((X86Ren.swap 4 r).mem mem0c) :=
  body_memW env1 σ _ h0

/-- **The whole run at a fresh rodata region** `r`: `run_swap_chain` for the kernel's step
function. -/
theorem x16_run_region (r : Region) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (env0 : Key → W32) (σ : Nat → Int)
    (c : Nat) :
    run prog r mem0c orcC (steps c) ((X86Ren.swap 4 r).state (mapState env0 σ entryW)) =
      (X86Ren.swap 4 r).state
        (run prog 4 ((X86Ren.swap 4 r).mem mem0c) orcC (steps c) (mapState env0 σ entryW)) :=
  X86Ren.run_swap_chain r hrNum hrRet prog mem0c orcC (steps c) _

/-- **The kernel at every count, at a fresh rodata region** `r`. -/
theorem x16_all_region (r : Region) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (env0 : Key → W32) (σ : Nat → Int)
    (c : Nat) (h0 : Mem0Rel env0 σ mW ((X86Ren.swap 4 r).mem mem0c))
    (hw : WfMemW rodata [] env0 σ ((X86Ren.swap 4 r).mem mem0c)) (hsp : 24 ≤ σ 9)
    (h10 : σ 10 = σ 1) (hc : σ 2 = (c : Int)) :
    x16postR r c (run prog r mem0c orcC (steps c) ((X86Ren.swap 4 r).state (mapState env0 σ entryW))) :=
  ⟨_, x16_run_region r hrNum hrRet mem0c orcC env0 σ c,
    x16_all ((X86Ren.swap 4 r).mem mem0c) orcC env0 σ c h0 hw hsp h10 hc⟩

end Hashtree.Proofs.Avx512X16WLoop
