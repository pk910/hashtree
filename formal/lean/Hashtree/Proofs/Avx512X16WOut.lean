import Hashtree.Proofs.Avx512X16WOutTail
import Hashtree.Proofs.Avx512X16WLoop

/-!
# R2c — output correctness of the `avx512_x16` loop at the wrapper's call state

`Avx512X16WLoop.x16_loop` runs the kernel for `c ≥ 16` blocks from `entryW` to the exit cut
`KTE` behind the write log of the turns, but says nothing about the bytes written.  This file
adds the digests:

* `iter_out` / `exit_out`: one continuing / final turn from the loop head `KH`, with the turn's
  write log exposed — exactly the 512 output cells `[σ 1, σ 1 + 512)` holding the SHA-256 of
  the 16 blocks at the input pointer (`outOk_KT` / `outOk_KTE` through the lifted invariant
  chain `invV_body` and the tail step `stepT_turn` / `stepT_exit`);
* `loop_out`: `j` turns, blocks `0 .. 16 j - 1` at `[σ 1, σ 1 + 512 j)`;
* `turnOut : TurnOut` — the statement fixed by R5 (`WinAvx512Bridge.TurnOut`, copied
  verbatim): under the hypotheses of `x16_loop` and the input bytes, the final write log is
  output cells of the finished blocks only, holding their digests.

The symbol bookkeeping: `tau` advances the input pointer (symbol `0`) by 1024 and the output
pointer (symbol `1`) by 512 per turn (`tau_in` / `tau_out`, `sIt_in` / `sIt_out`); the
input of turn `j` is the input shifted by `1024 j` bytes, read through `view M mem0c`, which
is transparent on region `rIn` because the loop only writes `rOut` (`view_rIn`).
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.Avx512X16
open Hashtree.Gen.Avx512X16P
open Hashtree.Proofs.Avx512X16WBody
open Hashtree.Proofs.Avx512X16WEntry
open Hashtree.Proofs.Avx512X16WTurn
open Hashtree.Proofs.Avx512X16WLoop

namespace Hashtree.Proofs.Avx512X16WOut

/-! ## The statement (R5's `WinAvx512Bridge.TurnOut`, verbatim) -/

/-- **`TurnOut`:** under the hypotheses of `Avx512X16WLoop.x16_loop` and the
input bytes, the linux avx512 loop's final write log consists of output cells of the finished
blocks only, `[σ 1, σ 1 + 32 (c - c % 16))`, holding their SHA-256 bytes.  The per-turn form
(turn `j` writes blocks `16 j .. 16 j + 15` at the W cut, `sIt j σ 1 = σ 1 + 512 j`) iterates to
this; the windows link consumes exactly this statement. -/
def TurnOut : Prop :=
  ∀ (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (env0 : Key → W32) (σ : Nat → Int)
    (c : Nat) (inp : Nat → Spec.Byte),
    Mem0Rel env0 σ Hashtree.Proofs.Avx512X16WBody.mW mem0c →
    WfMemW Hashtree.Kernels.X86.Avx512X16.rodata [] env0 σ mem0c → σ 10 = σ 1 →
    σ 2 = c → 16 ≤ c →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.Avx512X16.prog 4 mem0c orcC (Hashtree.Proofs.Avx512X16WLoop.steps c)
        (mapState env0 σ entryW)).mem,
      p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * ((c - c % 16 : Nat) : Int)) ∧
    OutOk inp (σ 1) (c - c % 16)
      (run Hashtree.Kernels.X86.Avx512X16.prog 4 mem0c orcC (Hashtree.Proofs.Avx512X16WLoop.steps c)
        (mapState env0 σ entryW)).mem

/-! ## Symbols -/

theorem tau_in (σ : Nat → Int) : sigmaOf tau σ 0 = σ 0 + 1024 := by
  have ht : tauAt tau 0 = (⟨1024, [1]⟩ : Lin) := rfl
  show (tauAt tau 0).eval σ = _
  rw [ht]
  simp [Lin.eval, dotC]
  omega

theorem tau_out (σ : Nat → Int) : sigmaOf tau σ 1 = σ 1 + 512 := by
  have ht : tauAt tau 1 = (⟨512, [0, 1]⟩ : Lin) := rfl
  show (tauAt tau 1).eval σ = _
  rw [ht]
  simp [Lin.eval, dotC]
  omega

theorem sIt_in : ∀ (j : Nat) (σ : Nat → Int), sIt j σ 0 = σ 0 + 1024 * (j : Int)
  | 0, σ => by simp [sIt_zero]
  | j + 1, σ => by
    rw [sIt_succ, sIt_in j, tau_in]
    push_cast
    omega

theorem sIt_out : ∀ (j : Nat) (σ : Nat → Int), sIt j σ 1 = σ 1 + 512 * (j : Int)
  | 0, σ => by simp [sIt_zero]
  | j + 1, σ => by
    rw [sIt_succ, sIt_out j, tau_out]
    push_cast
    omega

/-- The input bytes at the next turn's input pointer. -/
theorem hin_tau (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) (inp : Nat → Byte)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ o : Nat, mem0c ⟨rIn, sigmaOf tau σ 0 + o⟩ = .dat ((inp (1024 + o)).zeroExtend 32) 0 := by
  intro o
  rw [tau_in, show σ 0 + 1024 + (o : Int) = σ 0 + ((1024 + o : Nat) : Int) by push_cast; omega]
  exact hin (1024 + o)

/-- The input bytes after `j` turns. -/
theorem hin_sIt (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) (inp : Nat → Byte) (j : Nat)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ o : Nat, mem0c ⟨rIn, sIt j σ 0 + o⟩ = .dat ((inp (1024 * j + o)).zeroExtend 32) 0 := by
  intro o
  rw [sIt_in, show σ 0 + 1024 * (j : Int) + (o : Int) = σ 0 + ((1024 * j + o : Nat) : Int) by
    push_cast; omega]
  exact hin (1024 * j + o)

/-- `HMem` at the entry: the symbolic input cells are the concrete bytes (`Mem0Rel`). -/
theorem hmem_entry (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (h0 : Mem0Rel env σ mW mem0c)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    HMem 1024 inp env := by
  intro o _
  have hW : mW ⟨rIn, ⟨(o : Int), [1]⟩⟩ = .dat (.var (.m rIn ⟨(o : Int), [1]⟩)) 0 := rfl
  have hc := h0 ⟨rIn, ⟨(o : Int), [1]⟩⟩ (by rw [hW]; trivial)
  rw [hW] at hc
  simp only [mapAddr, mapCell, in_eval, E.eval] at hc
  rw [hin o] at hc
  exact (Cell.dat.inj hc).1.symm

/-! ## One turn, with its output -/

/-- A continuing turn (`32 ≤ σ 2`) from the loop head: the state after the turn behind the
turn's own 512 output cells, which hold the digests of the 16 blocks at the input pointer. -/
theorem iter_out (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (e : Key → W32) (σ : Nat → Int) (M : CLog) (inp : Nat → Byte)
    (hw : WfMemW rodata [] e σ mem0c) (hM : OutLogO M) (hge : 32 ≤ σ 2)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e' N,
      run prog 4 mem0c orcC turnSteps (fr M (mapState e σ KH)) =
          fr (N ++ M) (mapState e' (sigmaOf tau σ) KH) ∧
        (∀ p ∈ N, p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 512) ∧
        OutOk inp (σ 1) 16 N := by
  let E := ecomb e σ (view M mem0c)
  have hrel : Mem0Rel E σ mW (view M mem0c) := by
    rw [show mW = mem0sW 4 rodata [] from rfl]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c)
      (wfMemW_push_nil rodata e E σ (view M mem0c) (wfMemW_view rodata e σ mem0c M hM hw))
      (envMem_ecomb E σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC turnSteps (fr M (mapState e σ KH)) =
      fr M (mapState (turnE E) σ KT) := by
    rw [turnSteps_eq, run_fr]
    rw [mapState_nOnly e E σ (fun _ => rfl) KH KH_nOnly]
    exact congrArg (fr M) (turn_run E σ (view M mem0c) orcC hrel hge)
  have hmE : HMem 1024 inp E := hmem_view e σ M mem0c inp (outLogO_outLog hM) hin
  have hI : InvC inp (turnE E) L217 :=
    stepT_turn inp (Hashtree.Proofs.Avx512X16WBodyV.G216 E) (invV_body inp E hmE) hmE
  refine ⟨turnE E, KT.mem.map (fun p => (mapAddr σ p.1, mapCell (turnE E) σ p.2)), ?_, ?_, ?_⟩
  · have hstep : mapState (turnE E) σ KT =
        fr (KT.mem.map (fun p => (mapAddr σ p.1, mapCell (turnE E) σ p.2)))
          (mapState (turnE E) (sigmaOf tau σ) KH) :=
      turn_step (Hashtree.Proofs.Avx512X16WBodyV.G216 E) σ
    rw [hrun, hstep, fr_fr']
  · exact outShape_sound KT KT_outShape (turnE E) σ
  · exact outOk_KT inp (turnE E) σ hI

/-- The final turn (`16 ≤ σ 2 < 32`, `jb` taken) from the loop head: the exit cut `KTE`, whose
own write log is the turn's 512 output cells holding the 16 digests. -/
theorem exit_out (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (e : Key → W32) (σ : Nat → Int) (M : CLog) (inp : Nat → Byte)
    (hw : WfMemW rodata [] e σ mem0c) (hM : OutLogO M) (hge : 16 ≤ σ 2) (hlt : σ 2 < 32)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e',
      run prog 4 mem0c orcC turnSteps (fr M (mapState e σ KH)) = fr M (mapState e' σ KTE) ∧
        (∀ p ∈ (mapState e' σ KTE).mem, p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 512) ∧
        OutOk inp (σ 1) 16 (mapState e' σ KTE).mem := by
  let E := ecomb e σ (view M mem0c)
  have hrel : Mem0Rel E σ mW (view M mem0c) := by
    rw [show mW = mem0sW 4 rodata [] from rfl]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c)
      (wfMemW_push_nil rodata e E σ (view M mem0c) (wfMemW_view rodata e σ mem0c M hM hw))
      (envMem_ecomb E σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC turnSteps (fr M (mapState e σ KH)) =
      fr M (mapState (exitE E) σ KTE) := by
    rw [turnSteps_eq, run_fr]
    rw [mapState_nOnly e E σ (fun _ => rfl) KH KH_nOnly]
    exact congrArg (fr M) (exit_run E σ (view M mem0c) orcC hrel hge hlt)
  have hmE : HMem 1024 inp E := hmem_view e σ M mem0c inp (outLogO_outLog hM) hin
  have hI : InvC inp (exitE E) L217 :=
    stepT_exit inp (Hashtree.Proofs.Avx512X16WBodyV.G216 E) (invV_body inp E hmE) hmE
  exact ⟨exitE E, hrun, outShape_sound KTE KTE_outShape (exitE E) σ, outOk_KTE inp (exitE E) σ hI⟩

/-- Output cells only: R2b's turn-framing log invariant. -/
theorem outLogO_of_shape (N : CLog) (b lo : Int)
    (h : ∀ p ∈ N, p.1.region = rOut ∧ lo ≤ p.1.off ∧ p.1.off < b) : OutLogO N :=
  fun p hp => (h p hp).1

/-! ## The turns -/

/-- `j` continuing turns from the loop head: the new log `N` holds exactly the output cells
`[σ 1, σ 1 + 512 j)`, with the digests of blocks `0 .. 16 j - 1` of the input at the input
pointer. -/
theorem loop_out (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (s : Nat)
    (hs : 16 ≤ s) (hs32 : s < 32) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog) (inp : Nat → Byte),
      WfMemW rodata [] e σ mem0c →
      σ 2 = 16 * (j : Int) + (s : Int) → OutLogO M →
      (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
      ∃ e' N,
        run prog 4 mem0c orcC (j * turnSteps) (fr M (mapState e σ KH)) =
            fr (N ++ M) (mapState e' (sIt j σ) KH) ∧
          (∀ p ∈ N, p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 512 * (j : Int)) ∧
          OutOk inp (σ 1) (16 * j) N := by
  intro j
  induction j with
  | zero =>
    intro e σ M inp _ hσ hM hin
    refine ⟨e, [], rfl, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro n i b hn
      exact absurd hn (Nat.not_lt_zero n)
  | succ j ih =>
    intro e σ M inp hw hσ hM hin
    have hge : 32 ≤ σ 2 := by
      rw [hσ]
      have hj : (0 : Int) ≤ (j : Int) := Int.natCast_nonneg j
      have hs' : (16 : Int) ≤ (s : Int) := by exact_mod_cast hs
      push_cast
      omega
    obtain ⟨e1, N1, hrun1, hsh1, hout1⟩ := iter_out mem0c orcC e σ M inp hw hM hge hin
    have h9 : sigmaOf tau σ 9 = σ 9 := sigmaOf_ge σ 9 (by simp [tau])
    have hw1 : WfMemW rodata [] e1 (sigmaOf tau σ) mem0c := wfMemW_tr σ (sigmaOf tau σ) e e1 mem0c h9 hw
    have hσ1 : sigmaOf tau σ 2 = 16 * (j : Int) + (s : Int) := by
      rw [tau_count, hσ]
      push_cast
      omega
    have hM1 : OutLogO (N1 ++ M) := outLogO_app (outLogO_of_shape N1 _ _ hsh1) hM
    obtain ⟨e2, N2, hrun2, hsh2, hout2⟩ :=
      ih e1 (sigmaOf tau σ) (N1 ++ M) (fun o => inp (1024 + o)) hw1 hσ1 hM1
        (hin_tau mem0c σ inp hin)
    refine ⟨e2, N2 ++ N1, ?_, ?_, ?_⟩
    · have hlen : (j + 1) * turnSteps = turnSteps + j * turnSteps := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [hlen, run_add, hrun1, sIt_succ, List.append_assoc]
      exact hrun2
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · have := hsh2 p h
        rw [tau_out] at this
        refine ⟨this.1, ?_, ?_⟩ <;> push_cast <;> omega
      · have := hsh1 p h
        refine ⟨this.1, ?_, ?_⟩ <;> push_cast <;> omega
    · rw [show 16 * (j + 1) = 16 + 16 * j by omega]
      refine outOk_glue inp (σ 1) (16 * j) N2 N1 ?_ hout1 ?_
      · intro p hp hr
        have := hsh2 p hp
        rw [tau_out] at this
        omega
      · rw [tau_out] at hout2
        exact hout2

/-! ## From the entry -/

/-- **`TurnOut`.** -/
theorem turnOut : TurnOut := by
  intro mem0c orcC env0 σ c inp h0 hw h10 hc h16 hin
  let E : Key → W32 := envAbs env0 (run prog 4 mW orcEntry 8 entryW)
  have hA : AssumeOk σ (wcutE K1) :=
    assumeOk_of σ (wcutE K1) _ wcutE_K1_assume (asmge σ (by rw [hc]; omega))
  have hen : run prog 4 mem0c orcC 8 (mapState env0 σ entryW) =
      mapState E σ (wcutH K1) := by
    have h1 := (slice_sound env0 σ mW mem0c h0 prog 4 orcEntry orcC 8 entryW (wcutE K1) T0
      sliceW_entry wcutE_K1_err hA).1
    exact h1.trans (mapState_wcutE E σ h10)
  have hmemE : Mem0Rel E σ mW mem0c :=
    mem0Rel_envAbs env0 σ mW mem0c mW_keyed h0 (run prog 4 mW orcEntry 8 entryW)
  have hmE : HMem 1024 inp E :=
    hmem_envAbs 1024 inp env0 _ (hmem_entry env0 σ mem0c inp h0 hin)
  have hcnt : c - c % 16 = 16 * (c / 16) := by
    have := Nat.div_add_mod c 16
    omega
  rcases (show c / 16 = 1 ∨ 2 ≤ c / 16 by omega) with hj1 | hj2
  · -- a single turn: the exit
    have hlt : σ 2 < 32 := by rw [hc]; omega
    have hrun := exit1_run E σ mem0c orcC hmemE (by rw [hc]; omega) hlt
    have hfin : run prog 4 mem0c orcC (steps c) (mapState env0 σ entryW) =
        mapState (exitE1 E) σ KTE := by
      rw [steps_loop (by omega), hj1, Nat.mul_one, turnSteps_eq, run_add, hen]
      exact hrun
    have hI : InvC inp (exitE1 E) L217 :=
      stepT_exit inp (Hashtree.Proofs.Avx512X16WBody.G216 E) (invW_body inp E hmE) hmE
    rw [hfin, hcnt, hj1]
    refine ⟨?_, outOk_KTE inp (exitE1 E) σ hI⟩
    intro p hp
    have := outShape_sound KTE KTE_outShape (exitE1 E) σ p hp
    refine ⟨this.1, ?_, ?_⟩ <;> push_cast <;> omega
  · -- the first turn, the continuing turns, then the exit
    obtain ⟨q, hq⟩ : ∃ q, c / 16 = q + 2 := ⟨c / 16 - 2, by omega⟩
    have hge32 : 32 ≤ σ 2 := by rw [hc]; omega
    have hturn1 := turn1_run E σ mem0c orcC hmemE hge32
    have hstep1 : mapState (turnE1 E) σ KT =
        fr (KT.mem.map (fun p => (mapAddr σ p.1, mapCell (turnE1 E) σ p.2)))
          (mapState (turnE1 E) (sigmaOf tau σ) KH) :=
      turn_step (Hashtree.Proofs.Avx512X16WBody.G216 E) σ
    obtain ⟨N1, hN1⟩ : ∃ N1 : CLog, N1 = KT.mem.map (fun p => (mapAddr σ p.1, mapCell (turnE1 E) σ p.2)) :=
      ⟨_, rfl⟩
    rw [← hN1] at hstep1
    have hsh1 : ∀ p ∈ N1, p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 512 := by
      rw [hN1]; exact outShape_sound KT KT_outShape (turnE1 E) σ
    have hout1 : OutOk inp (σ 1) 16 N1 := by
      rw [hN1]
      exact outOk_KT inp (turnE1 E) σ
        (stepT_turn inp (Hashtree.Proofs.Avx512X16WBody.G216 E) (invW_body inp E hmE) hmE)
    have h9 : sigmaOf tau σ 9 = σ 9 := sigmaOf_ge σ 9 (by simp [tau])
    have hw1 : WfMemW rodata [] (turnE1 E) (sigmaOf tau σ) mem0c :=
      wfMemW_tr σ (sigmaOf tau σ) env0 (turnE1 E) mem0c h9 hw
    have hcq : c = 16 * (q + 2) + c % 16 := by
      have := Nat.div_add_mod c 16
      omega
    have hσ1 : sigmaOf tau σ 2 = 16 * (q : Int) + ((c % 16 + 16 : Nat) : Int) := by
      rw [tau_count, hc, hcq]
      push_cast
      omega
    obtain ⟨e2, N2, hloop, hsh2, hout2⟩ :=
      loop_out mem0c orcC (c % 16 + 16) (by omega) (by omega) q (turnE1 E) (sigmaOf tau σ) N1
        (fun o => inp (1024 + o)) hw1 hσ1 (outLogO_of_shape N1 _ _ hsh1)
        (hin_tau mem0c σ inp hin)
    -- the exit turn
    obtain ⟨σ2, hσ2def⟩ : ∃ σ2 : Nat → Int, σ2 = sIt q (sigmaOf tau σ) := ⟨_, rfl⟩
    rw [← hσ2def] at hloop
    have hσ2 : σ2 2 = ((c % 16 : Nat) : Int) + 16 := by
      rw [hσ2def, sIt_count, tau_count, hc, hcq]
      push_cast
      omega
    have hw2 : WfMemW rodata [] e2 σ2 mem0c := by
      have h9' : σ2 9 = sigmaOf tau σ 9 := by rw [hσ2def]; exact sIt_9 _ _
      exact wfMemW_tr (sigmaOf tau σ) _ (turnE1 E) e2 mem0c h9' hw1
    have hM2 : OutLogO (N2 ++ N1) :=
      outLogO_app (outLogO_of_shape N2 _ _ hsh2) (outLogO_of_shape N1 _ _ hsh1)
    have hin2 : ∀ o : Nat, mem0c ⟨rIn, σ2 0 + o⟩ = .dat ((inp (1024 * (q + 1) + o)).zeroExtend 32) 0 := by
      intro o
      rw [hσ2def, sIt_in, tau_in]
      rw [show σ 0 + 1024 + 1024 * (q : Int) + (o : Int) = σ 0 + ((1024 * (q + 1) + o : Nat) : Int) by
        push_cast; omega]
      exact hin _
    obtain ⟨e3, hexit, hsh3, hout3⟩ :=
      exit_out mem0c orcC e2 σ2 (N2 ++ N1) (fun o => inp (1024 * (q + 1) + o)) hw2 hM2
        (by rw [hσ2]; omega) (by rw [hσ2]; omega) hin2
    -- the whole run
    have hfin : run prog 4 mem0c orcC (steps c) (mapState env0 σ entryW) =
        fr (N2 ++ N1) (mapState e3 σ2 KTE) := by
      rw [steps_loop (by omega), hq, show turnSteps * (q + 2) = turnSteps + (q * turnSteps + turnSteps) by
        rw [Nat.mul_add, Nat.mul_comm turnSteps q]; omega]
      rw [run_add, hen, run_add]
      have hturn1' : run prog 4 mem0c orcC turnSteps (mapState E σ (wcutH K1)) =
          mapState (turnE1 E) σ KT := by
        rw [turnSteps_eq]
        exact hturn1
      rw [hturn1', hstep1, run_add, hloop]
      exact hexit
    -- the output
    have hσ2_1 : σ2 1 = σ 1 + 512 * ((q + 1 : Nat) : Int) := by
      rw [hσ2def, sIt_out, tau_out]
      push_cast
      omega
    have hσ1_1 : sigmaOf tau σ 1 = σ 1 + 512 := tau_out σ
    rw [hfin, hcnt, hq]
    show (∀ p ∈ (mapState e3 σ2 KTE).mem ++ (N2 ++ N1), _) ∧
      OutOk inp (σ 1) (16 * (q + 2)) ((mapState e3 σ2 KTE).mem ++ (N2 ++ N1))
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · have := hsh3 p h
        rw [hσ2_1] at this
        push_cast at this
        refine ⟨this.1, ?_, ?_⟩ <;> push_cast <;> omega
      · rcases List.mem_append.mp h with h | h
        · have := hsh2 p h
          rw [hσ1_1] at this
          push_cast at this
          refine ⟨this.1, ?_, ?_⟩ <;> push_cast <;> omega
        · have := hsh1 p h
          refine ⟨this.1, ?_, ?_⟩ <;> push_cast <;> omega
    · have hlow : OutOk inp (σ 1) (16 * (q + 1)) (N2 ++ N1) := by
        rw [show 16 * (q + 1) = 16 + 16 * q by omega]
        refine outOk_glue inp (σ 1) (16 * q) N2 N1 ?_ hout1 ?_
        · intro p hp hr
          have := hsh2 p hp
          rw [hσ1_1] at this
          omega
        · rw [hσ1_1] at hout2
          exact hout2
      rw [show q + 2 = (q + 1) + 1 by omega]
      refine outOk_step inp (σ 1) (q + 1) _ (N2 ++ N1) ?_ hlow ?_
      · intro p hp hr
        have := hsh3 p hp
        rw [hσ2_1] at this
        push_cast at this ⊢
        omega
      · rw [hσ2_1] at hout3
        exact hout3

end Hashtree.Proofs.Avx512X16WOut
