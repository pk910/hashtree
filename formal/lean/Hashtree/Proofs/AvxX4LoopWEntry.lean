import Hashtree.Proofs.AvxX4LoopW
import Hashtree.Proofs.AvxX4LoopWFrame

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.AvxX4
namespace Hashtree.Proofs.AvxX4LoopWExit
open Hashtree.Gen.AvxX4P
open Hashtree.Proofs.AvxX4W
open Hashtree.Proofs.AvxX4Loop
open Hashtree.Proofs.AvxX4LoopTurn
open Hashtree.Proofs.AvxX4LoopW
open Hashtree.Proofs.AvxX4LoopWFrame

/-!
# The W-mode entry and exit segments of the x4 kernel

`AvxX4LoopW` gives one turn from the rebased loop head and `AvxX4LoopWFrame` iterates it.
This module adds the two segments that bracket the loop from the wrapper call state:

* `entry_runW`: from `entryW` at any count `c ≥ 4`, 72 instructions reach the body's first
  cut `K1W` (the entry slice includes the 68-step head slice), behind the caller's log;
* `final_runW`: from the loop head at a residual count in `[4, 8)`, the head slice, the body
  and the 27-step exit slice reach the exit cut `K201W`, which tail-calls
  `hashtree_sha256_avx_x1` with the relative stack restored (`rsp = sAt 0`).

The W-mode run is carried out at `upd15 σ` (symbol 15 carries the dead `rax` of `entryWx`);
`upd15` is the identity on every symbol the kernel's registers and the stack base read.
-/

/-! ## Moving a log between stack bases -/

/-- `upd15` leaves the stack base symbol alone. -/
theorem upd15_9 (σ : Nat → Int) : upd15 σ 9 = σ 9 := by simp [upd15]

/-- A W-mode log only refers to the stack base symbol `σ 9`, so it moves with it. -/
theorem outLogW_s9 (M : CLog) {σ σ' : Nat → Int} (h9 : σ' 9 = σ 9) (hM : OutLogW σ M) :
    OutLogW σ' M := by
  intro p hp
  rcases hM p hp with h | ⟨h, hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, by rw [h9]; exact hlt⟩

/-! ## The entry segment: `entryW` -> the body's first cut -/

/-- The entry slice's taken branches (`cmp rdx,0; je` and `cmp rdx,4; jl` at pc 2). -/
def orcW : Nat → Bool := fun pc => decide (pc ∈ ([2] : List Nat))

theorem entryW_slice : sliceCheck prog 4 m0W orcW 72 entryWx K1W [] = true := by
  decide +kernel

theorem K1W_assume : K1W.assume = A0 := by decide +kernel
theorem K1W_err : K1W.err = none := by decide +kernel

/-- **The W-mode entry segment.**  From the wrapper call state `entryW` at any count `c ≥ 4`,
72 instructions reach the body's first cut `K1W` behind the caller's log.  The run starts at
the explicit entry cut `entryWx` under the wrapper environment `envM` built from the *viewed*
memory (the caller's log is folded in), at `upd15 σ`. -/
theorem entry_runW (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c)
    (hge : 4 ≤ upd15 σ 2) (hM : OutLogW (upd15 σ) M) :
    run prog 4 mem0c orcC 72 (fr M (mapState env0 σ entryW)) =
      fr M (mapState (G1W (envAbs (envM env0 (view M mem0c) (upd15 σ))
        (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) K1W) := by
  rw [run_fr, ← mapState_entryW env0 (view M mem0c) σ]
  have hrel : Mem0Rel (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) m0W (view M mem0c) := by
    rw [m0W_eq]
    exact mem0RelW_of_wf rodata [] _ _ (view M mem0c)
      (wfMemW_upd15 rodata env0 _ σ (view M mem0c)
        (wfW_view rodata env0 env0 σ mem0c M (outLogW_s9 M (upd15_9 σ).symm hM) hw))
      (fun r off => rfl)
  exact congrArg (fr M) (slice_sound (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) m0W
    (view M mem0c) hrel
    prog 4 orcW orcC 72 entryWx K1W [] entryW_slice K1W_err
    (assumeOk_of (upd15 σ) K1W A0 K1W_assume (asm0ge (upd15 σ) hge))).1

/-! ## The exit segment: the loop head -> the tail call -/

/-- The exit slice's taken branch (`cmp rdx,4; jl` at pc 6). -/
def orcExitW : Nat → Bool := fun pc => decide (pc ∈ ([6] : List Nat))

/-- The exit cut: the x4 kernel's tail call into `hashtree_sha256_avx_x1`. -/
def K201W : State E Lin := abstract (run prog 4 m0W orcExitW 27 K200W)

/-- The environment at the W-mode exit cut. -/
def EFW (env : Key → W32) : Key → W32 :=
  envAbs (G200W (envAbs env (run prog 4 m0W (fun _ => false) 68 KHL2W)))
    (run prog 4 m0W orcExitW 27 K200W)

theorem exit27W : sliceCheck prog 4 m0W orcExitW 27 K200W K201W [] = true := by
  decide +kernel

/-- The exit cut's assume list (the pilot's `A1`; `Gen.AvxX4P.Final` is not in this module's
imports, so the list is spelled out). -/
def A1W : List (Cond Lin × Bool) :=
  [((.lt (⟨-4, [0, 0, 1]⟩ : Lin) (⟨4, []⟩ : Lin)), true),
   ((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨4, []⟩ : Lin)), false),
   ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]

theorem K201W_assume : K201W.assume = A1W := by decide +kernel
theorem K201W_err : K201W.err = none := by decide +kernel
theorem K201W_tail : K201W.tail = some "hashtree_sha256_avx_x1" := by decide +kernel
theorem K201W_rsp : K201W.getG 4 = .ptr ⟨rStack, sAt 0⟩ := by decide +kernel

/-- The exit cut's writes are output bytes or stack bytes below the return marker. -/
theorem K201W_logB : K201W.mem.all logOkBW = true := by decide +kernel

theorem outLogW_map_K201W (σ : Nat → Int) (e : Key → W32) :
    OutLogW σ (K201W.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have h : logOkBW q = true := List.all_eq_true.mp K201W_logB q hq
  by_cases h1 : q.1.region = rOut
  · exact Or.inl (by simpa [mapAddr] using h1)
  by_cases h2 : q.1.region = rStack
  · have hd : decide (q.1.off.c = stkC ∧ q.1.off.k < 0) = true := by
      rw [logOkBW, if_neg h1, if_pos h2] at h
      exact h
    obtain ⟨hc, hk⟩ := of_decide_eq_true hd
    refine Or.inr ⟨by simpa [mapAddr] using h2, ?_⟩
    have hoff : q.1.off.eval σ = q.1.off.k + σ 9 := eval_stk σ q.1.off hc
    show q.1.off.eval σ < σ 9
    rw [hoff]
    omega
  · exfalso
    rw [logOkBW, if_neg h1, if_neg h2] at h
    cases h

/-- The exit slice's conditions at any residual count in `[4, 8)`. -/
theorem asm1geW (σ : Nat → Int) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    ∀ p ∈ A1W, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A1W, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;>
    omega

/-- **The W-mode final segment** (unframed).  From the loop invariant head at a residual
count in `[4, 8)`, the 68-step head slice, the branch-free body slices and the 27-step exit
slice reach the exit cut `K201W`. -/
theorem final_runW_core (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (h0 : Mem0Rel env σ m0W mem0c) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    run prog 4 mem0c orcC ((68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27))) (mapState env σ KHL2W) =
      mapState (EFW env) σ K201W := by
  have kq : MemKeyed m0W := m0W_keyed
  have hHead := (slice_sound env σ m0W mem0c h0 prog 4 (fun _ => false)
    orcC 68 KHL2W K1W [] KHL2W_head KHL2W_err
    (assumeOk_of σ K1W A0 rfl (asm0ge σ hge))).1
  have hH : run prog 4 mem0c orcC 68 (mapState env σ KHL2W) =
      mapState (envAbs env (run prog 4 m0W (fun _ => false) 68 KHL2W)) σ K1W := hHead
  have hm : Mem0Rel (envAbs env (run prog 4 m0W (fun _ => false) 68 KHL2W)) σ m0W mem0c :=
    mem0Rel_envAbs env σ m0W mem0c kq h0 _
  have hB := body_runW (envAbs env (run prog 4 m0W (fun _ => false) 68 KHL2W)) σ
    mem0c orcC hm hge
  have hB' : run prog 4 mem0c orcC ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (mapState (envAbs env (run prog 4 m0W (fun _ => false) 68 KHL2W)) σ K1W) =
      mapState (G200W (envAbs env (run prog 4 m0W (fun _ => false) 68 KHL2W))) σ K200W := hB
  have hm2 := body_memW (envAbs env (run prog 4 m0W (fun _ => false) 68 KHL2W)) σ mem0c hm
  have hExit := (slice_sound (G200W (envAbs env (run prog 4 m0W (fun _ => false) 68 KHL2W)))
    σ m0W mem0c hm2 prog 4 orcExitW orcC 27 K200W K201W [] exit27W K200W_err
    (assumeOk_of σ K201W A1W K201W_assume (asm1geW σ hge hlt))).1
  rw [run_add, run_add, hH, hB']
  exact hExit

/-- **The W-mode final segment, behind the caller's log.**  The incoming environment is read
through the log (`ecomb`), so the caller's earlier writes are honoured; the run leaves a
known environment `EFW` and appends the exit cut's own writes to the log. -/
theorem final_runW (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (σ0 : Nat → Int) (hw : WfMemW rodata [] env σ0 mem0c)
    (h9 : σ 9 = σ0 9) (M : CLog) (hM : OutLogW σ M) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    ∃ e', run prog 4 mem0c orcC ((68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27))) (fr M (mapState env σ KHL2W)) =
        fr M (mapState e' σ K201W) ∧
      OutLogW σ (K201W.mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  let E := ecomb env σ (view M mem0c)
  have kq : MemKeyed m0W := m0W_keyed
  have hrel : Mem0Rel E σ m0W (view M mem0c) := by
    rw [m0W_eq]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c)
      (wfW_view rodata env E σ mem0c M hM (wfMemW_s9 rodata env σ0 σ mem0c hw h9))
      (envMem_ecomb E σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC ((68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27))) (fr M (mapState env σ KHL2W)) =
      fr M (mapState (EFW E) σ K201W) := by
    rw [run_fr, mapState_nOnly env E σ (fun _ => rfl) KHL2W KHL2W_nOnly]
    exact congrArg (fr M) (final_runW_core E σ (view M mem0c) orcC hrel hge hlt)
  refine ⟨EFW E, hrun, outLogW_app σ ?_ hM⟩
  exact outLogW_map_K201W σ (EFW E)

end Hashtree.Proofs.AvxX4LoopWExit
