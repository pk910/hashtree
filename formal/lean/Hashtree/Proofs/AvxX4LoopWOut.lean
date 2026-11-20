import Hashtree.Proofs.AvxX4LoopWOutTail
import Hashtree.Proofs.AvxX4LoopWAll
import Hashtree.Proofs.AvxX4Exit

/-!
# R2c — output correctness of the `avx_x4` W-mode loop (`TurnOut4`)

Same route as `Avx512X16WOut`: the pilot's invariant chain (`Gen.AvxX4P`) is lifted to R2's W
cuts (`AvxX4LoopWOutInv`, the W slices re-checked with the pilot's trees in
`AvxX4LoopWOutChk*`), one turn's log is output cells of its 4 blocks plus the kernel's own stack
frame (`outShape4`), the digests come from the invariant at `L201` (`outOk_KHpW` / `outOk_K201W`),
and the turns compose along `AvxX4LoopWAll.x4_runW`: entry pass (72 + body + 23), `j` framed
turns (`TURNLEN` each), final pass (68 + body + 27).  `TurnOut4` and `x4RunSteps` are R5's text
(`WinAvxX4Bridge`), copied verbatim.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.AvxX4 Hashtree.Gen.AvxX4P
open Hashtree.Proofs.AvxX4W Hashtree.Proofs.AvxX4LoopW Hashtree.Proofs.AvxX4LoopWExit
open Hashtree.Proofs.AvxX4LoopWFrame Hashtree.Proofs.AvxX4LoopWAll Hashtree.Proofs.AvxX4LoopFrame
open Hashtree.Proofs.AvxX4LoopTurn (tau asm0ge)
open Hashtree.Proofs.Avx512X16WOut (OutOk lookup_none outOk_append_left outOk_step' outOk_glue'
  hmem_of_envMem)

namespace Hashtree.Proofs.AvxX4LoopWOut

/-! ## The statement (R5's `WinAvxX4Bridge.x4RunSteps` / `TurnOut4`, verbatim) -/

def x4RunSteps (j : Nat) : Nat := ((72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)) + j * Hashtree.Proofs.AvxX4LoopFrame.TURNLEN) + (68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27))

def TurnOut4 : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (j s : Nat) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c →
    Hashtree.Proofs.AvxX4LoopWFrame.OutLogW σ M → 4 ≤ s → s < 8 →
    σ 2 = 4 * ((j : Int) + 1) + (s : Int) →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4RunSteps j)
        (fr M (mapState env0 σ entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 128 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (4 * (j + 2))
      (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (x4RunSteps j)
        (fr M (mapState env0 σ entryW))).mem

/-- The run `TurnOut4` speaks about is the run of `x4_runW` (the literal is the same). -/
theorem x4RunSteps_eq (j : Nat) : x4RunSteps j = ((72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)) + j * Hashtree.Proofs.AvxX4LoopFrame.TURNLEN) + (68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)) := rfl


/-! ## Symbols -/

theorem upd15_0 (σ : Nat → Int) : upd15 σ 0 = σ 0 := by simp [upd15]
theorem upd15_1 (σ : Nat → Int) : upd15 σ 1 = σ 1 := by simp [upd15]
theorem upd15_2 (σ : Nat → Int) : upd15 σ 2 = σ 2 := by simp [upd15]

theorem tau_in4 (σ : Nat → Int) : sigmaOf tau σ 0 = σ 0 + 256 := by
  have h := Hashtree.Proofs.AvxX4Exit.sIt_0 1 σ
  simpa [sIt] using h

theorem tau_out4 (σ : Nat → Int) : sigmaOf tau σ 1 = σ 1 + 128 := by
  have h := Hashtree.Proofs.AvxX4Exit.sIt_1 1 σ
  simpa [sIt] using h

theorem sIt_in4 (j : Nat) (σ : Nat → Int) : sIt j σ 0 = σ 0 + 256 * (j : Int) :=
  Hashtree.Proofs.AvxX4Exit.sIt_0 j σ
theorem sIt_out4 (j : Nat) (σ : Nat → Int) : sIt j σ 1 = σ 1 + 128 * (j : Int) :=
  Hashtree.Proofs.AvxX4Exit.sIt_1 j σ

/-! ## Input bytes through the frame -/

/-- An `OutLogW` log never writes the input region. -/
theorem view_rIn_W (M : CLog) (m : Addr Int → Cell W32 Int) (σ : Nat → Int) (a : Int)
    (hM : OutLogW σ M) : view M m ⟨rIn, a⟩ = m ⟨rIn, a⟩ := by
  have hn : lookup (⟨rIn, a⟩ : Addr Int) M = .ok none := by
    refine lookup_none _ M ?_
    intro p hp heq
    rcases hM p hp with h | ⟨h, _⟩
    · rw [heq] at h; simp [rIn, rOut] at h
    · rw [heq] at h; simp [rIn, rStack] at h
  simp only [view, hn]

theorem hmem_viewW (e : Key → W32) (σ : Nat → Int) (M : CLog) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (hM : OutLogW σ M)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    HMem 256 inp (ecomb e σ (view M m)) :=
  hmem_of_envMem _ σ _ inp 256 (envMem_ecomb e σ (view M m))
    (fun o => by rw [view_rIn_W M m σ _ hM]; exact hin o)

/-- The wrapper environment of the entry pass reads the concrete memory behind the caller's log. -/
theorem hmem_envM (e : Key → W32) (σ : Nat → Int) (M : CLog) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (hM : OutLogW σ M)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    HMem 256 inp (envM e (view M m) (upd15 σ)) :=
  hmem_of_envMem _ (upd15 σ) _ inp 256 (envMem_envM_upd15 e (view M m) σ)
    (fun o => by rw [upd15_0, view_rIn_W M m σ _ hM]; exact hin o)

theorem hin_tau4 (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) (inp : Nat → Byte)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ o : Nat, mem0c ⟨rIn, sigmaOf tau σ 0 + o⟩ = .dat ((inp (256 + o)).zeroExtend 32) 0 := by
  intro o
  rw [tau_in4, show σ 0 + 256 + (o : Int) = σ 0 + ((256 + o : Nat) : Int) by push_cast; omega]
  exact hin (256 + o)

theorem hin_sIt4 (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) (inp : Nat → Byte) (j : Nat)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ o : Nat, mem0c ⟨rIn, sIt j σ 0 + o⟩ = .dat ((inp (256 * j + o)).zeroExtend 32) 0 := by
  intro o
  rw [sIt_in4, show σ 0 + 256 * (j : Int) + (o : Int) = σ 0 + ((256 * j + o : Nat) : Int) by
    push_cast; omega]
  exact hin (256 * j + o)

/-- The shape predicate of one turn's cells, relative to a symbol valuation. -/
def Cells (σ : Nat → Int) (lo : Int) (n : Int) (N : CLog) : Prop :=
  ∀ p ∈ N, (p.1.region = rOut ∧ lo ≤ p.1.off ∧ p.1.off < lo + n) ∨
    (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)

theorem outLogW_of_cells (σ : Nat → Int) (lo n : Int) (N : CLog) (h : Cells σ lo n N) :
    OutLogW σ N := by
  intro p hp
  rcases h p hp with ⟨h1, _⟩ | ⟨h1, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h3⟩

/-! ## One turn, with its output -/

/-- A framed loop turn (mirrors `iter_stepW`): the new log is the turn's own cells, the output
cells `[σ 1, σ 1 + 128)` hold the 4 digests of the blocks at the input pointer. -/
theorem iter_out4 (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env : Key → W32) (σ0 : Nat → Int) (σ : Nat → Int)
    (hw : WfMemW rodata [] env σ0 mem0c) (h9 : σ 9 = σ0 9)
    (e : Key → W32) (M : CLog) (inp : Nat → Byte)
    (hM : OutLogW σ M) (hge : 4 ≤ σ 2)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e' N,
      run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHL2W)) =
          fr (N ++ M) (mapState e' (sigmaOf tau σ) KHL2W) ∧
        Cells σ (σ 1) 128 N ∧ OutOk inp (σ 1) 4 N := by
  let E := ecomb e σ (view M mem0c)
  have hrel : Mem0Rel E σ m0W (view M mem0c) := by
    rw [m0W_eq]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c)
      (wfW_view rodata env E σ mem0c M hM
        (wfMemW_s9 rodata env σ0 σ mem0c hw h9)) (envMem_ecomb E σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHL2W)) =
      fr M (mapState (turnEW E) σ KHpW) := by
    rw [run_fr]
    rw [mapState_nOnly e E σ (fun _ => rfl) KHL2W KHL2W_nOnly]
    exact congrArg (fr M) (turn_runW E σ (view M mem0c) orcC hrel hge)
  have hmE : HMem 256 inp E := hmem_viewW e σ M mem0c inp hM hin
  have hI : InvC inp (turnEW E) L201 :=
    stepW4_turn inp (G200W (envAbs E (run prog 4 m0W (fun _ => false) 68 KHL2W)))
      (invW4_body inp (envAbs E (run prog 4 m0W (fun _ => false) 68 KHL2W))
        (stepW4_head inp E hmE) hmE) hmE
  refine ⟨turnEW E, KHpW.mem.map (fun p => (mapAddr σ p.1, mapCell (turnEW E) σ p.2)), ?_, ?_, ?_⟩
  · rw [hrun, turn_stepW (turnEW E) σ]
    simp only [fr, List.append_assoc]
  · exact outShape4_sound KHpW KHpW_outShape4 (turnEW E) σ
  · exact outOk_KHpW inp (turnEW E) σ hI

/-- The final pass (mirrors `final_runW`): head, body and the exit tail into `K201W`, whose own
cells are the turn's output and stack cells. -/
theorem final_out4 (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (σ0 : Nat → Int) (hw : WfMemW rodata [] env σ0 mem0c)
    (h9 : σ 9 = σ0 9) (M : CLog) (inp : Nat → Byte) (hM : OutLogW σ M) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e',
      run prog 4 mem0c orcC (68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)) (fr M (mapState env σ KHL2W)) =
          fr M (mapState e' σ K201W) ∧
        Cells σ (σ 1) 128 (mapState e' σ K201W).mem ∧ OutOk inp (σ 1) 4 (mapState e' σ K201W).mem := by
  let E := ecomb env σ (view M mem0c)
  have hrel : Mem0Rel E σ m0W (view M mem0c) := by
    rw [m0W_eq]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c)
      (wfW_view rodata env E σ mem0c M hM (wfMemW_s9 rodata env σ0 σ mem0c hw h9))
      (envMem_ecomb E σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC (68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)) (fr M (mapState env σ KHL2W)) =
      fr M (mapState (EFW E) σ K201W) := by
    rw [run_fr, mapState_nOnly env E σ (fun _ => rfl) KHL2W KHL2W_nOnly]
    exact congrArg (fr M) (final_runW_core E σ (view M mem0c) orcC hrel hge hlt)
  have hmE : HMem 256 inp E := hmem_viewW env σ M mem0c inp hM hin
  have hI : InvC inp (EFW E) L201 :=
    stepW4_exit inp (G200W (envAbs E (run prog 4 m0W (fun _ => false) 68 KHL2W)))
      (invW4_body inp (envAbs E (run prog 4 m0W (fun _ => false) 68 KHL2W))
        (stepW4_head inp E hmE) hmE) hmE
  exact ⟨EFW E, hrun, outShape4_sound K201W K201W_outShape4 (EFW E) σ, outOk_K201W inp (EFW E) σ hI⟩

/-! ## The turns -/

theorem loop_out4 (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env : Key → W32) (σ0 : Nat → Int) (hw : WfMemW rodata [] env σ0 mem0c)
    (s : Nat) (hs : 4 ≤ s) (hs8 : s < 8) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog) (inp : Nat → Byte),
      σ 2 = 4 * (j : Int) + (s : Int) → σ 9 = σ0 9 → OutLogW σ M →
      (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
      ∃ e' N,
        run prog 4 mem0c orcC (j * TURNLEN) (fr M (mapState e σ KHL2W)) =
            fr (N ++ M) (mapState e' (sIt j σ) KHL2W) ∧
          Cells σ (σ 1) (128 * (j : Int)) N ∧ OutOk inp (σ 1) (4 * j) N := by
  intro j
  induction j with
  | zero =>
    intro e σ M inp hσ h9 hM hin
    refine ⟨e, [], rfl, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro n i b hn
      exact absurd hn (Nat.not_lt_zero n)
  | succ j ih =>
    intro e σ M inp hσ h9 hM hin
    have hge : 4 ≤ σ 2 := by
      rw [hσ]
      have hsj : (0 : Int) ≤ (s : Int) := by exact_mod_cast (Nat.zero_le s)
      push_cast
      omega
    obtain ⟨e1, N1, hrun, hsh1, hout1⟩ := iter_out4 mem0c orcC env σ0 σ hw h9 e M inp hM hge hin
    have hσ1 : sigmaOf tau σ 2 = 4 * (j : Int) + (s : Int) := by
      rw [tau_count, hσ]
      push_cast
      omega
    have h9' : sigmaOf tau σ 9 = σ0 9 := by rw [tau_s9]; exact h9
    have hM1 : OutLogW (sigmaOf tau σ) (N1 ++ M) :=
      outLogW_app _ (outLogW_s9 N1 (tau_s9 σ) (outLogW_of_cells σ _ _ N1 hsh1))
        (outLogW_s9 M (tau_s9 σ) hM)
    obtain ⟨e2, N2, hrun2, hsh2, hout2⟩ :=
      ih e1 (sigmaOf tau σ) (N1 ++ M) (fun o => inp (256 + o)) hσ1 h9' hM1 (hin_tau4 mem0c σ inp hin)
    refine ⟨e2, N2 ++ N1, ?_, ?_, ?_⟩
    · have hlen : (j + 1) * TURNLEN = TURNLEN + j * TURNLEN := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [hlen, run_add, hrun, hrun2, List.append_assoc]
      rfl
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · rcases hsh2 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rw [tau_out4] at h2 h3
          left; refine ⟨h1, ?_, ?_⟩ <;> push_cast <;> omega
        · rw [tau_s9] at h2 h3
          right; exact ⟨h1, h2, h3⟩
      · rcases hsh1 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · left; refine ⟨h1, ?_, ?_⟩ <;> push_cast <;> omega
        · right; exact ⟨h1, h2, h3⟩
    · rw [show 4 * (j + 1) = 4 + 4 * j by omega]
      refine outOk_glue' inp (σ 1) 4 (4 * j) N2 N1 ?_ hout1 ?_
      · intro p hp hr
        rcases hsh2 p hp with ⟨_, h2, _⟩ | ⟨h1, _, _⟩
        · rw [tau_out4] at h2; push_cast; omega
        · rw [hr] at h1; simp [rOut, rStack] at h1
      · rw [tau_out4] at hout2
        have : (σ 1 + 128 : Int) = σ 1 + 32 * ((4 : Nat) : Int) := by push_cast; omega
        rw [this] at hout2
        exact hout2

/-! ## From the entry -/

/-- **`TurnOut4`.** -/
theorem turnOut4 : TurnOut4 := by
  intro env0 σ mem0c orcC M j s inp hw hM hs hs8 hc hin
  -- the entry pass (mirrors `x4_runW`)
  let σ15 : Nat → Int := upd15 σ
  let σ1 : Nat → Int := sigmaOf tau (upd15 σ)
  let E1 : Key → W32 := envM env0 (view M mem0c) (upd15 σ)
  let e1 : Key → W32 := envAbs (G200W (envAbs E1 (run prog 4 m0W orcW 72 entryWx)))
    (run prog 4 m0W (fun _ => false) 23 K200W)
  have hM15 : OutLogW (upd15 σ) M := outLogW_s9 M (upd15_9 σ) hM
  have hs4 : (4 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hc15 : upd15 σ 2 = 4 * ((j : Int) + 1) + (s : Int) := by rw [upd15_2]; exact hc
  have hge15 : 4 ≤ upd15 σ 2 := by rw [hc15]; omega
  have hentry := entry_runW env0 σ mem0c orcC M hw hge15 hM15
  have hrel1 : Mem0Rel (G1W (envAbs E1 (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) m0W
      (view M mem0c) := entry_relW env0 σ mem0c M hw hM
  have hbody := body_runW (envAbs E1 (run prog 4 m0W orcW 72 entryWx)) (upd15 σ) (view M mem0c)
    orcC hrel1 hge15
  have hm2 := body_memW (envAbs E1 (run prog 4 m0W orcW 72 entryWx)) (upd15 σ) (view M mem0c) hrel1
  have htail := (slice_sound (G200W (envAbs E1 (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) m0W
    (view M mem0c) hm2 prog 4 (fun _ => false) orcC 23 K200W KHpW [] KHpW_slice K200W_err
    (assumeOk_of (upd15 σ) KHpW A0 KHpW_assume (asm0ge (upd15 σ) hge15))).1
  obtain ⟨N1, hN1⟩ : ∃ N1 : CLog,
      N1 = KHpW.mem.map (fun p => (mapAddr (upd15 σ) p.1, mapCell e1 (upd15 σ) p.2)) := ⟨_, rfl⟩
  have hMB : run prog 4 mem0c orcC ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)
      (fr M (mapState (G1W (envAbs E1 (run prog 4 m0W orcW 72 entryWx))) (upd15 σ) K1W)) =
      fr (N1 ++ M) (mapState e1 σ1 KHL2W) := by
    rw [run_fr, run_add, hbody, htail, turn_stepW e1 (upd15 σ), hN1]
    simp only [fr, List.append_assoc, σ1]
  -- the entry pass's invariant and output
  have hmE1 : HMem 256 inp E1 := hmem_envM env0 σ M mem0c inp hM hin
  have hI1 : InvC inp e1 L201 :=
    stepW4_turn inp (G200W (envAbs E1 (run prog 4 m0W orcW 72 entryWx)))
      (invW4_body inp (envAbs E1 (run prog 4 m0W orcW 72 entryWx)) (stepW4_entry inp E1 hmE1) hmE1) hmE1
  have hsh1 : Cells (upd15 σ) (σ 1) 128 N1 := by
    rw [hN1]
    have h := outShape4_sound KHpW KHpW_outShape4 e1 (upd15 σ)
    rw [upd15_1] at h
    exact h
  have hout1 : OutOk inp (σ 1) 4 N1 := by
    rw [hN1]
    have h := outOk_KHpW inp e1 (upd15 σ) hI1
    rw [upd15_1] at h
    exact h
  -- the loop
  have hM1 : OutLogW σ1 (N1 ++ M) :=
    outLogW_s9 _ (tau_s9 (upd15 σ)) (outLogW_app (upd15 σ) (outLogW_of_cells _ _ _ N1 hsh1) hM15)
  have hrelW15 : WfMemW rodata [] env0 (upd15 σ) mem0c := wfMemW_upd15 rodata env0 env0 σ mem0c hw
  have hwbase : WfMemW rodata [] e1 σ1 mem0c :=
    wfMemW_env rodata env0 e1 σ1 mem0c (wfMemW_s9 rodata env0 (upd15 σ) σ1 mem0c hrelW15 (tau_s9 (upd15 σ)))
  have hcount : σ1 2 = 4 * (j : Int) + (s : Int) := by
    show sigmaOf tau (upd15 σ) 2 = 4 * (j : Int) + (s : Int)
    rw [tau_count, hc15]
    omega
  have hin1 : ∀ o : Nat, mem0c ⟨rIn, σ1 0 + o⟩ = .dat ((inp (256 + o)).zeroExtend 32) 0 := by
    intro o
    show mem0c ⟨rIn, sigmaOf tau (upd15 σ) 0 + o⟩ = _
    rw [tau_in4, upd15_0, show σ 0 + 256 + (o : Int) = σ 0 + ((256 + o : Nat) : Int) by push_cast; omega]
    exact hin (256 + o)
  obtain ⟨e2, N2, hloop, hsh2, hout2⟩ :=
    loop_out4 mem0c orcC e1 σ1 hwbase s hs hs8 j e1 σ1 (N1 ++ M) (fun o => inp (256 + o))
      hcount rfl hM1 hin1
  -- the final pass
  obtain ⟨σ2, hσ2def⟩ : ∃ σ2 : Nat → Int, σ2 = sIt j σ1 := ⟨_, rfl⟩
  rw [← hσ2def] at hloop
  have hσ2_2 : σ2 2 = (s : Int) := by rw [hσ2def, sIt_2W, hcount]; omega
  have hge2 : 4 ≤ σ2 2 := by rw [hσ2_2]; omega
  have hlt2 : σ2 2 < 8 := by rw [hσ2_2]; omega
  have h9_2 : σ2 9 = σ1 9 := by rw [hσ2def]; exact sIt_s9 j σ1
  have hwfin : WfMemW rodata [] e2 σ1 mem0c := wfMemW_env rodata e1 e2 σ1 mem0c hwbase
  have hM2 : OutLogW σ2 (N2 ++ (N1 ++ M)) :=
    outLogW_s9 _ h9_2 (outLogW_app σ1 (outLogW_of_cells _ _ _ N2 hsh2) hM1)
  have hin2 : ∀ o : Nat, mem0c ⟨rIn, σ2 0 + o⟩ = .dat ((inp (256 * (j + 1) + o)).zeroExtend 32) 0 := by
    intro o
    rw [hσ2def, sIt_in4]
    show mem0c ⟨rIn, sigmaOf tau (upd15 σ) 0 + 256 * (j : Int) + o⟩ = _
    rw [tau_in4, upd15_0, show σ 0 + 256 + 256 * (j : Int) + (o : Int) = σ 0 + ((256 * (j + 1) + o : Nat) : Int) by
      push_cast; omega]
    exact hin _
  obtain ⟨e3, hfin, hsh3, hout3⟩ :=
    final_out4 e2 σ2 mem0c orcC σ1 hwfin h9_2 (N2 ++ (N1 ++ M)) (fun o => inp (256 * (j + 1) + o))
      hM2 hge2 hlt2 hin2
  -- the whole run
  have hall : run prog 4 mem0c orcC (x4RunSteps j) (fr M (mapState env0 σ entryW)) =
      fr (N2 ++ (N1 ++ M)) (mapState e3 σ2 K201W) := by
    show run prog 4 mem0c orcC (((72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)) + j * TURNLEN) + (68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)))
      (fr M (mapState env0 σ entryW)) = _
    have sA := run_add prog 4 mem0c orcC ((72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)) + j * TURNLEN) (68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27))
      (fr M (mapState env0 σ entryW))
    have sB := run_add prog 4 mem0c orcC (72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)) (j * TURNLEN)
      (fr M (mapState env0 σ entryW))
    have sC := run_add prog 4 mem0c orcC 72 ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)
      (fr M (mapState env0 σ entryW))
    rw [sA, sB, sC, hentry, hMB, hloop]
    exact hfin
  -- symbols of the final cut
  have hσ2_1 : σ2 1 = σ 1 + 128 * ((j + 1 : Nat) : Int) := by
    rw [hσ2def, sIt_out4]
    show sigmaOf tau (upd15 σ) 1 + 128 * (j : Int) = _
    rw [tau_out4, upd15_1]
    push_cast
    omega
  have hσ1_1 : σ1 1 = σ 1 + 128 := by
    show sigmaOf tau (upd15 σ) 1 = _
    rw [tau_out4, upd15_1]
  have hσ2_9 : σ2 9 = σ 9 := by rw [h9_2]; show sigmaOf tau (upd15 σ) 9 = σ 9; rw [tau_s9, upd15_9]
  have hσ1_9 : σ1 9 = σ 9 := by show sigmaOf tau (upd15 σ) 9 = σ 9; rw [tau_s9, upd15_9]
  have hσ15_9 : upd15 σ 9 = σ 9 := upd15_9 σ
  rw [hall]
  show (∀ p ∈ (mapState e3 σ2 K201W).mem ++ (N2 ++ (N1 ++ M)), _) ∧
    OutOk inp (σ 1) (4 * (j + 2)) ((mapState e3 σ2 K201W).mem ++ (N2 ++ (N1 ++ M)))
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · rcases hsh3 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [hσ2_1] at h2 h3
        right; left; refine ⟨h1, ?_, ?_⟩ <;> push_cast at h2 h3 ⊢ <;> omega
      · rw [hσ2_9] at h2 h3
        right; right; exact ⟨h1, h2, h3⟩
    · rcases List.mem_append.mp h with h | h
      · rcases hsh2 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rw [hσ1_1] at h2 h3
          right; left; refine ⟨h1, ?_, ?_⟩ <;> push_cast at h3 ⊢ <;> omega
        · rw [hσ1_9] at h2 h3
          right; right; exact ⟨h1, h2, h3⟩
      · rcases List.mem_append.mp h with h | h
        · rcases hsh1 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · right; left; refine ⟨h1, ?_, ?_⟩ <;> push_cast <;> omega
          · rw [hσ15_9] at h2 h3
            right; right; exact ⟨h1, h2, h3⟩
        · left; exact h
  · have hlow : OutOk inp (σ 1) (4 * (j + 1)) (N2 ++ (N1 ++ M)) := by
      rw [show 4 * (j + 1) = 4 + 4 * j by omega]
      refine outOk_glue' inp (σ 1) 4 (4 * j) N2 (N1 ++ M) ?_ (outOk_append_left inp (σ 1) 4 N1 M hout1) ?_
      · intro p hp hr
        rcases hsh2 p hp with ⟨_, h2, _⟩ | ⟨h1, _, _⟩
        · rw [hσ1_1] at h2; push_cast; omega
        · rw [hr] at h1; simp [rOut, rStack] at h1
      · rw [hσ1_1] at hout2
        have : (σ 1 + 128 : Int) = σ 1 + 32 * ((4 : Nat) : Int) := by push_cast; omega
        rw [this] at hout2
        exact hout2
    rw [show 4 * (j + 2) = 4 * (j + 1) + 4 by omega]
    refine outOk_step' inp (σ 1) (4 * (j + 1)) 4 _ (N2 ++ (N1 ++ M)) ?_ hlow ?_
    · intro p hp hr
      rcases hsh3 p hp with ⟨_, h2, _⟩ | ⟨h1, _, _⟩
      · rw [hσ2_1] at h2; push_cast at h2 ⊢; omega
      · rw [hr] at h1; simp [rOut, rStack] at h1
    · rw [hσ2_1] at hout3
      have : (σ 1 + 128 * ((j + 1 : Nat) : Int) : Int) = σ 1 + 32 * ((4 * (j + 1) : Nat) : Int) := by
        push_cast; omega
      rw [this] at hout3
      have h64 : (fun o => inp (256 * (j + 1) + o)) = (fun o => inp (64 * (4 * (j + 1)) + o)) := by
        funext o; exact congrArg inp (by omega)
      rw [h64] at hout3
      exact hout3

end Hashtree.Proofs.AvxX4LoopWOut
