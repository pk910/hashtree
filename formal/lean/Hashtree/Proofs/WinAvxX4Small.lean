import Hashtree.Proofs.WinAvxX4WShift
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.AvxX4
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinAvxX4W (m0W m0W_eq entryWin_err)

/-!
# The windows `avx_x4` kernel at the wrapper call state, counts 1-3

For `0 < c < 4` the windows kernel takes the early exit: `nop; cmp r8,0; jne`, `sub rsp,568`,
the ten `xmm6..15` saves, `cmp r8,4; jl` taken, the ten restores, `add rsp,568` and the tail
call into `hashtree_sha256_avx_x1` (28 instructions).  `small_prefixW` states the run as one
kernel-checked symbolic slice from `entryWin`; the cut `KSmW` has the wrapper call state's
general registers, a 32 x 16 vector file, the 160 saved bytes in its log, and the x1 tail recorded.
-/

namespace Hashtree.Proofs.WinAvxX4Small

/-- The two taken branches of the early exit: `jne` at pc 2 and `jl` at pc 16. -/
def orcK : Nat → Bool := fun pc => decide (pc ∈ ([2, 16] : List Nat))

/-- The cut at the `jmpTail ...avx_x1` instruction after the early exit. -/
def KSmW : State E Lin := abstract (run prog 4 m0W orcK 28 entryWin)

/-- The early exit's recorded conditions: `c < 4` and `c ≠ 0`. -/
def ASm : List (Cond Lin × Bool) :=
  [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨4, []⟩ : Lin)), true),
   ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]

/-- The early-exit facts, one kernel evaluation. -/
def smallOk : Bool :=
  sliceCheck prog 4 m0W orcK 28 entryWin KSmW [] &&
  decide (KSmW.pc = 4162) && decide (KSmW.err = none) && decide (KSmW.halted = true) &&
  decide (KSmW.tail = some "hashtree_sha256_avx_x1") && decide (KSmW.assume = ASm) &&
  decide (KSmW.gpr = entryWin.gpr) && decide (KSmW.vr.length = 32) &&
  KSmW.vr.all (fun v => v.length == 16)

theorem smallOk_true : smallOk = true := by decide +kernel

theorem smallFacts :
    sliceCheck prog 4 m0W orcK 28 entryWin KSmW [] = true ∧ KSmW.pc = 4162 ∧ KSmW.err = none ∧
      KSmW.halted = true ∧ KSmW.tail = some "hashtree_sha256_avx_x1" ∧ KSmW.assume = ASm ∧
      KSmW.gpr = entryWin.gpr ∧ KSmW.vr.length = 32 ∧ (∀ v ∈ KSmW.vr, v.length = 16) := by
  have h := smallOk_true
  simp only [smallOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j⟩

theorem asmSm (σ : Nat → Int) (hlt : σ 2 < 4) (hne : σ 2 ≠ 0) :
    ∀ p ∈ ASm, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [ASm, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]; omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, hne, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]

theorem KSmW_assumeOk (σ : Nat → Int) (hlt : σ 2 < 4) (hne : σ 2 ≠ 0) : AssumeOk σ KSmW := by
  unfold AssumeOk
  rw [smallFacts.2.2.2.2.2.1]
  exact asmSm σ hlt hne

/-- **Counts 1-3 (windows)**: 28 instructions from the wrapper call state reach the tail call into
`avx_x1` at the cut `KSmW` (wrapper call registers, the saved `xmm6..15` bytes in the log). -/
theorem small_prefixW (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMemW rodata [] env0 σ mem0c) (he : EnvMem env0 σ mem0c)
    (hlt : σ 2 < 4) (hne : σ 2 ≠ 0) :
    run prog 4 mem0c orcC 28 (mapState env0 σ entryWin) =
      mapState (envAbs env0 (run prog 4 m0W orcK 28 entryWin)) σ KSmW := by
  have h0 : Mem0Rel env0 σ m0W mem0c := by
    rw [m0W_eq]; exact mem0RelW_of_wf rodata [] env0 σ mem0c hw he
  exact (slice_sound env0 σ m0W mem0c h0 prog 4 orcK orcC 28 entryWin KSmW []
    smallFacts.1 entryWin_err (KSmW_assumeOk σ hlt hne)).1

end Hashtree.Proofs.WinAvxX4Small
