import Hashtree.Gen.Avx2X8P.Ro
import Hashtree.Asm.Slice
import Hashtree.Asm.Chain
import Hashtree.Proofs.WrapperPre
import Hashtree.Proofs.AvxX4WPrep
import Hashtree.Proofs.AvxX4LoopWFrame
import Hashtree.Proofs.X86Chain
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.Avx2X8
open Hashtree.Gen.Avx2X8P (roC roC_eq)
open Hashtree.Proofs.AvxX4W (entryWx upd15 envM mapState_entryW wfMemW_upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW logOkBW wfW_view)
open Hashtree.Proofs.X86Chain (resume)

/-!
# The `avx2_x8` kernel at the wrapper's call state: the stack alignment

`avx2_x8` builds its frame with `push rbp; mov rbp,rsp; and rsp,-32; sub rsp,928`.  At the
wrapper's call state `entryW` the stack pointer is the symbolic `sAt 0` (the return marker is
at `σ 9`), so after the `push` it is `sAt (-8) = ⟨-8, stkC⟩`, and the symbolic executor cannot
evaluate `and rsp,-32` on it: `Lin.asInt` is `none` on a non-constant offset and the `.alu .and`
case of `exec` throws `"and on symbolic pointer"` (`Hashtree/Asm/X86.lean`).  The fixed-count
pilot never meets this because its stack pointer is the constant `24`.

The treatment here is the one the wrapper proof already uses for the wrapper's own
`ANDQ $-32, SP` (`WrapperPre.align_hom`, and R5's `align_homW` on windows): the alignment is
executed *concretely*.  The concrete state `mapState env σ x8P` has `rsp = ⟨rStack, σ 9 - 8⟩`,
an integer, on which `andInt` is total; the result `(σ 9 - 8) - (σ 9 - 8) % 32` is written as
`σ 9 - 8 - r` with the residue `r = (σ 9 - 8) % 32`, and the symbolic cut after the alignment is
`x8A r`, whose stack pointer is `sAt (-8 - r)` -- still relative to the single stack symbol
`9`, so every later stack address keeps a constant offset and the symbolic memory stays
decidable (`AddrEq Lin` decides addresses by the difference of their offsets; a second stack
symbol would make every lookup past the pushed `rbp` fail with `"may alias"`).  Nothing is
assumed about the stack base beyond what the caller gives: the residue is a parameter, and
the segments after the alignment are checked in the kernel for every residue `0 ≤ r < 32`.

* `align_hom8`: `exec` of `and rsp,-32` at `mapState env σ x8P` is `mapState env σ (x8A r)`
  for `r = (σ 9 - 8) % 32`; `run1_align` is the same as a one-step run.
* `smOk_all`: the small path `0 < c < 8` (`sub rsp,928`, the four saves, `cmp rdx,8`, `jb`
  taken, the four restores, `mov rsp,rbp; pop rbp`, `jmp avx_x4`) re-checks from `x8A r` at
  every residue, and its cut `x8Sm r` has the entry register file back (`gpr = entryWx.gpr`,
  `vr = entryWx.vr`, `rsp = sAt 0`), the tail `hashtree_sha256_avx_x4`, and a log of 40 pointer
  bytes below the return marker (`logOkBW`).
* `x8_small_run`: the composition from `fr M (mapState env0 σ entryW)` at the wrapper state:
  20 instructions reach `fr M (mapState e' (upd15 σ) (x8Sm r))`.
* `x8Sm_resume`: the resumed cut is the x4 entry state `entryWx` (i.e. `entryW`) up to flags,
  behind the small path's log -- the shape the x4 W-mode link takes.
* `residue_abi`: with the ABI fact the wrapper provides (`σ 9 ≡ 8 (mod 16)`: the Go wrapper
  aligns to 32 and the `CALL` pushes 8), the residue is `0` or `16`.
-/

namespace Hashtree.Proofs.Avx2X8Align

/-- The wrapper-call symbolic memory of the x8 kernel: its table in region 4, nothing pushed. -/
def m8 : Addr Lin → Cell E Lin := mem0qW 4 roC []

theorem m8_eq : m8 = mem0sW 4 rodata [] :=
  mem0qW_eq 4 rodata [] roC 69 roC_eq (by decide +kernel)

theorem m8_keyed : MemKeyed m8 :=
  mem0qW_keyed 4 rodata [] roC 69 roC_eq (by decide +kernel) (by decide +kernel)

/-! ## The prologue: five instructions to the alignment -/

/-- `jne` at pc 2 taken (count nonzero). -/
def orcNZ : Nat → Bool := fun pc => decide (pc ∈ ([2] : List Nat))

/-- The cut at `and rsp,-32`: `nop; cmp rdx,0; jne` (taken); `push rbp; mov rbp,rsp`. -/
def x8P : State E Lin := abstract (run prog 4 m8 orcNZ 5 entryWx)

theorem sliceP : sliceCheck prog 4 m8 orcNZ 5 entryWx x8P [] = true := by decide +kernel
theorem x8P_pc : x8P.pc = 6 := by decide +kernel
theorem x8P_halted : x8P.halted = false := by decide +kernel
theorem x8P_err : x8P.err = none := by decide +kernel
theorem x8P_rsp : x8P.gpr[4]? = some (.ptr ⟨rStack, sAt (-8)⟩) := by decide +kernel
theorem entryWx_err : entryWx.err = none := rfl
theorem entryWx_pc : entryWx.pc = 0 := rfl
theorem entryWx_halted : entryWx.halted = false := rfl
theorem entryWx_tail : entryWx.tail = none := rfl
theorem entryWx_mem : entryWx.mem = [] := rfl
theorem entryWx_assume : entryWx.assume = [] := rfl

/-- The prologue's recorded condition: the count is nonzero. -/
def A1nz : List (Cond Lin × Bool) :=
  [((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]

theorem x8P_assume : x8P.assume = A1nz := by decide +kernel

theorem asmNZ (σ : Nat → Int) (h0 : 0 < σ 2) :
    ∀ p ∈ A1nz, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A1nz, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
  omega

/-! ## The alignment, executed concretely -/

/-- `and rsp,-32` (pc 6 of the kernel). -/
def alignI8 : Instr := .alu .and 64 4 (.imm (-32))

theorem prog_6 : prog[6]? = some alignI8 := by decide +kernel

/-- The cut after the alignment at residue `r`: `rsp = sAt (-8 - r)`, flags cleared, pc 7. -/
def x8A (r : Nat) : State E Lin :=
  { x8P with gpr := x8P.gpr.set 4 (.ptr ⟨rStack, sAt (-8 - (r : Int))⟩), flags := none, pc := 7 }

theorem x8A_err (r : Nat) : (x8A r).err = none := x8P_err

/-- **The alignment at the concrete state.**  `rsp` is the integer `σ 9 - 8` there, so `andInt`
is total; the result is `x8A r` for the residue `r = (σ 9 - 8) % 32`. -/
theorem align_hom8 (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (r : Nat) (hr : (r : Int) = (σ 9 - 8) % 32) :
    exec 4 m orc alignI8 (mapState env σ x8P) = mapState env σ (x8A r) := by
  have hsp : (mapState env σ x8P).getG 4 = .ptr ⟨rStack, σ 9 - 8⟩ := by
    rw [getG_hom, Hashtree.Proofs.WrapperAmd64.getG_of _ _ _ x8P_rsp]
    simp only [mapVal, mapAddr, Hashtree.Proofs.WrapperAmd64.sAt_eval]; congr 2; omega
  have hh : (mapState env σ x8P).halted = false := by simp only [mapState, x8P_halted]
  simp only [exec, alignI8, hh, Bool.false_eq_true, ite_false]
  simp [okOr, gCtl, hsp, andInt, Ctl.asInt, Ctl.ofInt, bind, Except.bind, pure, Except.pure]
  simp only [mapState, x8A, clearFlags, State.setG, State.next, x8P_pc, List.map_set, mapVal,
    mapAddr, Hashtree.Proofs.WrapperAmd64.sAt_eval]
  congr 4
  omega

/-- The alignment as a one-instruction run. -/
theorem run1_align (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (r : Nat) (hr : (r : Int) = (σ 9 - 8) % 32) :
    run prog 4 m orc 1 (mapState env σ x8P) = mapState env σ (x8A r) := by
  have hh : (mapState env σ x8P).halted = false := by simp only [mapState, x8P_halted]
  have hpc : (mapState env σ x8P).pc = 6 := by simp only [mapState, x8P_pc]
  show run prog 4 m orc (0 + 1) (mapState env σ x8P) = mapState env σ (x8A r)
  simp only [run, hh, Bool.false_eq_true, ite_false, hpc, prog_6]
  exact align_hom8 env σ m orc r hr

/-! ## The small path, `0 < c < 8`, at every residue -/

/-- `jb` at pc 13 taken (count below 8). -/
def orcSm : Nat → Bool := fun pc => decide (pc ∈ ([13] : List Nat))

/-- The small path's cut: 14 instructions from `x8A r` -- `sub rsp,928`, the four saves,
`cmp rdx,8`, `jb` (taken), the four restores, `mov rsp,rbp`, `pop rbp`, `jmp avx_x4`. -/
def x8Sm (r : Nat) : State E Lin := abstract (run prog 4 m8 orcSm 14 (x8A r))

/-- The small path's recorded conditions: `c < 8` (taken) and `c ≠ 0` (taken). -/
def A1Sm : List (Cond Lin × Bool) :=
  [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨8, []⟩ : Lin)), true),
   ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]

theorem asmSm (σ : Nat → Int) (h0 : 0 < σ 2) (h8 : σ 2 < 8) :
    ∀ p ∈ A1Sm, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A1Sm, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega

/-- The small-path facts at one residue, as one boolean: the slice check, the tail, the
error/halt/pc fields, the entry register file restored, the recorded conditions, and the log
shape (every write at `rOut` or at a stack offset below `σ 9`). -/
def smOk (r : Nat) : Bool :=
  sliceCheck prog 4 m8 orcSm 14 (x8A r) (x8Sm r) [] &&
  decide ((x8Sm r).tail = some "hashtree_sha256_avx_x4") && decide ((x8Sm r).err = none) &&
  decide ((x8Sm r).halted = true) && decide ((x8Sm r).pc = 6080) &&
  decide ((x8Sm r).gpr = entryWx.gpr) && decide ((x8Sm r).vr = entryWx.vr) &&
  decide ((x8Sm r).assume = A1Sm) && (x8Sm r).mem.all logOkBW

/-- **Every residue.**  The 32 small paths, checked in the kernel. -/
theorem smOk_all : (List.range 32).all smOk = true := by decide +kernel

theorem smOk_of (r : Nat) (hr : r < 32) : smOk r = true :=
  List.all_eq_true.mp smOk_all r (List.mem_range.mpr hr)

theorem x8Sm_facts (r : Nat) (hr : r < 32) :
    sliceCheck prog 4 m8 orcSm 14 (x8A r) (x8Sm r) [] = true ∧
    (x8Sm r).tail = some "hashtree_sha256_avx_x4" ∧ (x8Sm r).err = none ∧
    (x8Sm r).halted = true ∧ (x8Sm r).pc = 6080 ∧
    (x8Sm r).gpr = entryWx.gpr ∧ (x8Sm r).vr = entryWx.vr ∧
    (x8Sm r).assume = A1Sm ∧ (x8Sm r).mem.all logOkBW = true := by
  have h := smOk_of r hr
  simp only [smOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The residue is below 32. -/
theorem residue_lt (σ : Nat → Int) (r : Nat) (hr : (r : Int) = (σ 9 - 8) % 32) : r < 32 := by
  omega

/-- **The x8 small path at the wrapper call state.**  For `0 < c < 8`, from
`fr M (mapState env0 σ entryW)` with a W-mode log `M`, 20 instructions (the five-instruction
prologue, the alignment at the residue `r = (σ 9 - 8) % 32`, and the 14-instruction small path)
reach `fr M (mapState e' (upd15 σ) (x8Sm r))`. -/
theorem x8_small_run (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (h0 : 0 < σ 2) (h8 : σ 2 < 8) (r : Nat) (hr : (r : Int) = (σ 9 - 8) % 32) :
    ∃ e', run prog 4 mem0c orcC 20 (fr M (mapState env0 σ entryW)) =
        fr M (mapState e' (upd15 σ) (x8Sm r)) := by
  have hr32 : r < 32 := residue_lt σ r hr
  have h9 : upd15 σ 9 = σ 9 := by simp [upd15]
  have h2 : upd15 σ 2 = σ 2 := by simp [upd15]
  have hw' : WfMemW rodata [] (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) (view M mem0c) :=
    wfMemW_upd15 rodata env0 _ σ (view M mem0c) (wfW_view rodata env0 env0 σ mem0c M hM hw)
  have hrel : Mem0Rel (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) m8 (view M mem0c) := by
    rw [m8_eq]
    exact mem0RelW_of_wf rodata [] _ _ (view M mem0c) hw' (fun r off => rfl)
  rw [run_fr, ← mapState_entryW env0 (view M mem0c) σ]
  have r5 := (slice_sound (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) m8 (view M mem0c)
    hrel prog 4 orcNZ orcC 5 entryWx x8P [] sliceP entryWx_err
    (assumeOk_of (upd15 σ) x8P A1nz x8P_assume (asmNZ (upd15 σ) (by rw [h2]; exact h0)))).1
  have hrel1 : Mem0Rel (envAbs (envM env0 (view M mem0c) (upd15 σ)) (run prog 4 m8 orcNZ 5 entryWx))
      (upd15 σ) m8 (view M mem0c) :=
    mem0Rel_envAbs _ _ _ _ m8_keyed hrel _
  have r1 := run1_align (envAbs (envM env0 (view M mem0c) (upd15 σ)) (run prog 4 m8 orcNZ 5 entryWx))
    (upd15 σ) (view M mem0c) orcC r (by rw [h9]; exact hr)
  have hf := x8Sm_facts r hr32
  have r14 := (slice_sound _ (upd15 σ) m8 (view M mem0c) hrel1 prog 4 orcSm orcC 14 (x8A r)
    (x8Sm r) [] hf.1 (x8A_err r)
    (assumeOk_of (upd15 σ) (x8Sm r) A1Sm hf.2.2.2.2.2.2.2.1
      (asmSm (upd15 σ) (by rw [h2]; exact h0) (by rw [h2]; exact h8)))).1
  refine ⟨envAbs (envAbs (envM env0 (view M mem0c) (upd15 σ)) (run prog 4 m8 orcNZ 5 entryWx))
    (run prog 4 m8 orcSm 14 (x8A r)), congrArg (fr M) ?_⟩
  rw [show (20 : Nat) = 5 + (1 + 14) from rfl, run_add, r5, run_add, r1]
  exact r14

/-! ## The hand-off to `avx_x4` -/

/-- The resumed small-path cut is the x4 entry state `entryWx` (`entryW` with the dead `rax`
on symbol 15) up to flags, behind the small path's own log. -/
theorem x8Sm_resume (r : Nat) (hr : r < 32) (e : Key → W32) (σ : Nat → Int) :
    resume (mapState e σ (x8Sm r)) =
      fr ((mapState e σ (x8Sm r)).mem)
        { mapState e σ entryWx with flags := (mapState e σ (x8Sm r)).flags } := by
  have hf := x8Sm_facts r hr
  simp only [resume, fr, mapState, hf.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1, entryWx_err,
    entryWx_pc, entryWx_halted, entryWx_tail, entryWx_mem, entryWx_assume, List.nil_append,
    List.map_nil]

/-- The small path's log at the concrete level is a W-mode log: output cells or stack cells
below `σ 9`. -/
theorem x8Sm_outLogW (r : Nat) (hr : r < 32) (e : Key → W32) (σ : Nat → Int) :
    OutLogW σ ((mapState e σ (x8Sm r)).mem) := by
  have hf := (x8Sm_facts r hr).2.2.2.2.2.2.2.2
  intro p hp
  simp only [mapState, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have h : logOkBW q = true := List.all_eq_true.mp hf q hq
  by_cases h1 : q.1.region = rOut
  · left
    simp only [mapAddr, h1]
  · by_cases h2 : q.1.region = rStack
    · right
      have hd : decide (q.1.off.c = stkC ∧ q.1.off.k < 0) = true := by
        rw [logOkBW, if_neg h1, if_pos h2] at h
        exact h
      obtain ⟨hc, hk⟩ := of_decide_eq_true hd
      refine ⟨h2, ?_⟩
      simp only [mapAddr]
      rw [Hashtree.Proofs.AvxX4LoopWFrame.eval_stk σ q.1.off hc]
      omega
    · exfalso
      rw [logOkBW, if_neg h1, if_neg h2] at h
      exact Bool.false_ne_true h

/-- The ABI fact the wrapper gives (`σ 9 ≡ 8 (mod 16)`: aligned to 32 before the `CALL`
pushes 8, or the same `σ 9` through a tail call) leaves two residues. -/
theorem residue_abi (σ : Nat → Int) (h : σ 9 % 16 = 8) :
    (σ 9 - 8) % 32 = 0 ∨ (σ 9 - 8) % 32 = 16 := by
  omega

end Hashtree.Proofs.Avx2X8Align
