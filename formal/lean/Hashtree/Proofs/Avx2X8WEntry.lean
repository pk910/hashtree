import Hashtree.Kernels.X86.Avx2X8
import Hashtree.Asm.X86SymW
import Hashtree.Asm.X86Ren
import Hashtree.Asm.Cut
import Hashtree.Asm.Chain
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
  Hashtree.Asm.X86Ren Hashtree.Kernels.X86.Avx2X8

namespace Hashtree.Proofs.Avx2X8WEntry

/-!
# The `avx2_x8` kernel at the wrapper's call state: the entry segment

`entryW` (`Hashtree/Asm/X86SymW`) is the state the Go wrapper calls a kernel in: the argument
registers point into the wrapper's frame, and the stack cells are addressed relative to the
symbol `9` (`sAt k`), not to a constant offset.  This file covers what the `avx2_x8` entry
segment can be proved at that state:

* **count 0** (`x8_zero_run`): `nop; cmp rdx,0; jne` not taken; `ret`.  Four instructions,
  plain return, no tail -- fully proved, also at an arbitrary fresh rodata region
  (`x8_zero_run_region`, via `X86Ren.run_swap_chain`).
* **count `0 < c`** (`x8_prologue_run`): the `jne` is taken and the five prologue instructions
  (`nop; cmp; jne` (taken) `push rbp; mov rbp,rsp`) run; the state reaches `pc = 6` with
  `err = none`.
* **the alignment blocker** (`x8_align_blocked`): the next instruction, `and rsp,-32`, *fails*
  at this call state with `err = some "and on symbolic pointer"`, because `rsp` holds the
  symbolic offset `sAt (-8)` (`= ⟨-8, stkC⟩`, coefficient `1` on symbol `9`) and
  `Ctl.asInt` is `none` on it (`Hashtree/Asm/X86.lean`, the `.alu .and` case).  Consequently
  the small path (`0 < c < 8`, which would tail into `avx_x4` after the frame setup) and the
  loop path of `avx2_x8` cannot be proved from `entryW` as it stands: the alignment must be
  supplied as a hypothesis about the caller's stack (`σ 9` aligned mod 32), exactly the shape
  of `WrapperPre.align_hom`.

The rodata table lives in region `4` here; `x8_zero_run_region` shows the lift to a link's
own fresh region.
-/

/-- The initial memory of the kernel: rodata in region 4, the wrapper's return marker at
`σ 9`, and input bytes.  The kernel pushes its frame itself, so no stack bytes are assumed. -/
def m8 : Addr Lin → Cell E Lin := mem0sW 4 rodata []

theorem m8_keyed : MemKeyed m8 := mem0sW_keyed 4 rodata [] (by decide)

/-- No branch taken (count 0). -/
def orcNone : Nat → Bool := fun _ => false

/-- `jne` at pc 2 taken (count nonzero). -/
def orcNZ : Nat → Bool := fun pc => decide (pc ∈ ([2] : List Nat))

/-! ## Count 0 -/

/-- Count 0: `nop; cmp rdx,0; jne` not taken; `ret`. -/
def x8Z : State E Lin := abstract (run prog 4 m8 orcNone 4 entryW)

theorem sliceW8_zero : sliceCheck prog 4 m8 orcNone 4 entryW x8Z [] = true := by decide +kernel
theorem x8Z_pc : x8Z.pc = 3 := by decide +kernel
theorem x8Z_halted : x8Z.halted = true := by decide +kernel
theorem x8Z_tail : x8Z.tail = none := by decide +kernel
theorem x8Z_err : x8Z.err = none := by decide +kernel
theorem x8Z_mem : x8Z.mem = [] := by decide +kernel
theorem x8Z_assume : x8Z.assume =
    [((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), false)] := by decide +kernel

/-- The count-0 condition, for a zero count. -/
theorem asmZero (σ : Nat → Int) (h0 : σ 2 = 0) :
    ∀ p ∈ ([((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), false)] :
        List (Cond Lin × Bool)),
      (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
  omega

/-- **Count 0**: the kernel returns after four instructions, whatever the concrete branch
oracle does. -/
theorem x8_zero_run (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (env0 : Key → W32)
    (σ : Nat → Int) (h0 : Mem0Rel env0 σ m8 mem0c) (hc : σ 2 = 0) :
    ∃ e', run prog 4 mem0c orcC 4 (mapState env0 σ entryW) = mapState e' σ x8Z ∧
      (mapState e' σ x8Z).halted = true ∧ (mapState e' σ x8Z).tail = none ∧
      (mapState e' σ x8Z).err = none := by
  have hA : AssumeOk σ x8Z :=
    assumeOk_of σ x8Z _ x8Z_assume (asmZero σ hc)
  refine ⟨envAbs env0 (run prog 4 m8 orcNone 4 entryW),
    (slice_sound env0 σ m8 mem0c h0 prog 4 orcNone orcC 4 entryW x8Z [] sliceW8_zero
      x8Z_err hA).1, ?_, ?_, ?_⟩
  · simp [mapState, x8Z_halted]
  · simp [mapState, x8Z_tail]
  · simp [mapState, x8Z_err]

/-- **Count 0 at a fresh rodata region** `r`: the region-4 run, renamed.  This is the form a
chain link uses (`X86Ren.run_swap_chain`). -/
theorem x8_zero_run_region (r : Region) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet)
    (m0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (env0 : Key → W32) (σ : Nat → Int)
    (h0 : Mem0Rel env0 σ m8 ((swap 4 r).mem m0c)) (hc : σ 2 = 0) :
    ∃ e', run prog r m0c orcC 4 ((swap 4 r).state (mapState env0 σ entryW)) =
        (swap 4 r).state (mapState e' σ x8Z) ∧
      (mapState e' σ x8Z).halted = true ∧ (mapState e' σ x8Z).tail = none ∧
      (mapState e' σ x8Z).err = none := by
  obtain ⟨e', hrun, hh, htl, he⟩ := x8_zero_run ((swap 4 r).mem m0c) orcC env0 σ h0 hc
  exact ⟨e', (run_swap_chain r hrNum hrRet prog m0c orcC 4 (mapState env0 σ entryW)).trans
    (congrArg (swap 4 r).state hrun), hh, htl, he⟩

/-! ## The prologue, and the alignment blocker -/

/-- The state after the five instructions `nop; cmp rdx,0; jne` (taken) `push rbp; mov rbp,rsp`,
i.e. at the `and rsp,-32`. -/
def x8P : State E Lin := abstract (run prog 4 m8 orcNZ 5 entryW)

theorem sliceW8_prologue : sliceCheck prog 4 m8 orcNZ 5 entryW x8P [] = true := by
  decide +kernel
theorem x8P_pc : x8P.pc = 6 := by decide +kernel
theorem x8P_halted : x8P.halted = false := by decide +kernel
theorem x8P_err : x8P.err = none := by decide +kernel

/-- The one recorded condition of the prologue: the count is nonzero. -/
theorem x8P_assume : x8P.assume =
    [((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)] := by decide +kernel

theorem asmNZ (σ : Nat → Int) (h0 : 0 < σ 2) :
    ∀ p ∈ ([((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)] :
        List (Cond Lin × Bool)),
      (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
  omega

/-- After the prologue the stack pointer is the symbolic `⟨-8, stkC⟩`: the caller's stack
pointer `sAt 0` moved down by the `push`. -/
theorem x8P_rsp : x8P.gpr[4]? = some (Val.ptr (⟨rStack, sAt (-8)⟩ : Addr Lin)) := by
  decide +kernel

/-- `Ctl.asInt` cannot read that offset: the coefficient of symbol `9` is nonzero. -/
theorem asInt_sAt : Ctl.asInt (⟨0, stkC⟩ : Lin) = none := by decide +kernel
theorem asInt_sAt' : Ctl.asInt (⟨-8, stkC⟩ : Lin) = none := by decide +kernel

/-- **The blocker, proved.**  The seventh instruction, `and rsp,-32`, fails at the wrapper's
call state: `rsp` is a symbolic pointer, so `Ctl.asInt` returns `none` and the semantics
throws `"and on symbolic pointer"` (`Hashtree/Asm/X86.lean`, `.alu .and` case). -/
theorem x8_align_blocked :
    (exec 4 m8 orcNZ (prog[6]!) x8P).err = some "and on symbolic pointer" := by
  decide +kernel

/-- The same, in the form of the run: the kernel cannot make progress past `pc = 6` at
`entryW`. -/
theorem x8_stuck :
    (run prog 4 m8 orcNZ 6 entryW).err = some "and on symbolic pointer" := by
  decide +kernel

/-- **`0 < c < 8` reaches the blocker after five instructions.**  The small path continues into
the frame setup, which cannot be executed at this call state (see `x8_align_blocked`), so this
is as far as the segment goes without an alignment hypothesis on `σ 9`. -/
theorem x8_prologue_run (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ : Nat → Int) (c : Nat) (h0 : Mem0Rel env0 σ m8 mem0c)
    (hc : σ 2 = (c : Int)) (hpos : 0 < c) :
    ∃ e', run prog 4 mem0c orcC 5 (mapState env0 σ entryW) = mapState e' σ x8P ∧
      (mapState e' σ x8P).err = none ∧ (mapState e' σ x8P).halted = false ∧
      (mapState e' σ x8P).pc = 6 := by
  have hp : 0 < σ 2 := by rw [hc]; exact_mod_cast hpos
  have hA : AssumeOk σ x8P := assumeOk_of σ x8P _ x8P_assume (asmNZ σ hp)
  refine ⟨envAbs env0 (run prog 4 m8 orcNZ 5 entryW),
    (slice_sound env0 σ m8 mem0c h0 prog 4 orcNZ orcC 5 entryW x8P [] sliceW8_prologue
      x8P_err hA).1, ?_, ?_, ?_⟩
  · simp [mapState, x8P_err]
  · simp [mapState, x8P_halted]
  · simp [mapState, x8P_pc]

end Hashtree.Proofs.Avx2X8WEntry
