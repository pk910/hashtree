import Hashtree.Asm.RiscvSlice
import Hashtree.Asm.Chain
import Hashtree.Asm.X86Sym
import Hashtree.Kernels.Riscv.DispHash

/-!
# The `hashtree_hash` stub

The shipped `hashtree_hash` is three instructions: `auipc` the address of the object's
`.data.rel.local` slot, load the pointer stored there, and tail-jump through it.  The slot is
initialized to `init_and_hash` (the object's constructor), which the dispatcher replaces with the
selected kernel on its first call.

`stub_correct`: on any memory whose `.data.rel.local` slot (region 60, bytes `[0,8)`) holds a
pointer to the `init_and_hash` region (6), the concrete run of the three instructions halts with
`tail = some "init_and_hash"`, no model error, no recorded conditions and no writes.  The registers
are arbitrary (every register is a distinct location variable at the entry).

Not modelled here: the dynamic-linker initialization that writes the slot (stated as the hypothesis
`Mem0Rel env σ M0 mem0c`), and `init_and_hash` itself (see `RvDispatchInit`).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace Hashtree.Proofs.RvDispatch
open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.X86Sym Hashtree.Kernels.Riscv.DispHash

/-- Regions: the stub's rodata/GOT/code (10/11/12), `.data.rel.local` (60), `init_and_hash` (6). -/
def syms : List (String × Region) := [(".data.rel.local", 60), ("init_and_hash", 6)]

/-- The stub's static environment. -/
def pe : Env := ⟨10, 11, 12, syms⟩

/-- Symbolic memory: the slot `[0,8)` of `.data.rel.local` is a pointer to `init_and_hash`
(eight pointer bytes); everything else is poison. -/
def M0 : Addr Lin → Cell E Lin := fun a =>
  match a.off.asInt with
  | some o => if a.region = 60 ∧ 0 ≤ o ∧ o < 8 then .pb ⟨6, Lin.ofInt 0⟩ o.toNat else poison
  | none => poison

/-- An entry state: every register a distinct location variable. -/
def entry : State E Lin :=
  { gpr := (List.range 32).map fun i => Val.num (.var (.n (2 * i))) (.var (.n (2 * i + 1))),
    vr := [], flags := none, mem := [], pc := 0, halted := false, tail := none, err := none,
    assume := [] }

/-- The run of the three instructions. -/
def Rfin : State E Lin := run prog pe M0 (fun _ => false) 3 entry

/-- Its cut. -/
def KF : State E Lin := abstract Rfin

theorem KF_halted : KF.halted = true := by decide +kernel

theorem KF_tail : KF.tail = some "init_and_hash" := by decide +kernel

theorem KF_err : KF.err = none := by decide +kernel

theorem KF_mem : KF.mem = [] := by decide +kernel

theorem KF_assume : KF.assume = [] := by decide +kernel

theorem KF_check : rvSliceCheck prog pe M0 (fun _ => false) 3 entry KF [] = true := by
  decide +kernel

/-- **The `hashtree_hash` stub tail-calls `init_and_hash`.**  From the LP64D entry (any registers)
on a memory whose `.data.rel.local` slot holds a pointer to `init_and_hash`, the three instructions
halt after 3 steps with `tail = some "init_and_hash"`, without a model error, without recording a
condition and without writing memory. -/
theorem stub_correct (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (h0 : Mem0Rel env σ M0 mem0c) :
    let fin := Riscv.run prog pe mem0c orcC 3 (mapState env σ entry)
    fin.halted = true ∧ fin.tail = some "init_and_hash" ∧ fin.err = none ∧ fin.mem = [] := by
  have h := (rvSlice_sound env σ M0 mem0c h0 prog pe (fun _ => false) orcC 3 entry KF []
    KF_check rfl (assumeOk_of σ KF [] KF_assume (by intro p hp; cases hp))).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]; exact KF_halted
  · rw [h]; exact KF_tail
  · rw [h]; exact KF_err
  · rw [h]; simp only [mapState, KF_mem, List.map_nil]

/-- A concrete memory meeting the stub's hypothesis: `.data.rel.local` holds the pointer to
`init_and_hash`, everything else is zero data. -/
def cmem : Addr Int → Cell W32 Int := fun a =>
  if a.region = 60 then
    if 0 ≤ a.off ∧ a.off < 8 then .pb ⟨6, 0⟩ a.off.toNat else .dat 0 0
  else .dat 0 0

/-- The hypothesis is satisfiable. -/
theorem cmem_rel (σ : Nat → Int) : Mem0Rel (fun _ => 0) σ M0 cmem := by
  intro a ha
  obtain ⟨r, off⟩ := a
  unfold M0 at ha ⊢
  cases hk : off.asInt with
  | none =>
    simp only [M0, hk] at ha
    simp [poison, Cell.okC] at ha
  | some o =>
    simp only [M0, hk] at ha ⊢
    have hev : off.eval σ = o := Lin.eval_asInt σ off o hk
    by_cases h1 : r = 60 ∧ 0 ≤ o ∧ o < 8
    · obtain ⟨rfl, h2, h3⟩ := h1
      simp only [mapAddr, mapCell, cmem, hev, h2, h3, Lin.ofInt, dotC]
      simp
      rfl
    · rw [if_neg h1] at ha
      simp [poison, Cell.okC] at ha

end Hashtree.Proofs.RvDispatch
