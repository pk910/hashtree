import Hashtree.Asm.Subst
import Hashtree.Gen.AvxX4P.P0

/-!
# The avx_x4 body as a loop, at its loop head

The fixed-count `AvxX4P` certificate decomposes the `c = 4` run from `entryS 24` into 201
slices, but it has no cut at the loop head (`pc = 5`, immediately after `sub rsp,408`), so its
body cannot be replayed for a second iteration.  This file adds the missing head and tail cuts
and proves that one turn of the loop is a substitution instance of its head state.

`orcPro` forces the `jne` at pc 2 (the count-0 early return is not taken); four instructions
then reach pc 5.

* `KH` is the loop head reached after that entry path, with the flags as fresh symbols (the
  first instruction at the head, `cmp rdx,4`, overwrites them).  `KH_head_slice` checks the
  68-instruction suffix of the pilot's first slice from it and ends at the pilot's cut `K1`
  (pc 73).
* `KHL` is the same head with the two dead registers `rcx` (a rodata pointer) and `r9` set to
  the values the body leaves in them at its end cut `K200` (`.rodata+1024` and `.num+1024`).
  The body never reads them before writing them, so the head slice `KHL_head_slice` still
  ends at `K1`.  `KHL` is the loop invariant: every iteration starts there.

The exit is checked from both heads (`exit_slice`, `exit_sliceL`): with `rdx < 4` the head
branches to pc 4142, restores `rsp` and reaches `jmpTail hashtree_sha256_avx_x1` with the
pointer registers unchanged (and the recorded conditions `c < 4` and `c != 0`).

The remaining half of the loop turn -- the 23 instructions from the pilot's end cut `K200`
back to the head, and the substitution shape `KHL.substL tau` -- needs the pilot's `K200`
and is kept in `AvxX4LoopTail.lean` (it can only be elaborated once `P199` is built).
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Kernels.X86.AvxX4

namespace Hashtree.Proofs.AvxX4Loop
open Hashtree.Gen.AvxX4P

/-- The pilot's prologue path: the `jne` at pc 2 (count nonzero) is taken. -/
def orcPro : Nat → Bool := fun pc => decide (pc ∈ ([2] : List Nat))

/-- The cut after the four-instruction entry path (`nop; cmp rdx,0; jne 4; sub rsp,408`). -/
def KHP : State E Lin := abstract (run prog 4 m0q orcPro 4 (entryS 24))

/-- The loop head (pc 5) reached from the system V entry state; `cmp rdx,4` overwrites the
flags, so they are fresh symbols. -/
def KH : State E Lin := { KHP with flags := some (Lin.sym 3, Lin.sym 4) }

theorem KH_pc : KH.pc = 5 := by decide +kernel

/-- `KHP` is `KH` with symbols 3 and 4 replaced by its concrete flags (and no conditions). -/
def tauP : List Lin :=
  match KHP.flags with
  | some (a, b) => [Lin.sym 0, Lin.sym 1, Lin.sym 2, a, b]
  | none => [Lin.sym 0, Lin.sym 1, Lin.sym 2, Lin.sym 3, Lin.sym 4]

theorem KHP_inst : { KHP with assume := [] } = KH.substL tauP := by decide +kernel

/-- The first 68 instructions at the head, ending at the pilot's cut `K1` (pc 73). -/
theorem KH_head_slice : sliceCheck prog 4 m0q (fun _ => false) 68 KH K1 [] = true := by
  decide +kernel

/-- The loop invariant head: the body leaves `rcx = .rodata + 1024` and `r9 = .num + 1024`
at `K200`; both are dead at the head (the body overwrites them before any read), and fixing
them here makes the end cut an exact substitution instance of the head. -/
def KHL : State E Lin :=
  { KH with gpr := KH.gpr.set 1 (.ptr ⟨4, (⟨1024, []⟩ : Lin)⟩)
                      |>.set 9 (.ptr ⟨0, (⟨1024, []⟩ : Lin)⟩) }

theorem KHL_pc : KHL.pc = 5 := by decide +kernel

theorem KHL_head_slice : sliceCheck prog 4 m0q (fun _ => false) 68 KHL K1 [] = true := by
  decide +kernel

/-- The exit path: the `jl` at pc 6 (count below the lane width) is taken. -/
def orcExit : Nat → Bool := fun pc => decide (pc ∈ ([6] : List Nat))

/-- The tail state reached from `KH` with `count < 4`: pc 4143, the `jmpTail` to avx_x1. -/
def KEx : State E Lin := abstract (run prog 4 m0q orcExit 4 KH)

/-- The same from the loop invariant head. -/
def KExL : State E Lin := abstract (run prog 4 m0q orcExit 4 KHL)

theorem exit_slice : sliceCheck prog 4 m0q orcExit 4 KH KEx [] = true := by decide +kernel
theorem exit_sliceL : sliceCheck prog 4 m0q orcExit 4 KHL KExL [] = true := by decide +kernel

theorem KEx_pc : KEx.pc = 4143 := by decide +kernel
theorem KEx_halted : KEx.halted = true := by decide +kernel
theorem KEx_tail : KEx.tail = some "hashtree_sha256_avx_x1" := by decide +kernel
theorem KEx_mem : KEx.mem = [] := by decide +kernel
theorem KEx_rsp : KEx.getG 4 = .ptr ⟨rStack, (⟨24, []⟩ : Lin)⟩ := by decide +kernel
theorem KEx_assume : KEx.assume =
    [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨4, []⟩ : Lin)), true),
     ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)] := by decide +kernel
theorem KExL_rsp : KExL.getG 4 = .ptr ⟨rStack, (⟨24, []⟩ : Lin)⟩ := by decide +kernel
theorem KExL_assume : KExL.assume =
    [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨4, []⟩ : Lin)), true),
     ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)] := by decide +kernel

/-! ## The two non-looping count classes, from the pilot entry state

The count-0 early return and the `1 ≤ c < 4` early exit, at `entryS 24` (the pilot's entry
state).  These are the entryS analogues of `AvxX4Entry.zero_run`/`small_prefix` at `entryW`. -/

/-- The count-0 path takes neither branch: pc 3 `ret` halts with rsp advanced past the return
marker. -/
def orc0 : Nat → Bool := fun _ => false

def KZ : State E Lin := abstract (run prog 4 m0q orc0 4 (entryS 24))

theorem zero_slice : sliceCheck prog 4 m0q orc0 4 (entryS 24) KZ [] = true := by decide +kernel
theorem KZ_pc : KZ.pc = 3 := by decide +kernel
theorem KZ_halted : KZ.halted = true := by decide +kernel
theorem KZ_tail : KZ.tail = none := by decide +kernel
theorem KZ_mem : KZ.mem = [] := by decide +kernel
theorem KZ_rsp : KZ.getG 4 = .ptr ⟨rStack, (⟨32, []⟩ : Lin)⟩ := by decide +kernel
theorem KZ_assume : KZ.assume =
    [((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), false)] := by decide +kernel

/-- Counts 1–3: the `jne` at pc 2 is taken, the `jl` at pc 6 exits, rsp is restored, and the
kernel reaches the avx_x1 tail in 8 instructions. -/
def orcS : Nat → Bool := fun pc => decide (pc ∈ ([2, 6] : List Nat))

def KSmS : State E Lin := abstract (run prog 4 m0q orcS 8 (entryS 24))

theorem small_slice : sliceCheck prog 4 m0q orcS 8 (entryS 24) KSmS [] = true := by decide +kernel
theorem KSmS_pc : KSmS.pc = 4143 := by decide +kernel
theorem KSmS_halted : KSmS.halted = true := by decide +kernel
theorem KSmS_tail : KSmS.tail = some "hashtree_sha256_avx_x1" := by decide +kernel
theorem KSmS_mem : KSmS.mem = [] := by decide +kernel
theorem KSmS_rsp : KSmS.getG 4 = .ptr ⟨rStack, (⟨24, []⟩ : Lin)⟩ := by decide +kernel
theorem KSmS_assume : KSmS.assume =
    [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨4, []⟩ : Lin)), true),
     ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)] := by decide +kernel

end Hashtree.Proofs.AvxX4Loop
