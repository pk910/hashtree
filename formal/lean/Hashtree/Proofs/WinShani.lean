import Hashtree.Proofs.Win64
import Hashtree.Kernels.X86.Shani
import Hashtree.Kernels.X86Win.Shani

/-!
# R5: the Win64 ABI model for the windows `shani_x2` kernel

This file establishes, on the *shipped* windows instruction stream, the parts of the Win64
contract that do not depend on the SHA-256 body semantics:

* `shani_body_correspondence` -- the 668 body instructions of the windows stream are exactly the
  linux body instructions under a register permutation `F`, a stack-displacement shift of 160
  bytes and a program-counter shift of 10 instructions.  This is machine-checked here (kernel
  evaluation over the shipped `Array Instr`s), so the only input that remains external is the
  identity of the two *models* with the COFF/ELF objects, which `formal/ci/proofs.py check`
  re-derives from the artifacts on every CI run.
* `shani_stack_footprint` -- every memory operand of the kernel that addresses the stack has
  `0 ≤ disp` and `disp + width ≤ 248` relative to the running `rsp`.  Since the kernel's first
  instruction sets `rsp = entry_rsp - 248` (`shani_rsp_balanced`) and only the epilogue restores
  it, the whole footprint is `[entry_rsp - 248, entry_rsp)`: it lies **below the return address**
  (`[entry_rsp, entry_rsp + 8)`, which is never touched) and **disjoint from the Win64 shadow
  space** `[entry_rsp + 8, entry_rsp + 40)`.
* `shani_callee_gpr_untouched` -- no instruction of the kernel writes a callee-saved general
  register (`rbx`, `rbp`, `rdi`, `rsi`, `r12`-`r15`).  The callee-saved *stack pointer* is
  balanced by `sub rsp, 248` / `add rsp, 248` (`shani_rsp_balanced`).
* `shani_prologue_saves` / `shani_epilogue_restores` / `shani_save_slots_untouched` -- the ten
  `xmm6`-`xmm15` saves of the prologue are read back, slot for slot, by the epilogue, and no
  instruction in between accesses the 160-byte save area.

The remaining, *semantic* step -- composing these facts into an invariant of the run
(`WinCalleeSaved` for the general registers and for `xmm6`-`xmm15`) -- is the `exec`-equivariance
induction over the 39 instruction forms described in `formal/notes/R5.md`; it is not proved here.
The one kernel that does have a full functional contract on windows is `avx512_x16`, whose stream
uses no stack at all (`Proofs.WinAvx512`).

Everything in this file is `decide`-checked over the shipped arrays; the only large kernel
evaluation is `bodyOk_full` (668 instruction comparisons, tens of seconds).
-/

open Hashtree.Asm Hashtree.Asm.X86
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinShani

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.Shani.prog
abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Shani.prog

/-- Number of body instructions shared by the two streams (linux pcs 1..668, windows pcs 11..678). -/
def bodyLen : Nat := 668

/-! ## The register permutation -/

/-- linux -> windows general register numbering.  The linux argument registers `rdi`, `rsi`,
`rdx` become the Win64 argument registers `rcx`, `rdx`, `r8`; the linux rodata bases `rcx`, `rax`
become `r9`, `rax`.  `rsp` is fixed. -/
def F : Nat → Nat
  | 1 => 9 | 2 => 8 | 3 => 5 | 5 => 7 | 6 => 2 | 7 => 1 | 8 => 3 | 9 => 6 | j => j

/-- windows -> linux general register numbering (the inverse of `F`). -/
def G : Nat → Nat
  | 1 => 7 | 2 => 6 | 3 => 8 | 5 => 3 | 6 => 9 | 7 => 5 | 8 => 2 | 9 => 1 | j => j

theorem all_fin {p : Nat → Prop} [DecidablePred p]
    (h : ((List.range 16).all (fun j => decide (p j))) = true) :
    ∀ j, j < 16 → p j := by
  intro j hj
  have hm : j ∈ List.range 16 := List.mem_range.mpr hj
  have h1 := List.all_eq_true.mp h j hm
  simpa using h1

theorem f_lt : ∀ j, j < 16 → F j < 16 := by apply all_fin; decide

theorem gf : ∀ j, j < 16 → G (F j) = j := by apply all_fin; decide

theorem fg : ∀ j, j < 16 → F (G j) = j := by apply all_fin; decide

theorem renPerm : RenPerm F G := ⟨f_lt, gf, fg, rfl⟩

/-! ## The body correspondence of the two shipped streams -/

/-- Shift the displacement of every `rsp`-relative memory operand by `d` (the windows frame is
160 bytes deeper than the linux one, so the same stack slot is `d = 160` further from `rsp`). -/
def mv (d : Int) (m : MemRef) : MemRef :=
  if m.base = some 4 then { m with disp := m.disp + d } else m

def vs (d : Int) : VSrc → VSrc
  | .reg i => .reg i
  | .mem m => .mem (mv d m)

def gs (d : Int) : GSrc → GSrc
  | .reg i => .reg i
  | .imm v => .imm v
  | .mem m => .mem (mv d m)

/-- The linux instruction with every `rsp`-relative displacement shifted by `d`. -/
def addDisp (d : Int) : Instr → Instr
  | .vop op vex w dd s1 s2 => .vop op vex w dd s1 (vs d s2)
  | .vload vex w dd src => .vload vex w dd (vs d src)
  | .vstore w m s => .vstore w (mv d m) s
  | .inserti128 dd s1 m imm => .inserti128 dd s1 (mv d m) imm
  | .inserti64x4 dd s1 m imm => .inserti64x4 dd s1 (mv d m) imm
  | .mov w dd s => .mov w dd (gs d s)
  | .movst w m s => .movst w (mv d m) s
  | .alu op w dd s => .alu op w dd (gs d s)
  | .sub w dd s => .sub w dd (gs d s)
  | .lea dd m => .lea dd (mv d m)
  | .cmp w a b => .cmp w a (gs d b)
  | i => i

/-- Shift every branch target by `p` instructions (the windows body starts 10 instructions later). -/
def shiftTgt (p : Nat) : Instr → Instr
  | .jcc c t => .jcc c (t + p)
  | .jmp t => .jmp (t + p)
  | i => i

/-- linux body instruction -> the corresponding windows body instruction. -/
def bodyI (f : Nat → Nat) (d : Int) (p : Nat) (i : Instr) : Instr :=
  shiftTgt p (rlI f (addDisp d i))

/-- The instruction-by-instruction comparison of the two shipped bodies. -/
def bodyOk (n : Nat) : Bool :=
  (List.range n).all (fun j =>
    decide (winProg[11 + j]? = (linuxProg[1 + j]?).map (bodyI F 160 10)))

/-- Machine-checked: the 668 body instructions of the windows stream are the linux ones renamed,
re-based and shifted. -/
theorem bodyOk_full : bodyOk bodyLen = true := by decide +kernel

/-- Pointwise form of `bodyOk_full`. -/
theorem shani_body_correspondence :
    ∀ j, j < bodyLen →
      winProg[11 + j]? = (linuxProg[1 + j]?).map (bodyI F 160 10) := by
  intro j hj
  have hm : j ∈ List.range bodyLen := List.mem_range.mpr hj
  have h := List.all_eq_true.mp bodyOk_full j hm
  simpa [bodyOk, bodyLen] using h

/-! ## Stack footprint: frame below the return address, shadow space untouched -/

def vsRefs (w : Nat) : VSrc → List (MemRef × Nat)
  | .reg _ => []
  | .mem m => [(m, 4 * w)]

def gsRefs (w : Nat) : GSrc → List (MemRef × Nat)
  | .reg _ => []
  | .imm _ => []
  | .mem m => [(m, if w = 64 then 8 else 4)]

/-- The memory operands of an instruction, each with the number of bytes it accesses. -/
def memRefs : Instr → List (MemRef × Nat)
  | .vop _ _ w _ _ m => vsRefs w m
  | .vload _ w _ src => vsRefs w src
  | .vstore w m _ => [(m, 4 * w)]
  | .inserti128 _ _ m _ => [(m, 16)]
  | .inserti64x4 _ _ m _ => [(m, 32)]
  | .mov w _ src => gsRefs w src
  | .movst w m _ => [(m, if w = 64 then 8 else 4)]
  | .alu _ w _ src => gsRefs w src
  | .sub w _ src => gsRefs w src
  | .lea _ m => [(m, 8)]
  | .cmp _ _ src => gsRefs 64 src
  | _ => []

/-- A stack-relative memory operand: no `rip` relocation and based on `rsp`. -/
def rspBased (m : MemRef) : Bool := m.ro.isNone && m.base = some 4

/-- The `disp` of an `rsp`-based operand lies in `[lo, hi - width]`, so the bytes touched are
inside `[rsp + lo, rsp + hi)`. -/
def refIn (lo hi : Int) (mw : MemRef × Nat) : Bool :=
  if rspBased mw.1 then decide (lo ≤ mw.1.disp) && decide (mw.1.disp + (mw.2 : Int) ≤ hi)
  else true

def refsIn (lo hi : Int) (i : Instr) : Bool := (memRefs i).all (refIn lo hi)

/-- Every stack access of the shipped windows kernel stays inside `[rsp, rsp + 248)`, i.e. inside
`[entry_rsp - 248, entry_rsp)` after the prologue's `sub rsp, 248`.  In particular the return
address (`[entry_rsp, entry_rsp + 8)`) and the Win64 shadow space (`[entry_rsp + 8,
entry_rsp + 40)`) are never touched: no stack access of this kernel has a nonnegative entry-
relative displacement. -/
theorem shani_stack_footprint : winProg.toList.all (refsIn 0 248) = true := by
  decide +kernel

/-! ## Callee-saved general registers -/

/-- The general registers an instruction writes.  `push`/`pop` write `rsp`; every other write is
the instruction's destination register. -/
def writesGpr : Instr → List Nat
  | .mov _ d _ => [d]
  | .alu _ _ d _ => [d]
  | .sub _ d _ => [d]
  | .lea d _ => [d]
  | .ror _ d _ => [d]
  | .shld _ d _ _ => [d]
  | .shl _ d _ => [d]
  | .bswap _ d => [d]
  | .push _ => [rsp]
  | .pop r => [r, rsp]
  | _ => []

/-- No instruction of the kernel writes a callee-saved general register. -/
theorem shani_callee_gpr_untouched :
    winProg.toList.all (fun i => (writesGpr i).all (fun r => !(winCalleeGpr.contains r))) = true := by
  decide +kernel

/-- The kernel restores `rsp`: the prologue reserves 248 bytes, the epilogue adds exactly 248
back, and no other instruction writes `rsp`. -/
theorem shani_rsp_balanced :
    winProg[0]? = some (.sub 64 rsp (.imm 248))
      ∧ winProg[689]? = some (.alu .add 64 rsp (.imm 248))
      ∧ (List.range 691).all (fun j => decide (j ≠ 0 → j ≠ 689 →
          (writesGpr (winProg[j]?.getD .nop)).all (fun r => decide (r ≠ rsp)))) = true := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  decide +kernel

/-! ## The callee-saved vector save area -/

/-- The prologue's ten `xmm6`-`xmm15` saves, slot for slot. -/
theorem shani_prologue_saves :
    (List.range 10).all (fun k => decide (winProg[1 + k]? =
      some (.vstore 4 { base := some rsp, disp := (16 * (k : Int)) } (6 + k)))) = true := by
  decide +kernel

/-- The epilogue's ten `xmm6`-`xmm15` restores, slot for slot, from the addresses the prologue
saved them to. -/
theorem shani_epilogue_restores :
    (List.range 10).all (fun k => decide (winProg[679 + k]? =
      some (.vload false 4 (6 + k) (.mem { base := some rsp, disp := (16 * (k : Int)) })))) = true := by
  decide +kernel

/-- No instruction between the prologue saves and the epilogue restores accesses the 160-byte save
area `[rsp, rsp + 160)`. -/
theorem shani_save_slots_untouched :
    ((winProg.toList.drop 11).take 668).all (fun i =>
      (memRefs i).all (fun mw => !(rspBased mw.1) || decide (mw.1.disp + (mw.2 : Int) ≤ 0)
        || decide (160 ≤ mw.1.disp))) = true := by
  decide +kernel

end Hashtree.Proofs.WinShani
