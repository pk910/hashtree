import Hashtree.Proofs.Win64
import Hashtree.Kernels.X86.SseX1
import Hashtree.Kernels.X86Win.SseX1

/-!
# R5: the Win64 ABI model for the windows `sse_x1` kernel

The windows stream is the linux stream with a Win64 prologue and epilogue and the general
registers renamed:

```
linux   : push rbx, rbp, r12-r15 ; sub rsp,88  ; <body at pc 7>  ; add rsp,88  ; 6 pops ; ret
windows : push rbx, r8, rsi, rdi, rbp, r12-r15 ; sub rsp,192
          ; 8 xmm saves at [rsp+64..192) ; <body at pc 18>
          ; 8 xmm restores ; add rsp,192 ; 9 pops ; ret
```

The body is instruction for instruction the linux body under the register permutation `F`
below and a program-counter shift of 11 instructions; the stack displacements are **not**
shifted (the shipping code uses the same low offsets `[rsp, rsp+64)` in both frames, it only
reserves a larger frame on windows).  `sse_body_correspondence` proves that over the shipped
arrays (4180 instructions).

The frame facts:

* `sse_stack_footprint` -- every `rsp`-based operand of the kernel has `0 <= disp` and
  `disp + width <= 192`; with `sse_rsp_balanced` (`sub rsp,192` at pc 9, `add rsp,192` at pc
  4206, no other write of `rsp`) the memory touched relative to the running `rsp` is
  `[rsp, rsp+192)` = `[entry_rsp-264, entry_rsp-72)`, i.e. below the nine pushed words
  `[entry_rsp-72, entry_rsp)` and therefore below the return address `[entry_rsp,
  entry_rsp+8)`; the Win64 shadow space `[entry_rsp+8, entry_rsp+40)` is never touched.
* `sse_body_footprint` -- the body itself only uses `[rsp, rsp+64)`; the 128-byte
  `xmm6`-`xmm13` save area `[rsp+64, rsp+192)` is touched by the prologue and epilogue only
  (`sse_save_slots_untouched`, `sse_prologue_saves`, `sse_epilogue_restores`).
* `sse_prologue_pushes` / `sse_epilogue_pops` -- the nine pushed general registers are popped
  in exactly the reverse order, so every pushed value is restored; the pushed set contains all
  of the Win64 callee-saved general registers (`sse_callee_saved_covered`).
* `sse_callee_vec_split`, `sse_no_xmm14_15` -- the callee-saved vector set `xmm6`-`xmm15` is
  `xmm6`-`xmm13` (saved and restored above) plus `xmm14`, `xmm15` (never written by the
  shipped kernel).

Not proved here (same gap as `shani_x2`, see `formal/notes/R5.md` section 6): the semantic
lifting of these facts into an invariant of the run, and the functional contract.  The kernel
with a complete windows functional contract is `avx512_x16` (`Proofs.WinAvx512`).
-/

open Hashtree.Asm Hashtree.Asm.X86
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinSseX1

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.SseX1.prog
abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.SseX1.prog

/-- Number of body instructions shared by the two streams (linux pcs 7..4186, windows pcs
18..4197). -/
def bodyLen : Nat := 4180

/-! ## The register permutation -/

/-- linux -> windows general register numbering: the linux argument registers `rdi`, `rsi`,
`rdx` become the Win64 argument registers `rcx`, `rdx`, `r8` (7->1, 6->2, 2->8), and the linux
`rcx`, `rax` become `rdi`, `rsi` (1->7, 8->6).  `rsp`, `rbx`, `rbp` and `r9`-`r15` are fixed. -/
def F : Nat → Nat
  | 1 => 7 | 2 => 8 | 6 => 2 | 7 => 1 | 8 => 6 | j => j

/-- windows -> linux general register numbering (the inverse of `F`). -/
def G : Nat → Nat
  | 7 => 1 | 8 => 2 | 2 => 6 | 1 => 7 | 6 => 8 | j => j

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

/-- Shift every branch target by `p` instructions (the windows body starts 11 instructions
later). -/
def shiftTgt (p : Nat) : Instr → Instr
  | .jcc c t => .jcc c (t + p)
  | .jmp t => .jmp (t + p)
  | i => i

/-- linux body instruction -> the corresponding windows body instruction.  The stack
displacements are unchanged (both streams use the same low `rsp` offsets). -/
def bodyI (f : Nat → Nat) (p : Nat) (i : Instr) : Instr := shiftTgt p (rlI f i)

/-- The instruction-by-instruction comparison of the two shipped bodies. -/
def bodyOk (n : Nat) : Bool :=
  (List.range n).all (fun j =>
    decide (winProg[18 + j]? = (linuxProg[7 + j]?).map (bodyI F 11)))

/-- Machine-checked: the 4180 body instructions of the windows stream are the linux ones
renamed and re-based.  The comparison is a compiled evaluation (`native_decide`): the kernel
reducer needs many minutes for an array of this size, so this theorem carries a
`native_decide` axiom, the same kind of compiled witness the Gen certificates use for their
`bv_decide` obligations. -/
theorem bodyOk_full : bodyOk bodyLen = true := by native_decide

/-- Pointwise form of `bodyOk_full`. -/
theorem sse_body_correspondence :
    ∀ j, j < bodyLen →
      winProg[18 + j]? = (linuxProg[7 + j]?).map (bodyI F 11) := by
  intro j hj
  have hm : j ∈ List.range bodyLen := List.mem_range.mpr hj
  have h := List.all_eq_true.mp bodyOk_full j hm
  simpa [bodyOk, bodyLen] using h

/-! ## Stack footprint -/

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

/-- Every stack access of the shipped windows kernel stays inside `[rsp, rsp + 192)`, i.e.
inside `[entry_rsp-264, entry_rsp-72)` after the nine pushes and `sub rsp,192`.  The return
address and the shadow space are never touched. -/
theorem sse_stack_footprint : winProg.toList.all (refsIn 0 192) = true := by
  native_decide

/-- The body only uses `[rsp, rsp + 64)`; the save area starts at `rsp + 64`. -/
theorem sse_body_footprint :
    ((winProg.toList.drop 18).take bodyLen).all (refsIn 0 64) = true := by
  native_decide

/-! ## Callee-saved general registers -/

/-- The general registers an instruction writes. -/
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

/-- Registers saved by the prologue, in push order. -/
def savedGprs : List Nat := [3, 8, 6, 7, 5, 12, 13, 14, 15]

/-- The nine prologue pushes, in order. -/
theorem sse_prologue_pushes :
    (List.range 9).all (fun k => decide (winProg[k]? = some (.push (savedGprs.getD k 0)))) = true := by
  decide +kernel

/-- The nine epilogue pops, in exactly the reverse order. -/
theorem sse_epilogue_pops :
    (List.range 9).all (fun k => decide (winProg[4207 + k]? =
      some (.pop (savedGprs.reverse.getD k 0)))) = true := by
  decide +kernel

/-- The pushed set contains every Win64 callee-saved general register. -/
theorem sse_callee_saved_covered :
    winCalleeGpr.all (fun r => savedGprs.contains r) = true := by
  decide

/-- `push`/`pop` are exempt from the "does not write `rsp`" scan below (they adjust `rsp` by
one word each and are matched one for one by the prologue/epilogue theorems). -/
def rspOk (i : Instr) : Bool :=
  match i with
  | .push _ => true
  | .pop _ => true
  | i => (writesGpr i).all (fun r => decide (r ≠ rsp))

/-- The only stack-pointer adjustments besides `push`/`pop` are the prologue's `sub rsp,192`
(pc 9) and the epilogue's `add rsp,192` (pc 4206): no other instruction writes `rsp`.  The
`push`/`pop` instructions are exempted here and are matched one for one by
`sse_prologue_pushes`/`sse_epilogue_pops`, so together with the two `192` adjustments the
frame is entered and left with the same `rsp`. -/
theorem sse_rsp_balanced :
    winProg[9]? = some (.sub 64 rsp (.imm 192))
      ∧ winProg[4206]? = some (.alu .add 64 rsp (.imm 192))
      ∧ (List.range 4243).all (fun j => decide (j ≠ 9 → j ≠ 4206 →
          rspOk (winProg[j]?.getD .nop))) = true := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  native_decide

/-! ## The callee-saved vector save area -/

/-- The prologue's eight `xmm6`-`xmm13` saves, slot for slot, at `[rsp+64, rsp+192)`. -/
theorem sse_prologue_saves :
    (List.range 8).all (fun k => decide (winProg[10 + k]? =
      some (.vstore 4 { base := some rsp, disp := (64 + 16 * (k : Int)) } (6 + k)))) = true := by
  decide +kernel

/-- The epilogue's eight restores, from the addresses the prologue saved them to. -/
theorem sse_epilogue_restores :
    (List.range 8).all (fun k => decide (winProg[4198 + k]? =
      some (.vload false 4 (6 + k) (.mem { base := some rsp, disp := (64 + 16 * (k : Int)) })))) = true := by
  decide +kernel

/-- No instruction of the body accesses the 128-byte save area `[rsp+64, rsp+192)`. -/
theorem sse_save_slots_untouched :
    ((winProg.toList.drop 18).take bodyLen).all (fun i =>
      (memRefs i).all (fun mw => !(rspBased mw.1) || decide (mw.1.disp + (mw.2 : Int) ≤ 64)
        || decide (192 ≤ mw.1.disp))) = true := by
  native_decide

/-- The vector registers written by an instruction. -/
def writesVec : Instr → List Nat
  | .vop _ _ _ d _ _ => [d]
  | .vshift _ _ _ d _ _ => [d]
  | .vshiftq _ _ d _ _ => [d]
  | .vror _ d _ _ => [d]
  | .vtern _ d _ _ _ => [d]
  | .vload _ _ d _ => [d]
  | .pshufd _ d _ _ => [d]
  | .pshufb _ _ d _ _ => [d]
  | .palignr _ d _ _ _ => [d]
  | .pblendw d _ _ => [d]
  | .shufps _ d _ _ _ => [d]
  | .perm2f128 d _ _ _ => [d]
  | .inserti128 d _ _ _ => [d]
  | .inserti64x4 d _ _ _ => [d]
  | .permi2d d _ _ => [d]
  | .permi2q d _ _ => [d]
  | .sha256rnds2 d _ => [d]
  | .sha256msg1 d _ => [d]
  | .sha256msg2 d _ => [d]
  | _ => []

/-- The vector registers the prologue saves, `xmm6`-`xmm13`, in save order. -/
def savedVecs : List Nat := [6, 7, 8, 9, 10, 11, 12, 13]

/-- The Win64 callee-saved vector set is `xmm6`-`xmm13` (saved and restored) followed by
`xmm14`, `xmm15` (never written). -/
theorem sse_callee_vec_split : winCalleeVec = savedVecs ++ [14, 15] := by decide

/-- No instruction of the shipped kernel writes `xmm14` or `xmm15`; together with
`sse_prologue_saves`/`sse_epilogue_restores` this covers every Win64 callee-saved vector
register. -/
theorem sse_no_xmm14_15 :
    winProg.toList.all (fun i => (writesVec i).all (fun r => decide (r ≠ 14 ∧ r ≠ 15))) = true := by
  native_decide

end Hashtree.Proofs.WinSseX1
