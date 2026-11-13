import Hashtree.Proofs.WinSseX1
import Hashtree.Kernels.X86.Avx2X8
import Hashtree.Kernels.X86Win.Avx2X8

/-!
# R5: the Win64 ABI/frame model for the windows `avx2_x8` kernel

The shipped windows `avx2_x8` stream (`Hashtree.Kernels.X86Win.Avx2X8.prog`, 6107 instructions)
has the layout

```
pc 0        nop                       (endbr64)
pc 1, 2, 3  cmp r8,0 ; jne 4 ; ret    (null-length early return)
pc 4        push rbp
pc 5        push rsi
pc 6        mov rbp,rsp               (records the post-push rsp)
pc 7        and rsp,-32               (32-byte alignment)
pc 8        sub rsp,1248              (the frame)
pc 9..12    movst 64 [rsp+896+8k] (r12+k)          (r12-r15)
pc 13..22   vstore 8 [rsp+928+32k] (ymm{6+k})      (ymm6-ymm15)
pc 23       cmp r8,8                  (loop guard)
pc 24       jb 6086                   (loop exit, into the epilogue)
pc 25..6084 loop body                 (6060 instructions)
pc 6085     jmp 23                    (loop back)
pc 6086..6095 vload 8 (ymm{6+k}) [rsp+928+32k]     (the ten vector restores)
pc 6096..6099 mov (r12+k) [rsp+896+8k]             (the four general restores)
pc 6100     mov rsp,rbp               (undo `and`/`sub`)
pc 6101     pop rsi
pc 6102     pop rbp
pc 6103     jmp hashtree_sha256_avx_x4            (tail call)
```

The frame is entered with `rsp` restored from `rbp`, so the alignment `and rsp,-32` and the
`sub rsp,1248` are fully undone regardless of the entry `rsp` (that is `avx2x8_rsp_chain`); the
only residue is that the frame base is the aligned value `A = (entry_rsp - 16) & -32`, which is
below the pushed words whenever the stack has room for the frame (`avx2x8_frame_below`).

As for `avx_x4`, the windows stream is **not** a renaming of the linux stream
(`Hashtree.Kernels.X86.Avx2X8`): the register allocation and the `rip`-relative `.rodata`
offsets differ instruction by instruction, so `avx2x8_site_pc_shifts` records the pc map as
data instead of deriving it from a constant shift.

Everything here is a kernel-checked scan of the shipped arrays (`decide +kernel`, one 2048-
instruction slice at a time; no `native_decide`).
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinScan
open Hashtree.Proofs.WinSseX1 (memRefs rspBased refIn refsIn writesGpr rspOk writesVec)
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvx2X8

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Avx2X8.prog

/-- Number of instructions of the loop (windows pcs `23..6085`). -/
def loopLen : Nat := 6063

theorem size_eq : winProg.size = 6107 := by decide +kernel

/-! ## The control-flow skeleton -/

/-- The frame instructions of the shipped stream, at their pcs. -/
theorem frame_layout :
    winProg[0]? = some .nop
      ∧ winProg[1]? = some (.cmp 64 8 (.imm 0))
      ∧ winProg[2]? = some (.jcc .ne 4)
      ∧ winProg[3]? = some .ret
      ∧ winProg[4]? = some (.push 5)
      ∧ winProg[5]? = some (.push 6)
      ∧ winProg[6]? = some (.mov 64 5 (.reg 4))
      ∧ winProg[7]? = some (.alu .and 64 rsp (.imm (-32)))
      ∧ winProg[8]? = some (.sub 64 rsp (.imm 1248))
      ∧ winProg[23]? = some (.cmp 64 8 (.imm 8))
      ∧ winProg[24]? = some (.jcc .b 6086)
      ∧ winProg[6085]? = some (.jmp 23)
      ∧ winProg[6100]? = some (.mov 64 rsp (.reg 5))
      ∧ winProg[6101]? = some (.pop 6)
      ∧ winProg[6102]? = some (.pop 5)
      ∧ winProg[6103]? = some (.jmpTail "hashtree_sha256_avx_x4") := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The control-flow sites of an instruction: `some none` for the two ways out of the stream
(`ret` and a tail call), `some (some t)` for a branch inside it, `none` otherwise. -/
def ctlSite : Instr → Option (Option Nat)
  | .jcc _ t => some (some t)
  | .jmp t => some (some t)
  | .jccTail _ _ => some none
  | .jmpTail _ => some none
  | .ret => some none
  | _ => none

/-- The control-flow sites of a stream with their pcs, as a structural fold (kernel-reducible;
`List.filterMap` over an index range is not). -/
def sitesAux : Nat → List Instr → List (Nat × Option Nat)
  | _, [] => []
  | pc, i :: is =>
    (match ctlSite i with | some t => [(pc, t)] | none => []) ++ sitesAux (pc + 1) is

/-- The target map of the shipped stream. -/
def sites : List (Nat × Option Nat) := sitesAux 0 winProg.toList

/-- **The target map of the windows `avx2_x8` stream**, kernel-checked: the null-length guard
(branch + `ret`), the loop guard `jb 6086`, the loop-back `jmp 23`, and the tail call. -/
theorem avx2x8_sites :
    sites = [(2, some 4), (3, none), (24, some 6086), (6085, some 23), (6103, none)] := by
  decide +kernel

/-- Every in-stream target of the stream is a valid instruction index. -/
theorem avx2x8_targets_in_range :
    (sites.map (fun e => e.2)).all (fun o => match o with
      | some t => decide (t < 6107)
      | none => true) = true := by
  decide +kernel

/-- The two targets of the loop's own control flow: the loop-back goes to the head `23`, and the
loop exit goes to the epilogue head `6086`. -/
theorem avx2x8_loop_edges :
    winProg[6085]? = some (.jmp 23) ∧ winProg[24]? = some (.jcc .b 6086) := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- The tail-call targets of the stream, kernel-checked. -/
def tailsAux : List Instr → List String
  | [] => []
  | .jmpTail n :: is => n :: tailsAux is
  | .jccTail _ n :: is => n :: tailsAux is
  | _ :: is => tailsAux is

theorem avx2x8_tails : tailsAux winProg.toList = ["hashtree_sha256_avx_x4"] := by
  decide +kernel

/-! ## The frame footprint -/

/-- Every stack access of the shipped kernel stays inside `[rsp, rsp + 1248)`, i.e. inside the
frame between the aligned base and the two pushed words.  The return address and the Win64
shadow space are never touched. -/
theorem avx2x8_stack_footprint : winProg.toList.all (refsIn 0 1248) = true := by
  apply all_take_drop _ winProg.toList 2048
  · decide +kernel
  apply all_take_drop _ (winProg.toList.drop 2048) 2048
  · decide +kernel
  apply all_take_drop _ (winProg.toList.drop 4096) 2048
  · decide +kernel
  decide +kernel

/-- The loop only uses `[rsp, rsp + 896)`; the save area starts at `rsp + 896`. -/
theorem avx2x8_body_footprint :
    ((winProg.toList.drop 23).take loopLen).all (refsIn 0 896) = true := by
  change ((winProg.toList.drop 23).take 6063).all (refsIn 0 896) = true
  apply all_take_drop _ ((winProg.toList.drop 23).take 6063) 2048
  · decide +kernel
  apply all_take_drop _ (((winProg.toList.drop 23).take 6063).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-- The frame `[A-1248, A)` lies below the two pushed words `[e-16, e)` (and hence below the
return address at `e` and the shadow space above it) as soon as the aligned base `A` is not
above `e-16` and the stack has room for the frame.  `A = (e-16) & -32` satisfies the first
hypothesis; the second is the usual "the frame fits on the stack" side condition. -/
theorem avx2x8_frame_below (A e : Int) (hA : A ≤ e - 16) (hfit : 1248 ≤ A) :
    A - 1248 + 1248 ≤ e - 16 := by
  rw [show A - 1248 + 1248 = A from by omega]
  exact hA

/-! ## Callee-saved general registers -/

/-- The two pushed general registers, in push order. -/
def savedPush : List Nat := [5, 6]

/-- The four general registers saved by `movst` into `[rsp+896+8k]`. -/
def savedMov : List Nat := [12, 13, 14, 15]

/-- The two prologue pushes. -/
theorem avx2x8_prologue_pushes :
    (List.range 2).all (fun k => decide (winProg[4 + k]? = some (.push (savedPush.getD k 0)))) = true := by
  decide +kernel

/-- The two epilogue pops, in exactly the reverse order. -/
theorem avx2x8_epilogue_pops :
    (List.range 2).all (fun k => decide (winProg[6101 + k]? =
      some (.pop (savedPush.reverse.getD k 0)))) = true := by
  decide +kernel

/-- The four `movst` saves, at `[rsp+896+8k]`, pcs `9..12`. -/
theorem avx2x8_prologue_gpr_saves :
    (List.range 4).all (fun k => decide (winProg[9 + k]? =
      some (.movst 64 { base := some rsp, disp := (896 + 8 * (k : Int)) } (12 + k)))) = true := by
  decide +kernel

/-- The four epilogue restores, from the same slots, pcs `6096..6099`. -/
theorem avx2x8_epilogue_gpr_restores :
    (List.range 4).all (fun k => decide (winProg[6096 + k]? =
      some (.mov 64 (12 + k) (.mem { base := some rsp, disp := (896 + 8 * (k : Int)) })))) = true := by
  decide +kernel

/-- A scan that forbids writes of the whole Win64 callee-saved set. -/
def calleeFreeB (i : Instr) : Bool := (writesGpr i).all (fun r =>
  decide (r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 6 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 14 ∧ r ≠ 15))

/-- A scan that forbids writes of `rbx` and `rdi` (never used by this kernel). -/
def noRbxRdiB (i : Instr) : Bool := (writesGpr i).all (fun r => decide (r ≠ 3 ∧ r ≠ 7))

/-- A scan that allows `rbp` only (the `mov rbp,rsp` at pc 6). -/
def onlyRbpB (i : Instr) : Bool := (writesGpr i).all (fun r =>
  decide (r ≠ 3 ∧ r ≠ 7 ∧ r ≠ 6 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 14 ∧ r ≠ 15))

/-- A scan that allows `rsi` only (the loop's `.rodata` base scratch, pcs 25, 34, 3709, 3726). -/
def onlyRsiB (i : Instr) : Bool := (writesGpr i).all (fun r =>
  decide (r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 14 ∧ r ≠ 15))

/-- A scan that allows `rsi` and `rbp` only (the two pops at pcs 6101, 6102). -/
def onlyRsiRbpB (i : Instr) : Bool := (writesGpr i).all (fun r =>
  decide (r ≠ 3 ∧ r ≠ 7 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 14 ∧ r ≠ 15))

/-- A scan that allows `r12`-`r15` only (the four `mov` restores at pcs 6096..6099). -/
def onlyR12to15B (i : Instr) : Bool := (writesGpr i).all (fun r =>
  decide (r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 6))

/-- **The general-register accounting of the shipped kernel.**  `rbx` and `rdi` are never
written at all; `rbp` is written only by the `mov rbp,rsp` at pc 6 (after the push at pc 4) and
restored by `mov rsp,rbp`/`pop rbp`; `rsi` is written only inside `(5, 6101)` (its push and pop
bracket it); `r12`-`r15` are written only by the four restores, which read the slots written at
pcs 9..12.  Together with `avx2x8_prologue_gpr_saves`/`avx2x8_epilogue_gpr_restores` and
`avx2x8_prologue_pushes`/`avx2x8_epilogue_pops`, every Win64 callee-saved general register is
preserved.

The scans cover pcs `0..5`, `7..6095`, `6096..6099` and `6100..`; pc 6 is the single
`onlyRbpB` check. -/
theorem avx2x8_callee_gpr_untouched :
    winProg.toList.all noRbxRdiB = true
      ∧ (winProg.toList.take 6).all calleeFreeB = true
      ∧ onlyRbpB (winProg.getD 6 .nop) = true
      ∧ ((winProg.toList.drop 7).take 6089).all onlyRsiB = true
      ∧ (List.range 4).all (fun k => onlyR12to15B (winProg.getD (6096 + k) .nop)) = true
      ∧ (winProg.toList.drop 6100).all onlyRsiRbpB = true := by
  refine ⟨?_, by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  · apply all_take_drop _ winProg.toList 2048
    · decide +kernel
    apply all_take_drop _ (winProg.toList.drop 2048) 2048
    · decide +kernel
    apply all_take_drop _ (winProg.toList.drop 4096) 2048
    · decide +kernel
    decide +kernel
  · apply all_take_drop _ ((winProg.toList.drop 7).take 6089) 2048
    · decide +kernel
    apply all_take_drop _ (((winProg.toList.drop 7).take 6089).drop 2048) 2048
    · decide +kernel
    decide +kernel

/-- The pushed set (`rbp`, `rsi`), the `movst`-saved set (`r12`-`r15`) and the two registers the
kernel never writes (`rbx`, `rdi`) together cover every Win64 callee-saved general register. -/
theorem avx2x8_callee_saved_covered :
    winCalleeGpr.all (fun r => savedPush.contains r || savedMov.contains r
      || r == 3 || r == 7) = true := by
  decide

/-- **The `rsp` chain.**  The two pushes lower `rsp` by 16; `mov rbp,rsp` records that value;
the `and rsp,-32` and `sub rsp,1248` build the frame from it; the epilogue's `mov rsp,rbp`
restores the recorded value and the two pops lower it back to the entry `rsp`.  Hence the tail
call runs with the entry `rsp`, independently of the alignment. -/
theorem avx2x8_rsp_chain :
    winProg[6]? = some (.mov 64 5 (.reg 4))
      ∧ winProg[6100]? = some (.mov 64 rsp (.reg 5))
      ∧ ((List.range 2).all (fun k => decide (winProg[4 + k]? = some (.push (savedPush.getD k 0)))))
          = true
      ∧ ((List.range 2).all (fun k => decide (winProg[6101 + k]? =
          some (.pop (savedPush.reverse.getD k 0))))) = true
      := by
  exact ⟨by decide +kernel, by decide +kernel, avx2x8_prologue_pushes, avx2x8_epilogue_pops⟩

/-- The stack pointer is written in exactly six instructions: the two pushes (pcs 4, 5), the
alignment (pc 7), the frame reservation (pc 8), the restore from `rbp` (pc 6100) and the two
pops (pcs 6101, 6102).  Every other instruction leaves `rsp` alone.  The three scans cover
pcs `0..3`, `5..6` and `9..6099`, and the four excluded pcs are pinned by
`avx2x8_rsp_chain`/`frame_layout`. -/
theorem avx2x8_rsp_balanced :
    winProg[7]? = some (.alu .and 64 rsp (.imm (-32)))
      ∧ winProg[8]? = some (.sub 64 rsp (.imm 1248))
      ∧ (winProg.toList.take 4).all rspOk = true
      ∧ ((winProg.toList.drop 5).take 2).all rspOk = true
      ∧ ((winProg.toList.drop 9).take 6091).all rspOk = true
      ∧ (winProg.toList.drop 6101).all rspOk = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_,
    by decide +kernel⟩
  apply all_take_drop _ ((winProg.toList.drop 9).take 6091) 2048
  · decide +kernel
  apply all_take_drop _ (((winProg.toList.drop 9).take 6091).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-! ## The callee-saved vector save area -/

/-- The ten `ymm` saves, slot for slot: `ymm{6+k}` at `[rsp+928+32k]`, pcs `13..22`. -/
theorem avx2x8_prologue_vec_saves :
    (List.range 10).all (fun k => decide (winProg[13 + k]? =
      some (.vstore 8 { base := some rsp, disp := (928 + 32 * (k : Int)) } (6 + k)))) = true := by
  decide +kernel

/-- The ten `ymm` restores, pcs `6086..6095`. -/
theorem avx2x8_epilogue_vec_restores :
    (List.range 10).all (fun k => decide (winProg[6086 + k]? =
      some (.vload true 8 (6 + k) (.mem { base := some rsp, disp := (928 + 32 * (k : Int)) })))) = true := by
  decide +kernel

/-- No instruction of the loop accesses the save area `[rsp+896, rsp+1248)`. -/
theorem avx2x8_save_slots_untouched :
    ((winProg.toList.drop 23).take loopLen).all (fun i =>
      (memRefs i).all (fun mw => !(rspBased mw.1) || decide (mw.1.disp + (mw.2 : Int) ≤ 896)
        || decide (1248 ≤ mw.1.disp))) = true := by
  change ((winProg.toList.drop 23).take 6063).all (fun i =>
    (memRefs i).all (fun mw => !(rspBased mw.1) || decide (mw.1.disp + (mw.2 : Int) ≤ 896)
      || decide (1248 ≤ mw.1.disp))) = true
  apply all_take_drop _ ((winProg.toList.drop 23).take 6063) 2048
  · decide +kernel
  apply all_take_drop _ (((winProg.toList.drop 23).take 6063).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-- The vector registers the prologue saves: the whole Win64 callee-saved set. -/
def savedVecs : List Nat := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- `xmm6`-`xmm15` are all saved and restored, so the vector side of the ABI is discharged
without a "never written" side condition. -/
theorem avx2x8_callee_vec_covered : winCalleeVec.all (fun r => savedVecs.contains r) = true := by
  decide

/-! ## The linux reference stream and the non-constant pc map -/

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.Avx2X8.prog

/-- The control-flow sites of the linux stream, kernel-checked. -/
theorem avx2x8_linux_sites :
    sitesAux 0 linuxProg.toList =
      [(2, some 4), (3, none), (13, some 6074), (6073, some 12), (6080, none)] := by
  decide +kernel

/-- The linux and windows control-flow **pc** sites, paired in order.  The pc shift is not
constant: `2 -> 2`, `3 -> 3`, `13 -> 24` (+11, the extra saves), `6073 -> 6085` (+12),
`6080 -> 6103` (+23).  The targets shift by `+0`, `+12`, `+11` respectively (next theorem). -/
theorem avx2x8_site_pc_shifts :
    ((sitesAux 0 linuxProg.toList).map (fun e => e.1)).zip (sites.map (fun e => e.1)) =
      [(2, 2), (3, 3), (13, 24), (6073, 6085), (6080, 6103)] := by
  decide +kernel

/-- The same pairing on the targets. -/
theorem avx2x8_target_pairs :
    ((sitesAux 0 linuxProg.toList).map (fun e => e.2)).zip (sites.map (fun e => e.2)) =
      [(some 4, some 4), (none, none), (some 6074, some 6086), (some 12, some 23),
        (none, none)] := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8
