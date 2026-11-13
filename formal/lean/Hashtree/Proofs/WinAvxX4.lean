import Hashtree.Proofs.WinSseX1
import Hashtree.Kernels.X86.AvxX4
import Hashtree.Kernels.X86Win.AvxX4

/-!
# R5: the Win64 ABI/frame model for the windows `avx_x4` kernel

The shipped windows `avx_x4` stream (`Hashtree.Kernels.X86Win.AvxX4.prog`, 4163 instructions)
has the layout

```
pc 0        nop                       (endbr64)
pc 1, 2, 3  cmp r8,0 ; jne 4 ; ret    (null-length early return)
pc 4        sub rsp,568               (the frame)
pc 5..14    vstore 4 [rsp+384+16k] (xmm{6+k})     (the ten callee-saved xmm saves)
pc 15       cmp r8,4                  (loop guard)
pc 16       jl 4151                   (loop exit, into the epilogue)
pc 17..4149 loop body                 (4133 instructions)
pc 4150     jmp 15                    (loop back)
pc 4151..4160 vload 4 (xmm{6+k}) [rsp+384+16k]    (the ten restores)
pc 4161     add rsp,568
pc 4162     jmp hashtree_sha256_avx_x1            (tail call, leaves the frame)
```

Unlike `sse_x1`/`avx_x1` this kernel pushes no general registers: it touches only `rax`, `rcx`,
`rdx`, `r8`, `r9` and `rsp` (`avx_x4_callee_gpr_untouched`), and it saves and restores the whole
Win64 callee-saved vector set `xmm6`-`xmm15` (`avx_x4_callee_vec_covered`).

Everything here is a kernel-checked scan of the shipped array (`decide +kernel`, one 2048-
instruction slice at a time; no `native_decide`).  The model is static: it fixes the frame
footprint and the control-flow skeleton that a dynamic frame/functional contract has to
consume, and it does not itself execute the kernel.

The **target map** (`avx_x4_sites`) is recorded explicitly because it is *not* a constant shift
of the linux stream: the body is re-based by 10 (`linux pc 7 -> windows pc 17`) up to the
`jmp` at windows pc 704, and by 9 after it (`linux pc 1726 -> windows pc 1735`), and the
windows stream has its own loop head (15), exit (4151) and tail target
(`hashtree_sha256_avx_x1`).
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinScan
open Hashtree.Proofs.WinSseX1 (memRefs rspBased refIn refsIn writesGpr rspOk writesVec)
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvxX4

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.AvxX4.prog

/-- Number of instructions of the loop (windows pcs `15..4150`). -/
def loopLen : Nat := 4136

theorem size_eq : winProg.size = 4163 := by decide +kernel

/-! ## The control-flow skeleton -/

/-- The frame instructions of the shipped stream, at their pcs. -/
theorem frame_layout :
    winProg[4]? = some (.sub 64 rsp (.imm 568))
      ∧ winProg[15]? = some (.cmp 64 8 (.imm 4))
      ∧ winProg[16]? = some (.jcc .l 4151)
      ∧ winProg[4150]? = some (.jmp 15)
      ∧ winProg[4161]? = some (.alu .add 64 rsp (.imm 568))
      ∧ winProg[4162]? = some (.jmpTail "hashtree_sha256_avx_x1") := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

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

/-- **The target map of the windows `avx_x4` stream**, kernel-checked: two early exits of the
null-length guard (`jne` to the frame setup, `ret`), the loop guard `jl 4151`, three jumps
inside the body, the loop-back `jmp 15`, and the tail call. -/
theorem avx_x4_sites :
    sites = [(2, some 4), (3, none), (16, some 4151), (704, some 706), (1715, some 706),
      (1735, some 1738), (4150, some 15), (4162, none)] := by
  decide +kernel

/-- Every in-stream target of the stream is a valid instruction index: no branch leaves the
array.  (`ret` and the tail call leave the *stream*, and are recorded as `none`.) -/
theorem avx_x4_targets_in_range :
    (sites.map (fun e => e.2)).all (fun o => match o with
      | some t => decide (t < 4163)
      | none => true) = true := by
  decide +kernel

/-- The two targets of the loop's own control flow: the loop-back goes to the head `15`, and the
loop exit goes to the epilogue head `4151`.  This is the pc invariant a loop-trajectory argument
has to consume. -/
theorem avx_x4_loop_edges :
    winProg[4150]? = some (.jmp 15) ∧ winProg[16]? = some (.jcc .l 4151) := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- The tail-call targets of the stream, kernel-checked. -/
def tailsAux : List Instr → List String
  | [] => []
  | .jmpTail n :: is => n :: tailsAux is
  | .jccTail _ n :: is => n :: tailsAux is
  | _ :: is => tailsAux is

theorem avx_x4_tails : tailsAux winProg.toList = ["hashtree_sha256_avx_x1"] := by
  decide +kernel

/-! ## The frame footprint -/

/-- Every stack access of the shipped kernel stays inside `[rsp, rsp + 568)`, i.e. inside
`[entry_rsp - 576, entry_rsp - 8)` after `sub rsp,568`.  The return address `[entry_rsp,
entry_rsp+8)` and the Win64 shadow space `[entry_rsp+8, entry_rsp+40)` are never touched. -/
theorem avx_x4_stack_footprint : winProg.toList.all (refsIn 0 568) = true := by
  apply all_take_drop _ winProg.toList 2048
  · decide +kernel
  apply all_take_drop _ (winProg.toList.drop 2048) 2048
  · decide +kernel
  decide +kernel

/-- The loop only uses `[rsp, rsp + 384)`; the save area starts at `rsp + 384`. -/
theorem avx_x4_body_footprint :
    ((winProg.toList.drop 15).take loopLen).all (refsIn 0 384) = true := by
  change ((winProg.toList.drop 15).take 4136).all (refsIn 0 384) = true
  apply all_take_drop _ ((winProg.toList.drop 15).take 4136) 2048
  · decide +kernel
  apply all_take_drop _ (((winProg.toList.drop 15).take 4136).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-! ## Callee-saved general registers -/

/-- No instruction writes a Win64 callee-saved general register: the kernel uses only `rax`,
`rcx`, `rdx`, `r8`, `r9` and `rsp`. -/
theorem avx_x4_callee_gpr_untouched :
    winProg.toList.all (fun i => (writesGpr i).all (fun r =>
      decide (r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 7 ∧ r ≠ 6 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 14 ∧ r ≠ 15))) = true := by
  apply all_take_drop _ winProg.toList 2048
  · decide +kernel
  apply all_take_drop _ (winProg.toList.drop 2048) 2048
  · decide +kernel
  decide +kernel

/-- The stack pointer is adjusted in exactly two instructions, the prologue's `sub rsp,568`
(pc 4) and the epilogue's `add rsp,568` (pc 4161); every other instruction leaves `rsp` alone,
so the frame is entered and left with the same `rsp`.  The three scans cover pcs `0..3`,
`5..4160` and `4162`. -/
theorem avx_x4_rsp_balanced :
    winProg[4]? = some (.sub 64 rsp (.imm 568))
      ∧ winProg[4161]? = some (.alu .add 64 rsp (.imm 568))
      ∧ (winProg.toList.take 4).all rspOk = true
      ∧ ((winProg.toList.drop 5).take 4156).all rspOk = true
      ∧ (winProg.toList.drop 4162).all rspOk = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  apply all_take_drop _ ((winProg.toList.drop 5).take 4156) 2048
  · decide +kernel
  apply all_take_drop _ (((winProg.toList.drop 5).take 4156).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-! ## The callee-saved vector save area -/

/-- The ten prologue saves, slot for slot: `xmm{6+k}` at `[rsp+384+16k]`, pcs `5..14`. -/
theorem avx_x4_prologue_saves :
    (List.range 10).all (fun k => decide (winProg[5 + k]? =
      some (.vstore 4 { base := some rsp, disp := (384 + 16 * (k : Int)) } (6 + k)))) = true := by
  decide +kernel

/-- The ten epilogue restores, from the addresses the prologue saved them to, pcs `4151..4160`. -/
theorem avx_x4_epilogue_restores :
    (List.range 10).all (fun k => decide (winProg[4151 + k]? =
      some (.vload true 4 (6 + k) (.mem { base := some rsp, disp := (384 + 16 * (k : Int)) })))) = true := by
  decide +kernel

/-- No instruction of the loop accesses the 160-byte save area `[rsp+384, rsp+544)`. -/
theorem avx_x4_save_slots_untouched :
    ((winProg.toList.drop 15).take loopLen).all (fun i =>
      (memRefs i).all (fun mw => !(rspBased mw.1) || decide (mw.1.disp + (mw.2 : Int) ≤ 384)
        || decide (544 ≤ mw.1.disp))) = true := by
  change ((winProg.toList.drop 15).take 4136).all (fun i =>
    (memRefs i).all (fun mw => !(rspBased mw.1) || decide (mw.1.disp + (mw.2 : Int) ≤ 384)
      || decide (544 ≤ mw.1.disp))) = true
  apply all_take_drop _ ((winProg.toList.drop 15).take 4136) 2048
  · decide +kernel
  apply all_take_drop _ (((winProg.toList.drop 15).take 4136).drop 2048) 2048
  · decide +kernel
  decide +kernel

/-- The vector registers the prologue saves: the whole Win64 callee-saved set. -/
def savedVecs : List Nat := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The saved set is exactly the Win64 callee-saved vector set, so `xmm6`-`xmm15` are covered
without a "never written" side condition (unlike `sse_x1`/`avx_x1`, which never touch
`xmm14`/`xmm15`). -/
theorem avx_x4_callee_vec_covered : winCalleeVec.all (fun r => savedVecs.contains r) = true := by
  decide

/-! ## The linux reference stream and the non-constant site pairing -/

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.AvxX4.prog

/-- The control-flow sites of the linux stream, kernel-checked. -/
theorem avx_x4_linux_sites :
    sitesAux 0 linuxProg.toList =
      [(2, some 4), (3, none), (6, some 4142), (694, some 697), (1706, some 697),
        (1726, some 1729), (4141, some 5), (4143, none)] := by
  decide +kernel

/-- The linux and windows control-flow **pc** sites, paired in order.  The pairing is **not** a
constant pc shift: `2 -> 2`, `3 -> 3`, `6 -> 16` (= +10, the ten xmm saves), `694 -> 704`
(+10), `1706 -> 1715` (+9), `1726 -> 1735` (+9), `4141 -> 4150` (+9), `4143 -> 4162` (+19).
Likewise the targets: `4 -> 4`, `4142 -> 4151` (+9), `697 -> 706` (+9), `1729 -> 1738` (+9),
`5 -> 15` (+10).  A single `shiftPc p` therefore cannot describe this stream; the model records
the target map explicitly, and a composition has to carry the pc map as data. -/
theorem avx_x4_site_pc_shifts :
    ((sitesAux 0 linuxProg.toList).map (fun e => e.1)).zip (sites.map (fun e => e.1)) =
      [(2, 2), (3, 3), (6, 16), (694, 704), (1706, 1715), (1726, 1735), (4141, 4150),
        (4143, 4162)] := by
  decide +kernel

/-- The same pairing on the targets: `4 -> 4`, `4142 -> 4151` (+9), `697 -> 706` (+9),
`1729 -> 1738` (+9), `5 -> 15` (+10).  The shift of the *targets* is non-constant too. -/
theorem avx_x4_target_pairs :
    ((sitesAux 0 linuxProg.toList).map (fun e => e.2)).zip (sites.map (fun e => e.2)) =
      [(some 4, some 4), (none, none), (some 4142, some 4151), (some 697, some 706),
        (some 697, some 706), (some 1729, some 1738), (some 5, some 15), (none, none)] := by
  decide +kernel

end Hashtree.Proofs.WinAvxX4
