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
(`hashtree_sha256_avx_x1`).  `avx_x4_body_correspondence` proves the pointwise form: every body
instruction of the windows stream is the paired linux instruction renamed by `bodyI` (general
registers by `bodyReg`, branch targets by `bodyTgt`), with the pairing `bodyPc`; the two halves
of the piecewise pc map are the two zipped scans `avx_x4_body_lo_scan` / `avx_x4_body_hi_scan`.
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

/-! ## The body correspondence of the two shipped streams

The site pairing above compares the two streams only at their control-flow sites.  The theorem
below covers the rest: every one of the 4134 body instructions of the windows stream (pcs
`17..4150`) is the linux instruction of the paired pc, with general registers relabelled by
`bodyReg` and branch targets mapped by `bodyTgt`.  Because the windows prologue is shorter by
one instruction before the body and the linux `jmp` at pc 694 is one instruction shorter than
its windows counterpart at 704, the pc pairing is piecewise (`bodyPc`): `w - 10` up to pc 704,
`w - 9` after it; that is why the body is covered by two zipped scans instead of one. -/

/-- linux -> windows general register substitution of the `avx_x4` body, recovered from the two
streams: the linux scratch `rcx`, `rdx`, `rsi`, `rdi` are the windows `rax`, `r8`, `rdx`, `rcx`
(1->0, 2->8, 6->2, 7->1); `rsp`, `rbx`, `rbp`, `r8`, `r9` are fixed.  (Both streams use
different scratch allocations, so this is a substitution, not a permutation of the register
file.) -/
def bodyReg : Nat → Nat
  | 1 => 0 | 2 => 8 | 6 => 2 | 7 => 1 | j => j

/-- The **non-constant target map** of the body, as a function of the linux target: the linux
`jmp` at 5 (loop tail) becomes the windows loop head 15, and the linux body targets 697, 1729,
4142 become the windows 706, 1738, 4151 (+9, the shift of the body after the linux `jmp` at
pc 694); the linux early-return target 4 is unchanged. -/
def bodyTgt (t : Nat) : Nat :=
  if t = 4 then 4
  else if t = 5 then 15
  else if t = 697 then 706
  else if t = 1729 then 1738
  else if t = 4142 then 4151
  else t

/-- linux body instruction -> the corresponding windows body instruction. -/
def bodyI (i : Instr) : Instr :=
  match i with
  | .jcc c t => .jcc c (bodyTgt t)
  | .jmp t => .jmp (bodyTgt t)
  | i => rlI bodyReg i

/-- The piecewise linux pc of a windows body pc: `w - 10` up to the windows `jmp` at pc 704
(linux pc 694), `w - 9` after it. -/
def bodyPc (w : Nat) : Nat := if w < 705 then w - 10 else w - 9

/-- The target map realizes exactly the site pairing of `avx_x4_target_pairs`. -/
theorem avx_x4_bodyTgt_values :
    bodyTgt 4 = 4 ∧ bodyTgt 5 = 15 ∧ bodyTgt 697 = 706 ∧ bodyTgt 1729 = 1738
      ∧ bodyTgt 4142 = 4151 := by decide

/-- The pc map realizes exactly the site pairing of `avx_x4_site_pc_shifts`, and it is not a
constant shift: `bodyPc` is `w - 10` at the windows `jmp` pc 704 and `w - 9` at the loop head's
branch pc 1715. -/
theorem avx_x4_bodyPc_values :
    bodyPc 704 = 694 ∧ bodyPc 1715 = 1706 ∧ bodyPc 1735 = 1726 ∧ bodyPc 4150 = 4141
      ∧ bodyPc 705 = 696 := by decide

def bodyZipLo : List (Instr × Instr) :=
  ((winProg.toList.drop 17).take 688).zip ((linuxProg.toList.drop 7).take 688)

def bodyZipHi : List (Instr × Instr) :=
  ((winProg.toList.drop 705).take 3446).zip ((linuxProg.toList.drop 696).take 3446)

/-- Machine-checked: windows pcs `17..704` are linux pcs `7..694` renamed by `bodyI`. -/
theorem avx_x4_body_lo_scan : bodyZipLo.all (fun p => decide (p.1 = bodyI p.2)) = true := by
  change (((winProg.toList.drop 17).take 688).zip
    ((linuxProg.toList.drop 7).take 688)).all (fun p => decide (p.1 = bodyI p.2)) = true
  decide +kernel

/-- Machine-checked: windows pcs `705..4150` are linux pcs `696..4141` renamed by `bodyI`. -/
theorem avx_x4_body_hi_scan : bodyZipHi.all (fun p => decide (p.1 = bodyI p.2)) = true := by
  change (((winProg.toList.drop 705).take 3446).zip
    ((linuxProg.toList.drop 696).take 3446)).all (fun p => decide (p.1 = bodyI p.2)) = true
  decide +kernel

/-- Pointwise form of the lower half of the body correspondence. -/
theorem avx_x4_body_correspondence_lo :
    ∀ j, j < 688 → winProg[17 + j]? = (linuxProg[7 + j]?).map bodyI := by
  have hz : bodyZipLo.all (fun p => decide (p.1 = bodyI p.2)) = true := avx_x4_body_lo_scan
  have h := of_zip_scan (l1 := winProg.toList) (l2 := linuxProg.toList)
    (o1 := 17) (o2 := 7) (n := 688) (f := bodyI) (by decide) (by decide) hz
  intro j hj
  have := h j hj
  simpa using this

/-- Pointwise form of the upper half of the body correspondence. -/
theorem avx_x4_body_correspondence_hi :
    ∀ j, j < 3446 → winProg[705 + j]? = (linuxProg[696 + j]?).map bodyI := by
  have hz : bodyZipHi.all (fun p => decide (p.1 = bodyI p.2)) = true := avx_x4_body_hi_scan
  have h := of_zip_scan (l1 := winProg.toList) (l2 := linuxProg.toList)
    (o1 := 705) (o2 := 696) (n := 3446) (f := bodyI) (by decide) (by decide) hz
  intro j hj
  have := h j hj
  simpa using this

/-- **The body correspondence of the windows `avx_x4` stream**: every body instruction of the
windows stream is the paired linux instruction under `bodyI`, and the pairing is given by
`bodyPc` (piecewise, not a constant shift). -/
theorem avx_x4_body_correspondence :
    (∀ w, 17 ≤ w → w < 705 → winProg[w]? = (linuxProg[bodyPc w]?).map bodyI)
      ∧ (∀ w, 705 ≤ w → w < 4151 → winProg[w]? = (linuxProg[bodyPc w]?).map bodyI) := by
  refine ⟨fun w h1 h2 => ?_, fun w h1 h2 => ?_⟩
  · have hw : w < 705 := h2
    rw [bodyPc, ite_eq_left hw]
    have h := avx_x4_body_correspondence_lo (w - 17) (by omega)
    rwa [show 17 + (w - 17) = w from by omega, show 7 + (w - 17) = w - 10 from by omega] at h
  · have hw : ¬ w < 705 := by omega
    rw [bodyPc, ite_eq_right hw]
    have h := avx_x4_body_correspondence_hi (w - 705) (by omega)
    rwa [show 705 + (w - 705) = w from by omega, show 696 + (w - 705) = w - 9 from by omega] at h

end Hashtree.Proofs.WinAvxX4
