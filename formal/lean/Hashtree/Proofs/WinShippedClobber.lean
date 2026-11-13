import Hashtree.Proofs.WinAvx2X8
import Hashtree.Kernels.X86Win.WrapperWindows

/-!
# R5: the shipped windows frame is concretely corrupt for `avx2_x8`

`wrapper_kernelW_shipped` (`Proofs/WinWrapper`) proves that the linux-style footprint claim
`Foot (σ 9) 2056` is false for the shipped `$1024` frame: the text's `ADDQ $2048, SP` places
the aligned call `rsp` 985..1016 bytes *above* the wrapper's entry `rsp`, so the kernel's stack
frame occupies the caller's stack words.  This file upgrades that statement from "the footprint
claim is false" to the concrete overwrite, using only the shipped instruction array and
arithmetic --- no machine run and no kernel contract:

* the `avx2_x8` loop body (`pc` 25..6084, sequential by `WinAvx2X8.avx2x8_sites`/`frame_layout`)
  executes the 32-byte vector store at `pc` 442, `vmovdqa [rsp+0x100], ymm8`, whose value is
  the input block loaded at `pc` 35, `vmovdqu ymm8, [rdx]` with `rdx` = the Go `input`
  argument;
* with the shipped frame the body `rsp` is `B = ((E + 1016) & -32) - 1280`, where `E` is the
  wrapper's ABI0 entry `rsp`; since `E % 16 = 8`, either `B = E - 264` or `B = E - 280`;
* hence the store interval `[B + 256, B + 288)` contains `[E - 8, E + 8)`: the Go caller's
  saved `rbp` word and return address --- exactly the two words the wrapper's epilogue
  `POPQ BP ; RET` reads (`post F` reads `[rbx + F]` and `[rbx + F + 8]`, i.e. `E - 8` and `E`).

The same geometry applies to the `avx512_x16 -> avx2_x8` tail link: the tail `JMP` does not
push a return address, so `avx2_x8` enters the tail with `rsp` still the aligned call `rsp`
(`σ 10`), and its body is `σ 10 - 1272` --- the same `B` as a direct call.

Everything here is `decide +kernel` on the shipped array plus `omega`; no `native_decide`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinAvx2X8
open Hashtree.Kernels.X86Win.WrapperWindows (shippedFrame)

namespace Hashtree.Proofs.WinShippedClobber

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Avx2X8.prog

/-! ## The instruction stream -/

/-- `vmovdqu ymm8, [rdx]`: the input block, loaded into the register the loop stores. -/
theorem avx2x8_input_load_pc :
    winProg[35]? = some (.vload true 8 8 (.mem { base := some 2, disp := 0 })) := by
  decide +kernel

/-- `vmovdqa [rsp+0x100], ymm8`: the 32-byte store at `pc` 442 that reaches into the caller's
stack under the shipped frame. -/
theorem avx2x8_store_pc :
    winProg[442]? = some (.vstore 8 { base := some 4, disp := 256 } 8) := by
  decide +kernel

/-- The loop guard: `CMPQ R8, $8 ; JB 6086` at `pc` 23--24, so a call with count at least 8
falls through into the body (this repeats `WinAvx2X8.frame_layout` in the form used here). -/
theorem avx2x8_loop_guard :
    winProg[23]? = some (.cmp 64 8 (.imm 8)) ∧ winProg[24]? = some (.jcc .b 6086) := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- Every instruction of the loop body `pc` 25..6084 is sequential (`ctlSite = none`): the only
control site in the loop is the loop-back `JMP 23` at `pc` 6085.  Hence a loop iteration
executes `pc` 442 before any branch. -/
theorem avx2x8_body_sequential_scan :
    ((winProg.toList.drop 25).take 6060).all (fun i => ctlSite i == none) = true := by
  decide +kernel

theorem avx2x8_body_sequential (pc : Nat) (h1 : 25 ≤ pc) (h2 : pc < 6085) :
    ∃ i, winProg[pc]? = some i ∧ ctlSite i = none := by
  have hlen : pc - 25 < ((winProg.toList.drop 25).take 6060).length := by
    rw [List.length_take, List.length_drop]
    have : winProg.toList.length = 6107 := by decide +kernel
    omega
  have hget : ((winProg.toList.drop 25).take 6060)[pc - 25]? = winProg.toList[pc]? := by
    rw [List.getElem?_take_of_lt (by omega), Hashtree.Proofs.WinScan.getElem?_drop]
    congr 1
    omega
  have hmem : ((winProg.toList.drop 25).take 6060)[pc - 25] ∈
      (winProg.toList.drop 25).take 6060 :=
    List.getElem_mem hlen
  have hall := List.all_eq_true.mp avx2x8_body_sequential_scan _ hmem
  rw [beq_iff_eq] at hall
  exact ⟨_, by rw [← Array.getElem?_toList, ← hget, List.getElem?_eq_getElem hlen], hall⟩

/-! ## The shipped frame's geometry

`E` is the wrapper's ABI0 entry `rsp` (`σ 9`).  The prologue does
`SUBQ $1024, SP ; ... ; ADDQ $2048, SP ; ANDQ $-32, SP`, so the aligned call `rsp` is
`shippedCallRsp E = (E + 1016) & -32`.  The `avx2_x8` prologue (`PUSH RBP ; PUSH RSI ;
MOV RBP, SP ; ANDQ $-32, SP ; SUBQ $1248, SP`) is applied to the call entry `rsp` (the call
pushes its return address 8 bytes below `shippedCallRsp E`), so the body `rsp` is
`shippedBodyRsp E = shippedCallRsp E - 1280`. -/

/-- The aligned call `rsp` of the shipped `$1024` frame. -/
def shippedCallRsp (E : Int) : Int := (E + 1016) - (E + 1016) % 32

/-- The `avx2_x8` body `rsp` (after its two pushes, alignment and `SUBQ $1248`) for a call from
the shipped wrapper at ABI0 entry `rsp = E`. -/
def shippedBodyRsp (E : Int) : Int := shippedCallRsp E - 1280

/-- The two cases the 16-byte ABI0 residue leaves for the alignment. -/
theorem shippedCallRsp_cases (E : Int) (hE : E % 16 = 8) :
    (E % 32 = 8 → shippedCallRsp E = E + 1016) ∧
      (E % 32 = 24 → shippedCallRsp E = E + 1000) := by
  constructor <;> intro h <;> simp only [shippedCallRsp] <;> omega

/-- The body `rsp` in the two cases. -/
theorem shippedBodyRsp_cases (E : Int) (hE : E % 16 = 8) :
    (E % 32 = 8 → shippedBodyRsp E = E - 264) ∧
      (E % 32 = 24 → shippedBodyRsp E = E - 280) := by
  constructor <;> intro h <;> simp only [shippedBodyRsp, shippedCallRsp] <;> omega

/-- The 32-byte store `[B + 256, B + 288)` contains the Go saved-`rbp` word `[E - 8, E)` and the
return address `[E, E + 8)`. -/
theorem shippedBodyRsp_store_covers_go_frame (E : Int) (hE : E % 16 = 8) :
    shippedBodyRsp E + 256 ≤ E - 8 ∧ E + 8 ≤ shippedBodyRsp E + 288 := by
  simp only [shippedBodyRsp, shippedCallRsp]
  omega

/-! ## The corruption witness -/

/-- **The shipped `$1024` frame is concretely corrupt for `avx2_x8`.**  For every ABI0 entry
`rsp = E`, the loop body (sequential from the guard at `pc` 24 to the loop-back at `pc` 6085)
executes the input-derived 32-byte store at `pc` 442, and under the shipped frame that store's
address interval `[B + 256, B + 288)` covers both the Go caller's saved `rbp` word and its
return address --- the two words `post F` (`POPQ BP ; RET`) reads. -/
theorem shipped_avx2x8_store_clobbers_go_frame (E : Int) (hE : E % 16 = 8) :
    winProg[23]? = some (.cmp 64 8 (.imm 8)) ∧
      winProg[24]? = some (.jcc .b 6086) ∧
      winProg[35]? = some (.vload true 8 8 (.mem { base := some 2, disp := 0 })) ∧
      winProg[442]? = some (.vstore 8 { base := some 4, disp := 256 } 8) ∧
      (∀ pc, 25 ≤ pc → pc < 6085 → ∃ i, winProg[pc]? = some i ∧ ctlSite i = none) ∧
      (E % 32 = 8 → shippedBodyRsp E = E - 264) ∧
      (E % 32 = 24 → shippedBodyRsp E = E - 280) ∧
      (shippedBodyRsp E + 256 ≤ E - 8 ∧ E + 8 ≤ shippedBodyRsp E + 288) := by
  refine ⟨avx2x8_loop_guard.1, avx2x8_loop_guard.2, avx2x8_input_load_pc, avx2x8_store_pc,
    avx2x8_body_sequential, (shippedBodyRsp_cases E hE).1, (shippedBodyRsp_cases E hE).2, ?_⟩
  exact shippedBodyRsp_store_covers_go_frame E hE

/-- The same witness in the wrapper's own `σ` vocabulary (`Proofs/WinWrapper`): if the aligned
call `rsp` is `σ 10 + 8` and the entry `rsp` is `σ 9`, the store covers `[σ 9 - 8, σ 9 + 8)`
and the body `rsp` is `σ 10 - 1272`. -/
theorem shipped_avx2x8_store_clobbers_go_frame_sigma (σ : Nat → Int)
    (hσ : σ 10 + 8 = shippedCallRsp (σ 9)) (hE : σ 9 % 16 = 8) :
    winProg[442]? = some (.vstore 8 { base := some 4, disp := 256 } 8) ∧
      shippedBodyRsp (σ 9) = σ 10 - 1272 ∧
      (σ 10 - 1272 + 256 ≤ σ 9 - 8 ∧ σ 9 + 8 ≤ σ 10 - 1272 + 288) := by
  refine ⟨avx2x8_store_pc, ?_, ?_⟩
  · simp only [shippedBodyRsp]
    omega
  · have h := shippedBodyRsp_store_covers_go_frame (σ 9) hE
    simp only [shippedBodyRsp] at h ⊢
    omega

end Hashtree.Proofs.WinShippedClobber
