import Hashtree.Asm.X86

/-!
# R5: the windows/amd64 Go wrapper `HashtreeHash` (wrapper_windows_amd64.s)

The Go assembler expands `TEXT ·HashtreeHash(SB), 0, $F-24` into the prologue
`PUSHQ BP ; MOVQ SP, BP ; SUBQ $F, SP` and the epilogue `ADDQ $F, SP ; POPQ BP ; RET`
(go1.26; checked with `go tool asm -S`).  The body between them is

```
MOVQ output+0(FP), CX ; MOVQ input+8(FP), DX
MOVQ R8, R12 ; MOVQ count+16(FP), R8      // saves the incoming R8 in R12
MOVQ SP, BX ; ADDQ $2048, SP ; ANDQ $-32, SP
CMPB hasShani,1 ; JE shani ; CMPB hasAVX512,1 ; JE avx512 ; CMPB hasAVX2,1 ; JE avx2
CALL avx_x1 ; JMP epilog ; shani: CALL shani_x2 ; ... ; avx2: CALL avx2_x8
epilog: MOVQ BX, SP ; MOVQ R12, R8 ; <assembler epilogue>
```

`pre F` below is the prologue plus the two argument loads and the frame save
(9 instructions, the `ADDQ $2048` included); `alignI` is the `ANDQ $-32, SP`; `post F`
is `MOVQ BX, SP ; MOVQ R12, R8` followed by the assembler epilogue of frame `F`.
The kernel `CALL` is the chain call of `Proofs.WinChain` / `Proofs.X86Chain`.

The shipped source declares `$1024` (`shippedFrame`); the open fix branch
`fix/windows-wrapper-frame` declares `$2048` (`fixedFrame`).  `ADDQ $2048, SP` is part
of the text and is *not* adjusted with the declared frame, so the shipped frame places
the kernel's stack 1024 bytes above the wrapper's entry `rsp`; `WinWrapper` proves both
placements.

ABI conventions: ABI0 entry with `rsp = SPe`, the return address at `[SPe]` and the
three argument slots at `SPe+8`, `+16`, `+24` (output, input, count); the kernels are
called with `rcx`/`rdx`/`r8` = output/input/count, the Win64 argument registers.
-/

namespace Hashtree.Kernels.X86Win.WrapperWindows
open Hashtree.Asm Hashtree.Asm.X86

/-- The wrapper's prefix for declared frame `F`: the assembler prologue, the three
argument loads, and `MOVQ SP, BX ; ADDQ $2048, SP`. -/
def pre (F : Int) : Array Instr := #[
  .push 5,
  .mov 64 5 (.reg 4),
  .sub 64 4 (.imm F),
  .mov 64 1 (.mem { base := some 4, disp := F + 16 }),
  .mov 64 2 (.mem { base := some 4, disp := F + 24 }),
  .mov 64 12 (.reg 8),
  .mov 64 8 (.mem { base := some 4, disp := F + 32 }),
  .mov 64 3 (.reg 4),
  .alu .add 64 4 (.imm 0x800)]

/-- `ANDQ $-32, SP`. -/
def alignI : Instr := .alu .and 64 4 (.imm (-0x20))

/-- The wrapper's epilogue for declared frame `F`: `MOVQ BX, SP ; MOVQ R12, R8` and the
assembler epilogue `ADDQ $F, SP ; POPQ BP ; RET`. -/
def post (F : Int) : Array Instr := #[
  .mov 64 4 (.reg 3),
  .mov 64 8 (.reg 12),
  .alu .add 64 4 (.imm F),
  .pop 5,
  .ret]

/-- The kernels the wrapper can call. -/
inductive Kern | shani | avx512 | avx2 | avx1
  deriving DecidableEq, Repr

/-- `CMPB hasShani, 1; JE shani; CMPB hasAVX512, 1; JE avx512; CMPB hasAVX2, 1; JE avx2;
CALL avx_x1`. -/
def pick (hasShani hasAVX512 hasAVX2 : Bool) : Kern :=
  if hasShani then .shani else if hasAVX512 then .avx512 else if hasAVX2 then .avx2 else .avx1

/-- The frame size the shipped source declares. -/
def shippedFrame : Int := 0x400

/-- The frame size of the open fix branch `fix/windows-wrapper-frame`. -/
def fixedFrame : Int := 0x800

end Hashtree.Kernels.X86Win.WrapperWindows
