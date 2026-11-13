import Hashtree.Asm.Riscv

/-!
# Our linux/riscv64 wrapper `HashtreeHash` (`wrapper_linux_riscv64.s`, assembled by go1.26)

Source (`hashtree-bindings/wrapper_linux_riscv64.s`, `//go:build cgo && linux && riscv64`):

    TEXT ·HashtreeHash(SB), 0, $0-24
        MOV output+0(FP), A0
        MOV input+8(FP), A1
        MOV count+16(FP), A2
        CALL hashtree_hash(SB)
        RET

`$0-24` is a Go ABI0 frame: no local frame words, 24 argument bytes.  At the ABI0 entry `sp = SPe`
points at the return address and the three words are at `SPe + 8` (output), `+ 16` (input),
`+ 24` (count); `SPe` is 8 mod 16, so the callee entry `SPe - 8` is 0 mod 16 (RISC-V psABI).
go1.26 emits (`go tool objdump -s 'main.HashtreeHash'` of the linked binary; the stack-check
preamble at `0x6c700`, `MOV 16(X27),X6; BLTU X6,X2,3(PC); JAL X5,runtime.morestack_noctxt.abi0`,
is abstracted):

    0  sd ra,-8(sp)                -- 0x6c710  spill the caller's ra below sp
    1  addi sp,sp,-8               -- 0x6c714  allocate the 8-byte frame
    2  sd ra,0(sp)                 -- 0x6c716  ra slot = SPe - 8
    3  ld a0,16(sp)                -- 0x6c718  output = (SPe - 8) + 16 = SPe + 8
    4  ld a1,24(sp)                -- 0x6c71a  input  = SPe + 16
    5  ld a2,32(sp)                -- 0x6c71c  count  = SPe + 24
    6  auipc ra, %pcrel_hi(hashtree_hash)  -- 0x6c71e  CALL hashtree_hash
    7  jalr ra,ra,0                --        link ra = instruction 8
    8  ld ra,0(sp)                 -- 0x6c722  ra slot = SPe - 8
    9  addi sp,sp,8                -- 0x6c724  release the frame
    10 jalr zero,0(ra)             -- 0x6c726  RET

The `CALL` is `auipc`+`jalr` (the `auipc` overwrites `ra`; the caller's `ra` is in the frame) and
the `RET` is `jalr zero,0(ra)`.  A return to `⟨rRet, _⟩` halts (the harness's return target).

Not modelled: the stack-check preamble (`morestack` is out of scope; the 16-byte check is assumed
to pass), the linker's `%pcrel_hi` relaxation, and the call and return themselves.  The prefix
stops at `tail = some "call:hashtree_hash"` with `pc` = the return point; `epilogue` starts from a
state in which the callee has returned to that point with `sp` (and the caller's saved `ra` slot)
intact.
-/

namespace Hashtree.Kernels.Riscv.WrapperLinux
open Hashtree.Asm Hashtree.Asm.Riscv

/-- Regions of the wrapper's own object (its rodata/GOT/code) and of its `hashtree_hash` symbol. -/
def rWro : Region := 31
def rWgot : Region := 32
def rWcode : Region := 33
def rSymHH : Region := 30

/-- The wrapper's static environment: its code region, and `hashtree_hash` as a named symbol. -/
def wenv : Env := ⟨rWro, rWgot, rWcode, [("hashtree_hash", rSymHH)]⟩

/-- The compiled stream, instructions 0-10 above (the abstracted preamble not included). -/
def prog : Array Instr := #[
  .sd 1 2 (-8),
  .addi 2 2 (-8),
  .sd 1 2 0,
  .ld 10 2 16,
  .ld 11 2 24,
  .ld 12 2 32,
  .auipc 1 (.sym "hashtree_hash" 0),
  .jalr 1 1 0,
  .ld 1 2 0,
  .addi 2 2 8,
  .jalr 0 1 0]

/-- The ABI0 entry state: `ra` = the return target, `sp = sp0`, and the three argument words
(pre-loaded by the caller into `a0`/`a1`/`a2`; on the machine they are read from the frame). -/
def entryW (sp0 : Int) (aOut aIn : Addr Int) (k : Int) : State W32 Int :=
  { gpr := (List.range 32).map fun i =>
      if i = 1 then .ptr ⟨rRet, 0⟩
      else if i = 2 then .ptr ⟨rStack, sp0⟩
      else if i = 10 then .ptr aOut
      else if i = 11 then .ptr aIn
      else if i = 12 then .ptr ⟨rNum, k⟩
      else .num 0 0,
    vr := [], flags := none, mem := [], pc := 0, halted := false, tail := none, err := none,
    assume := [] }

/-- The ABI0 frame memory: the three words at `sp0 + 8`, `+ 16`, `+ 24`, as pointer bytes (the
model's encoding of pointers and of a 64-bit count), and zero data elsewhere. -/
def ABI0frame (sp0 : Int) (aOut aIn : Addr Int) (k : Int) : Addr Int → Cell W32 Int := fun a =>
  if a.region = rStack ∧ sp0 + 8 ≤ a.off ∧ a.off < sp0 + 32 then
    if a.off < sp0 + 16 then .pb aOut (a.off - (sp0 + 8)).toNat
    else if a.off < sp0 + 24 then .pb aIn (a.off - (sp0 + 16)).toNat
    else .pb ⟨rNum, k⟩ (a.off - (sp0 + 24)).toNat
  else .dat 0 0

/-- A concrete ABI-aligned entry (`SPe = 8`): output at `⟨rOut, 8⟩`, input at `⟨rIn, 0⟩`, count 3. -/
def cOut : Addr Int := ⟨rOut, 8⟩
def cIn : Addr Int := ⟨rIn, 0⟩
def cCount : Int := 3
def entryC : State W32 Int := entryW 8 cOut cIn cCount
def memC : Addr Int → Cell W32 Int := ABI0frame 8 cOut cIn cCount

end Hashtree.Kernels.Riscv.WrapperLinux
