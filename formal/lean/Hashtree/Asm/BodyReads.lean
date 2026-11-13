import Hashtree.Asm.X86

/-!
# Body read sets for windows/linux kernel bodies

Shared, kernel-independent scan used to decide when a run can depend on the entry value of a
general register.  `srcs i` / `dsts i` are the general registers an instruction reads / writes
(complete over the `Instr` type: `Asm/RunAgree` proves that `exec i` reads only `srcs i` and
writes only `dsts i`).  An ALU/sub/ror/shld/shl/bswap destination is counted as read
(read-modify-write), a memory operand's base and index registers are reads, `push`/`pop`/`ret`
read `rsp`, and `pop` writes its register and `rsp`.  Vector register numbers are not general
registers, so `VSrc.reg` contributes nothing here.

`rbw is` is the list of general registers read before their first write along the instruction
list `is` taken in order: the read set of a straight-line stream.  For a stream with jumps
(a loop) the per-pc read sets are the liveness certificate of `Asm/RunAgree` (`Cert`), which is
what the run-invariance engine consumes; `rbw` of a body is the linear over-approximation of its
entry live set, and the two are compared by `decide` per kernel.
-/

namespace Hashtree.Asm.BodyReads

open Hashtree.Asm Hashtree.Asm.X86

def baseOf (m : MemRef) : List Nat := match m.base with | some b => [b] | none => []
def indexOf (m : MemRef) : List Nat := match m.index with | some i => [i] | none => []

/-- General registers an effective-address computation may read. -/
def memRegs (m : MemRef) : List Nat := baseOf m ++ indexOf m

def gsrc : GSrc → List Nat | .reg s => [s] | .imm _ => [] | .mem m => memRegs m
def vsrc : VSrc → List Nat | .reg _ => [] | .mem m => memRegs m

/-- General registers read by one instruction. -/
def srcs : Instr → List Nat
  | .vop _ _ _ _ _ s => vsrc s
  | .vload _ _ _ s => vsrc s
  | .mov _ _ s => gsrc s
  | .alu _ _ d s => d :: gsrc s
  | .sub _ d s => d :: gsrc s
  | .cmp _ a s => a :: gsrc s
  | .test _ a b => [a, b]
  | .ror _ d _ => [d]
  | .shld _ d s _ => [d, s]
  | .shl _ d _ => [d]
  | .bswap _ d => [d]
  | .lea _ m => memRegs m
  | .movst _ m s => s :: memRegs m
  | .vstore _ m _ => memRegs m
  | .inserti128 _ _ m _ => memRegs m
  | .inserti64x4 _ _ m _ => memRegs m
  | .push r => [rsp, r]
  | .pop _ => [rsp]
  | .ret => [rsp]
  | _ => []

/-- General registers written by one instruction. -/
def dsts : Instr → List Nat
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
  | .ret => [rsp]
  | _ => []

/-- Reads the flags (`jcc`/`jccTail`). -/
def readsF : Instr → Bool
  | .jcc _ _ => true
  | .jccTail _ _ => true
  | _ => false

/-- Tail calls (`jmpTail`/`jccTail`): the certificate seeds their pc with the next link's entry set. -/
def tails : Instr → Bool
  | .jmpTail _ => true
  | .jccTail _ _ => true
  | _ => false

/-- Writes the flags: the comparisons and the flag-clobbering data operations (every branch of
their `exec` ends in `setFlags`/`clearFlags`). -/
def writesF : Instr → Bool
  | .alu _ _ _ _ => true
  | .sub _ _ _ => true
  | .cmp _ _ _ => true
  | .test _ _ _ => true
  | .ror _ _ _ => true
  | .shld _ _ _ _ => true
  | .shl _ _ _ => true
  | _ => false

def rbwAux : List Nat → List Instr → List Nat
  | _, [] => []
  | w, i :: is => (srcs i).filter (fun r => !(w.contains r)) ++ rbwAux (w ++ dsts i) is

/-- General registers read before their first write in `is`. -/
def rbw (is : List Instr) : List Nat := (rbwAux [] is).eraseDups

/-- The read set as a membership predicate. -/
def ReadsBefore (is : List Instr) (r : Nat) : Prop := r ∈ rbw is

end Hashtree.Asm.BodyReads
