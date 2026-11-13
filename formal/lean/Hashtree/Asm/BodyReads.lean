import Hashtree.Asm.X86

/-!
# Body read sets for windows/linux kernel bodies

Shared, kernel-independent scan used to decide when a run can depend on the entry value of a
general register.  `rbw is` is the list of general registers read before their first write in the
instruction list `is`: a static over-approximation (sound for branchy streams), where an
ALU/sub/ror/shld destination is counted as read (read-modify-write) and a memory operand base is
counted as a read.  Vector register numbers are not general registers, so `VSrc.reg` contributes
nothing here.
-/

namespace Hashtree.Asm.BodyReads

open Hashtree.Asm Hashtree.Asm.X86

def baseOf (m : MemRef) : List Nat := match m.base with | some b => [b] | none => []

def gsrc : GSrc → List Nat | .reg s => [s] | .imm _ => [] | .mem m => baseOf m
def vsrc : VSrc → List Nat | .reg _ => [] | .mem m => baseOf m

/-- General registers read by one instruction. -/
def srcs : Instr → List Nat
  | .vop _ _ _ _ _ s => vsrc s
  | .vload _ _ _ s => vsrc s
  | .mov _ _ s => gsrc s
  | .alu _ _ d s => d :: gsrc s
  | .sub _ d s => d :: gsrc s
  | .cmp _ a s => a :: gsrc s
  | .ror _ d _ => [d]
  | .shld _ d s _ => [d, s]
  | .lea _ m => baseOf m
  | .movst _ m s => s :: baseOf m
  | .vstore _ m _ => baseOf m
  | .inserti128 _ _ m _ => baseOf m
  | .inserti64x4 _ _ m _ => baseOf m
  | _ => []

/-- General registers written by one instruction. -/
def dsts : Instr → List Nat
  | .mov _ d _ => [d]
  | .alu _ _ d _ => [d]
  | .sub _ d _ => [d]
  | .lea d _ => [d]
  | .ror _ d _ => [d]
  | .shld _ d _ _ => [d]
  | _ => []

def rbwAux : List Nat → List Instr → List Nat
  | _, [] => []
  | w, i :: is => (srcs i).filter (fun r => !(w.contains r)) ++ rbwAux (w ++ dsts i) is

/-- General registers read before their first write in `is`. -/
def rbw (is : List Instr) : List Nat := (rbwAux [] is).eraseDups

/-- The read set as a membership predicate (the shape the run-invariance engine consumes). -/
def ReadsBefore (is : List Instr) (r : Nat) : Prop := r ∈ rbw is

end Hashtree.Asm.BodyReads
