import Hashtree.Asm.RspMap

/-!
# R5: the region-typing certificate (the lift's region side condition)

The frame-slot lift (`Proofs/FrameLift`) asks that every memory operand whose base is not rsp
evaluates outside the `rStack` region (`RegionOk`).  The base registers of the push-saving
windows bodies (rbp/rsi after the prologue, rcx, rdx) are rewritten inside the bodies, so the
region of a base register is a per-pc fact: this module computes and verifies it.

A table `RTags` (one `Option Region` per general register) per pc records the *known* region of
a register (`none` = unknown).  The meaning (`RegRel`): a register with known region `ρ` holds a pointer of
region `ρ`, or data when `ρ = rNum` (data is a number: as an address it fails, as a control
operand it is a count of region `rNum`).  The transfer follows `exec` for the forms the bodies
define their pointer registers with: `mov d, s` copies, `mov d, imm` gives `rNum`, `lea` takes
the operand's base region (rip-relative = the rodata region 4, no base = `rNum`), 64-bit `add`
takes the non-`rNum` side, 64-bit `and`/`sub` keep the destination's region, `xor d, d` gives
`rNum`, `push`/`pop`/`ret` keep rsp's; every other write (loads, `pop r`, 32-bit results) is
unknown.  `regCheck` verifies, per pc, that every non-rsp, non-rip
memory base has a known region other than `rStack`, and that successors' tables are contained
in the stepped table (a must-analysis, computed like the others as a fixpoint).
-/

set_option autoImplicit false

namespace Hashtree.Asm.RegionTags

open Hashtree.Asm.X86 Hashtree.Asm.BodyReads Hashtree.Asm.RspMap

/-- The known region of each of the 16 general registers (`none` = unknown). -/
abbrev RTags := List (Option Region)

def regOf (R : RTags) (r : Nat) : Option Region := R.getD r none
def setReg (R : RTags) (r : Nat) (v : Option Region) : RTags := R.set r v
def clearReg (R : RTags) (r : Nat) : RTags := R.set r none

/-- The region of a general source as a control operand. -/
def gsrcReg (R : RTags) : GSrc → Option Region
  | .reg s => regOf R s
  | .imm _ => some rNum
  | .mem _ => none

/-- The region of an effective address (`lea`). -/
def memReg (R : RTags) (m : MemRef) : Option Region :=
  match m.ro, m.base with
  | some _, _ => some 4
  | none, none => some rNum
  | none, some b => regOf R b

/-- The table after one instruction: the few forms the bodies define their pointer registers with
are tracked precisely (`mov d, reg` / `mov d, imm`, `lea`, 64-bit `add`/`and`/`sub`, the zeroing
idiom), `push`/`pop`/`ret` keep rsp's region, every other written register becomes unknown. -/
def clearAll (i : Instr) (R : RTags) : RTags := (dsts i).foldl (fun acc r => clearReg acc r) R

def regStep (i : Instr) (R : RTags) : RTags :=
  match i with
  | .mov w d src =>
    if w = 64 then
      (match src with
        | .reg s => setReg R d (regOf R s)
        | .imm _ => setReg R d (some rNum)
        | .mem _ => setReg R d none)
    else clearAll i R
  | .alu op w d src =>
    if w = 64 then
      if op = .xor ∧ src = .reg d then setReg R d (some rNum)
      else if op = .add then
        (match regOf R d, gsrcReg R src with
          | some a, some b => setReg R d (some (if b = rNum then a else b))
          | _, _ => setReg R d none)
      else if op = .and then R
      else setReg R d none
    else clearAll i R
  | .sub w _ _ => if w = 64 then R else clearAll i R
  | .lea d m => setReg R d (memReg R m)
  | .push _ => R
  | .pop r => setReg R r none
  | .ret => R
  | _ => clearAll i R

/-- The memory bases of an instruction other than rsp and rip-relative operands. -/
def baseRegs (i : Instr) : List Nat :=
  (memOps i).filterMap fun (m, _) => match m.ro, m.base with
    | none, some b => if b = 4 then none else some b
    | _, _ => none

/-- Every non-rsp base has a known region other than `rStack`. -/
def basesOk (R : RTags) (i : Instr) : Bool :=
  (baseRegs i).all fun b => match regOf R b with | some ρ => ρ != rStack | none => false

/-- `R ⊆ R'` as maps (every known region of `R` is that of `R'`). -/
def subRegs (R R' : RTags) : Bool := (List.range 16).all fun r => regOf R r = none || regOf R r = regOf R' r

abbrev RSegs := List (Nat × Option RTags)

def atR (RT : RSegs) (p : Nat) : Option RTags :=
  RT.foldl (fun acc s => if s.1 ≤ p then s.2 else acc) none

/-- The check at one pc (unvisited pcs are not checked). -/
def regAt (n : Nat) (RT : RSegs) (p : Nat) (i : Instr) : Bool :=
  match atR RT p with
  | none => true
  | some R =>
    R.length == 16 && basesOk R i &&
    (nexts p i).all fun q => q < n && (match atR RT q with | some Rq => subRegs Rq (regStep i R) | none => false)

def regAux (n : Nat) (RT : RSegs) : Nat → List Instr → Bool
  | _, [] => true
  | p, i :: rest => regAt n RT p i && regAux n RT (p + 1) rest

/-- **The region certificate check**: the entry table, and `regAt` at every pc. -/
def regCert (n : Nat) (prog : Array Instr) (RT : RSegs) (R0 : RTags) : Bool :=
  atR RT 0 = some R0 && regAux n RT 0 prog.toList

/-! ## Computing the table -/

def meet (R R' : RTags) : RTags := (List.range 16).map fun r => if regOf R r = regOf R' r then regOf R r else none

def regPass (prog : Array Instr) (A : Array (Option RTags)) : Array (Option RTags) := Id.run do
  let mut A := A
  for p in [0:prog.size] do
    match A[p]!, prog[p]? with
    | some R, some i =>
      let R' := regStep i R
      for q in nexts p i do
        if q < prog.size then
          A := A.set! q (match A[q]! with | some Rq => some (meet Rq R') | none => some R')
    | _, _ => pure ()
  return A

def regs (prog : Array Instr) (R0 : RTags) (passes : Nat := 16) : RSegs := Id.run do
  let mut A : Array (Option RTags) := Array.replicate prog.size none
  A := A.set! 0 (some R0)
  for _ in [0:passes] do A := regPass prog A
  let mut out : RSegs := []
  let mut last : Option (Option RTags) := none
  for p in [0:A.size] do
    if last ≠ some A[p]! then
      out := out ++ [(p, A[p]!)]
      last := some A[p]!
  return out

/-- Where `basesOk` fails (for `#eval`). -/
def failures (prog : Array Instr) (RT : RSegs) : List Nat :=
  (List.range prog.size).filter fun p =>
    match atR RT p, prog[p]? with
    | some R, some i => !basesOk R i
    | _, _ => false

/-- The entry table of the windows call state: rcx = rOut, rdx = rIn, r8 = count, rsp/rbx/rbp
stack pointers, r12/r13/r15 numbers, r14 = region 6 (`X86SymW.rG`), the rest data. -/
def entryWinRegs : RTags :=
  [some rNum, some rOut, some rIn, some rStack, some rStack, some rStack, some rNum, some rNum,
   some rNum, some rNum, some rNum, some rNum, some rNum, some rNum, some 6, some rNum]

end Hashtree.Asm.RegionTags
