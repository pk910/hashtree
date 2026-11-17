import Hashtree.Asm.X86
import Hashtree.Asm.BodyReads

/-!
# R5: the static rsp map of an x86 stream (frame-slot certificate, step 1)

For every pc of a stream, `rsp = base + δ(pc)`, where the base is the entry rsp (`0`) or the
aligned base after `and rsp, -32` (`1`, avx2_x8 only; a fresh base, `δ = 0`), and `rbp` may hold a
saved rsp value (`mov rbp, rsp` / `mov rsp, rbp`).  The map is given as a list of segments
`(start pc, value)` (a pc takes the value of the last segment starting at or before it) and
*verified* per pc by the decidable `ok`: the entry is `(0, 0)`, every instruction's effect on rsp
is one of the supported forms (`push`, `pop`, `sub/add rsp, imm`, `and rsp, -32`, `mov rbp, rsp`,
`mov rsp, rbp`; no other write of rsp), every successor carries the stepped value, and every
exit (`ret`, tail jumps) is at the entry rsp.  `compute` produces the segments (used in `#eval`
only; the proof is `ok`).

Memory operands `[rsp + k]` at pc are the frame slots `(base, δ(pc) + k, size)` (`slots`), which
the frame-slot liveness certificate (step 2/3 of the design) keys its items by.
-/

set_option autoImplicit false

namespace Hashtree.Asm.RspMap

open Hashtree.Asm.X86 Hashtree.Asm.BodyReads

/-- An rsp value: `(base, δ)`. -/
abbrev RV := Nat × Int

/-- The per-pc fact: rsp and the saved rsp in rbp (if any). -/
structure Fact where
  sp : RV
  saved : Option RV := none
  deriving DecidableEq, Repr, Inhabited

/-- An instruction that is none of the rsp forms: it must not write rsp; a write of rbp drops
the saved value. -/
def stepOther (i : Instr) (f : Fact) : Option Fact :=
  if 4 ∈ dsts i then none else if 5 ∈ dsts i then some { f with saved := none } else some f

/-- The effect of one instruction on the fact; `none` = an unsupported rsp (or rbp-save) write. -/
def step (i : Instr) (f : Fact) : Option Fact :=
  match i with
  | .push _ => some { f with sp := (f.sp.1, f.sp.2 - 8) }
  | .pop r => if r = 4 then none else some { sp := (f.sp.1, f.sp.2 + 8), saved := if r = 5 then none else f.saved }
  | .ret => some { f with sp := (f.sp.1, f.sp.2 + 8) }
  | .sub w d src =>
    if w = 64 ∧ d = 4 then (match src with | .imm k => some { f with sp := (f.sp.1, f.sp.2 - k) } | _ => none)
    else stepOther i f
  | .alu op w d src =>
    if w = 64 ∧ d = 4 then
      (match op, src with
        | .add, .imm k => some { f with sp := (f.sp.1, f.sp.2 + k) }
        | .and, .imm k => if k = -32 then some { f with sp := (f.sp.1 + 1, 0) } else none
        | _, _ => none)
    else stepOther i f
  | .mov w d src =>
    if w = 64 ∧ d = 5 ∧ src = .reg 4 then some { f with saved := some f.sp }
    else if w = 64 ∧ d = 4 ∧ src = .reg 5 then (match f.saved with | some v => some { f with sp := v } | none => none)
    else stepOther i f
  | _ => stepOther i f

/-- Control successors (as `RunAgree.succs`). -/
def nexts (p : Nat) : Instr → List Nat
  | .jcc _ t => [p + 1, t]
  | .jmp t => [t]
  | .jccTail _ _ => [p + 1]
  | .jmpTail _ => []
  | .ret => []
  | _ => [p + 1]

/-- Exits leave at the entry rsp (`ret` pops the return address from it). -/
def exitOk : Instr → Fact → Bool
  | .ret, f => f.sp = (0, 0)
  | .jmpTail _, f => f.sp = (0, 0)
  | .jccTail _ _, f => f.sp = (0, 0)
  | _, _ => true

/-- The segment table: the value at `p` is that of the last segment starting at or before `p`. -/
def at? (segs : List (Nat × Option Fact)) (p : Nat) : Option Fact :=
  (segs.foldl (fun acc s => if s.1 ≤ p then s.2 else acc) none)

/-- The check at one pc: the instruction steps, exits are at the entry rsp, and every control
successor (below `n`, the stream length) carries the stepped value. -/
def okAt (n : Nat) (segs : List (Nat × Option Fact)) (p : Nat) (i : Instr) : Bool :=
  match at? segs p with
  | none => true
  | some f =>
    (f.sp.1 == 0 || f.sp.1 == 1) &&
    match step i f with
    | none => false
    | some f' => exitOk i f && (nexts p i).all fun q => q < n && at? segs q = some f'

/-- A linear sweep over the instruction list from pc `p` (the stream is walked once; indexing
the array per pc would be quadratic in the kernel). -/
def okAux (n : Nat) (segs : List (Nat × Option Fact)) : Nat → List Instr → Bool
  | _, [] => true
  | p, i :: rest => okAt n segs p i && okAux n segs (p + 1) rest

/-- The per-pc verification of a segment table against the stream (`n = prog.size`, passed
explicitly so it is evaluated once). -/
def ok (n : Nat) (prog : Array Instr) (segs : List (Nat × Option Fact)) : Bool :=
  at? segs 0 = some { sp := (0, 0) } && okAux n segs 0 prog.toList

/-! ## Computing the segments (for `#eval`) -/

/-- Forward propagation: `passes` in-order sweeps over the stream. -/
def computeT (prog : Array Instr) (passes : Nat := 8) : Array (Option Fact) := Id.run do
  let mut T : Array (Option Fact) := Array.replicate prog.size none
  T := T.set! 0 (some { sp := (0, 0) })
  for _ in [0:passes] do
    for p in [0:prog.size] do
      match T[p]!, prog[p]? with
      | some f, some i =>
        match step i f with
        | some f' => for q in nexts p i do if q < prog.size then T := T.set! q (some f')
        | none => pure ()
      | _, _ => pure ()
  return T

/-- The segments of a table (runs of equal values). -/
def segsOf (T : Array (Option Fact)) : List (Nat × Option Fact) := Id.run do
  let mut out : List (Nat × Option Fact) := []
  let mut last : Option (Option Fact) := none
  for p in [0:T.size] do
    if last ≠ some T[p]! then
      out := out ++ [(p, T[p]!)]
      last := some T[p]!
  return out

def compute (prog : Array Instr) : List (Nat × Option Fact) := segsOf (computeT prog)

/-! ## Frame slots -/

/-- Memory operands of an instruction with their byte sizes (lanes are 4 bytes; a 64-bit `mov`/`movst`
moves 8 bytes, every other general operand is read as a 32-bit lane or not at all). -/
def memOps : Instr → List (MemRef × Nat)
  | .vop _ _ w _ _ (.mem m) => [(m, 4 * w)]
  | .vload _ w _ (.mem m) => [(m, 4 * w)]
  | .vstore w m _ => [(m, 4 * w)]
  | .inserti128 _ _ m _ => [(m, 16)]
  | .inserti64x4 _ _ m _ => [(m, 32)]
  | .mov w _ (.mem m) => [(m, if w = 64 then 8 else 4)]
  | .movst w m _ => [(m, if w = 64 then 8 else 4)]
  | .alu _ _ _ (.mem m) => [(m, 4)]
  | .sub _ _ (.mem m) => [(m, 4)]
  | .cmp _ _ (.mem m) => [(m, 4)]
  | _ => []

/-- The rsp-relative slots `(base, offset, size)` of an instruction at a pc with fact `f`
(`push`/`pop`/`ret` access the 8-byte cell at the new/old rsp). -/
def slotsAt (i : Instr) (f : Fact) : List (Nat × Int × Nat) :=
  match i with
  | .push _ => [(f.sp.1, f.sp.2 - 8, 8)]
  | .pop _ => [(f.sp.1, f.sp.2, 8)]
  | .ret => [(f.sp.1, f.sp.2, 8)]
  | _ => (memOps i).filterMap fun (m, sz) =>
      if m.base = some 4 ∧ m.index = none then some (f.sp.1, f.sp.2 + m.disp, sz) else none

/-- Whether an instruction's rsp-based memory operand is indexed or rip-relative (unsupported for slots). -/
def rspIndexed (i : Instr) : Bool :=
  (memOps i).any fun (m, _) => m.base = some 4 ∧ (m.index ≠ none ∨ m.ro ≠ none)

def slotsAux (segs : List (Nat × Option Fact)) : Nat → List Instr → List (Nat × Int × Nat)
  | _, [] => []
  | p, i :: rest =>
    (match at? segs p with | some f => slotsAt i f | none => []) ++ slotsAux segs (p + 1) rest

/-- All frame slots of a stream under a segment table (deduplicated). -/
def slots (prog : Array Instr) (segs : List (Nat × Option Fact)) : List (Nat × Int × Nat) :=
  (slotsAux segs 0 prog.toList).eraseDups

/-- No rsp-based operand is indexed, and every rsp-based access is at a mapped pc. -/
def slotsOkAt (segs : List (Nat × Option Fact)) (p : Nat) (i : Instr) : Bool :=
  !rspIndexed i && (at? segs p ≠ none || (memOps i).all fun (m, _) => m.base ≠ some 4)

def slotsOkAux (segs : List (Nat × Option Fact)) : Nat → List Instr → Bool
  | _, [] => true
  | p, i :: rest => slotsOkAt segs p i && slotsOkAux segs (p + 1) rest

def slotsOk (prog : Array Instr) (segs : List (Nat × Option Fact)) : Bool :=
  slotsOkAux segs 0 prog.toList

end Hashtree.Asm.RspMap
