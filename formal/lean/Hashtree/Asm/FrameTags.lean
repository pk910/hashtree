import Hashtree.Asm.RspMap

/-!
# R5: the frame-slot certificate (tag flow of the callee-saved registers), steps 2-3

Push-saving bodies (sse_x1, avx_x1, avx2_x8) move the Win64 callee-saved registers into frame
cells and back.  With the plain liveness engine those cells are reads, so the entry live sets
contain the callee-saved registers.  Here the *items* are general registers and rsp-relative
frame slots `(base, offset, size)` (from the verified rsp map, `Asm/RspMap`), and a **tag**
`item ↦ n` says "this item holds the entry value of register `n`".  The tag table is a forward
must-analysis over the CFG (computed like `RunAgree.live`, verified per pc like `certB`):

* entry: every callee-saved register is tagged with itself;
* `push r` / `mov [rsp+k], r` copy the tag of `r` to the slot; `pop r` / `mov r, [rsp+k]` copy the
  slot's tag to `r`; every other write clears the tag of what it writes (registers in `dsts`;
  an rsp-based write drops the tags of the slots it *covers* and fails on a partial overwrite of
  a tagged slot, whose remaining cells would still differ);
* **no instruction reads a tagged item** except as the source of a push/save (a register) or
  of a pop/restore (a slot): registers in `srcs` must be untagged, and an rsp-based memory read
  must not overlap a tagged slot;
* at every exit (`ret`, tail jumps) every callee-saved register is tagged with itself, so the
  caller sees them restored, and rsp is never tagged;
* at a join every path carries the same tags (verified as equality of tag maps at every
  successor): an item that differs between the runs on one path and agrees on another would be
  neither.

A pc the rsp map leaves unmapped (dead code) carries no tags and is not checked.
`tagCert` is the decidable per-pc check; `tags` computes the table (fixpoint of `tagStep` over
`passes` in-order sweeps, intersecting at joins; unvisited pcs stay `none`).

## The semantic relation (statement; the run lift is the next step)

`TagRel T B s0 s0' s s'`: two runs from entry states `s0`, `s0'` that agree on everything except
the callee-saved registers and the memory below the entry rsp stay related at a pc with tags
`T`: untagged registers agree; a register tagged `n` holds its own run's entry value of `n`;
an untagged cell agrees; a slot tagged `n` holds (as an 8-byte value) its own run's entry value
of `n`; vector file, flags, pc, halted, tail, err agree.  `B : Nat → Int` gives the base values
(`B 0` = the entry rsp, `B 1` = the aligned base after `and rsp, -32`).  The lift (to prove):
`tagCert` + `RspMap.ok` ⇒ `TagRel` is preserved by every error-free step, provided that every
load through a base register other than rsp reads outside the frame window `[B 0 - D, B 0)`
(the kernel's own frame; true of the three bodies, whose non-rsp pointers are the rIn/rOut/rodata
pointers — a hypothesis of the lift, discharged per kernel by the region discipline of the
model).  At an exit the tags give `RegsOkW`'s callee-saved clauses and "memory equal outside the
frame".
-/

set_option autoImplicit false

namespace Hashtree.Asm.FrameTags

open Hashtree.Asm.X86 Hashtree.Asm.BodyReads Hashtree.Asm.RspMap

/-- A frame slot `(base, offset, size)`. -/
abbrev Slot := Nat × Int × Nat

inductive Item where
  | reg (r : Nat)
  | slot (s : Slot)
  deriving DecidableEq, Repr, Inhabited

/-- The status of an item: absent = the two runs agree on it; `some n` = it holds the entry value
of register `n` (tagged); `none` = free (no guarantee; the join of a tagged and an agreeing
path).  Tagged and free items may only be read by the copies. -/
abbrev Tags := List (Item × Option Nat)

/-- `some st` for a listed item (`st = some n` tagged, `st = none` free), `none` = agreeing. -/
def statusOf (T : Tags) (i : Item) : Option (Option Nat) := (T.find? (·.1 = i)).map (·.2)
def tagOf (T : Tags) (i : Item) : Option Nat := (statusOf T i).getD none
def clearItem (T : Tags) (i : Item) : Tags := T.filter (·.1 ≠ i)
/-- Give `i` the status `st` (absent = agreeing). -/
def setStatus (T : Tags) (i : Item) : Option (Option Nat) → Tags
  | some st => (i, st) :: clearItem T i
  | none => clearItem T i

/-- The cells of a slot as an interval relative to the entry rsp (base 0): a base-1 slot (after
`and rsp, -32` at entry rsp - 16) sits between `B 0 - 47` and `B 0 - 16` below the entry rsp, so
its interval is widened by that slack (the physical relation `B 1 - B 0 ∈ [-47, -16]` is a
hypothesis of the lift, `BaseRel`).  Other bases are not supported (an all-covering interval). -/
def phys (s : Slot) : Int × Int :=
  if s.1 = 0 then (s.2.1, s.2.1 + s.2.2)
  else if s.1 = 1 then (s.2.1 - 47, s.2.1 + s.2.2 - 16)
  else (-1000000000, 1000000000)

/-- Possibly overlapping cells: exact on the same base, through `phys` across bases. -/
def overlaps (s t : Slot) : Bool :=
  if s.1 = t.1 then s.2.1 < t.2.1 + t.2.2 && t.2.1 < s.2.1 + s.2.2
  else (phys s).1 < (phys t).2 && (phys t).1 < (phys s).2

/-- `s` covers `t` exactly enough (same base, every cell of `t` written). -/
def covers (s t : Slot) : Bool := s.1 = t.1 && s.2.1 ≤ t.2.1 && t.2.1 + t.2.2 ≤ s.2.1 + s.2.2

/-- A listed slot overlapping the write `s` becomes free. -/
def freeOv (s : Slot) (p : Item × Option Nat) : Item × Option Nat :=
  match p.1 with | .slot t => if overlaps s t then (p.1, none) else p | _ => p

/-- A write of `s` with agreeing data: every listed slot it overlaps must be covered, and becomes
free (its cells are rewritten with agreeing data, which the relation then need not know); a
partial overwrite of a listed slot is a failure. -/
def clearOverlap? (T : Tags) (s : Slot) : Option Tags :=
  if T.any (fun p => match p.1 with | .slot t => overlaps s t && !covers s t | _ => false) then none
  else some (T.map (freeOv s))

/-- Some listed slot overlaps `s` (a read of `s` could read a tagged or free cell). -/
def hitsTagged (T : Tags) (s : Slot) : Bool :=
  T.any fun p => match p.1 with | .slot t => overlaps s t | _ => false

/-- The registers are all agreeing (not listed). -/
def regsUntagged (T : Tags) (rs : List Nat) : Bool := rs.all fun r => statusOf T (.reg r) = none

/-- The rsp-relative slot of a memory operand, if it is rsp-based and unindexed. -/
def slotOf (f : Fact) (m : MemRef) (size : Nat) : Option Slot :=
  if m.base = some 4 ∧ m.index = none ∧ m.ro = none then some (f.sp.1, f.sp.2 + m.disp, size) else none

/-- The rsp-based memory operands (as slots) an instruction reads. -/
def readSlots (f : Fact) : Instr → List Slot
  | .pop _ => [(f.sp.1, f.sp.2, 8)]
  | .ret => [(f.sp.1, f.sp.2, 8)]
  | .vstore _ _ _ => []
  | .movst _ _ _ => []
  | i => (memOps i).filterMap fun (m, sz) => slotOf f m sz

/-- The registers written by an instruction become agreeing. -/
def clearRegs (T : Tags) (D : List Nat) : Tags := T.filter fun p => match p.1 with | .reg r => !decide (r ∈ D) | _ => true

/-- The rsp-based slot a general instruction writes. -/
def writeSlot (f : Fact) : Instr → Option Slot
  | .vstore w m _ => slotOf f m (4 * w)
  | .movst w m _ => slotOf f m (if w = 64 then 8 else 4)
  | _ => none

/-- A general instruction (not one of the four copies): every register it reads is agreeing,
every rsp-based read misses the listed slots; its register writes clear, its rsp-based write
frees the slots it covers (and fails on a partial overwrite). -/
def generalStep (f : Fact) (i : Instr) (T : Tags) : Option Tags :=
  if regsUntagged T (srcs i) && !(readSlots f i).any (hitsTagged T) then
    match writeSlot f i with
    | some sl => clearOverlap? (clearRegs T (dsts i)) sl
    | none => some (clearRegs T (dsts i))
  else none

/-- The four copies: `push`, `pop`, `mov [rsp+k], r` and `mov r, [rsp+k]` (64-bit). -/
def isCopy : Instr → Bool
  | .push _ => true
  | .pop _ => true
  | .movst w _ _ => w == 64
  | .mov w _ (.mem _) => w == 64
  | _ => false

/-- One instruction's effect on the statuses; `none` = the certificate fails here (a listed item
is read other than by a copy, or a listed slot is partially overwritten). -/
def tagStep (f : Fact) (i : Instr) (T : Tags) : Option Tags :=
  match i with
  | .push r =>
    if statusOf T (.reg 4) ≠ none then none else
    let s : Slot := (f.sp.1, f.sp.2 - 8, 8)
    (clearOverlap? T s).map fun T1 => setStatus T1 (.slot s) (statusOf T (.reg r))
  | .pop r =>
    if statusOf T (.reg 4) ≠ none ∨ r = 4 ∨ 16 ≤ r then none else
    match statusOf T (.slot (f.sp.1, f.sp.2, 8)) with
    | some none => none   -- a free slot (no guarantee on either run's cells): not readable
    | none => if hitsTagged T (f.sp.1, f.sp.2, 8) then none else some (setStatus T (.reg r) none)
    | some (some n) => some (setStatus T (.reg r) (some (some n)))
  | .movst w m s =>
    if w = 64 then
      if !regsUntagged T (memRegs m) then none else
      match slotOf f m 8 with
      | some sl => (clearOverlap? T sl).map fun T1 => setStatus T1 (.slot sl) (statusOf T (.reg s))
      | none => if statusOf T (.reg s) ≠ none then none else some T
    else generalStep f i T
  | .mov w d (.mem m) =>
    if w = 64 then
      if !regsUntagged T (memRegs m) || 16 ≤ d then none else
      match slotOf f m 8 with
      | some sl =>
        match statusOf T (.slot sl) with
        | some none => none
        | none => if hitsTagged T sl then none else some (setStatus T (.reg d) none)
        | some (some n) => some (setStatus T (.reg d) (some (some n)))
      | none => some (clearItem T (.reg d))
    else generalStep f i T
  | _ => generalStep f i T

/-- The exit condition: every callee-saved register tagged with itself, rsp agreeing. -/
def exitOk (cs : List Nat) (T : Tags) : Bool :=
  cs.all (fun r => statusOf T (.reg r) = some (some r)) && statusOf T (.reg 4) = none

def isExit : Instr → Bool
  | .ret => true | .jmpTail _ => true | .jccTail _ _ => true | _ => false

/-- `T ⊑ T'`: every item's status in `T'` is free, or equal to its status in `T` (so what `T`
guarantees implies what `T'` guarantees). -/
def leqTags (T T' : Tags) : Bool :=
  (T.all fun p => statusOf T' p.1 = some none ∨ statusOf T' p.1 = some p.2) &&
  (T'.all fun p => p.2 = none ∨ statusOf T p.1 = some p.2)

/-- The entry tags of a callee-saved set. -/
def entryTags (cs : List Nat) : Tags := cs.map fun r => (.reg r, some r)

/-- Every listed slot is an 8-byte cell on base 0 or 1 (what the lift's slot values read). -/
def tableOk (T : Tags) : Bool :=
  T.all fun p => match p.1 with | .slot t => (t.1 == 0 || t.1 == 1) && t.2.2 == 8 | _ => true

/-- The tag table as segments `(start pc, tags)` (as the rsp map: a pc takes the value of the last
segment starting at or before it; `none` = unvisited). -/
abbrev TagSegs := List (Nat × Option Tags)

def atT (TT : TagSegs) (p : Nat) : Option Tags :=
  TT.foldl (fun acc s => if s.1 ≤ p then s.2 else acc) none

/-- The check at one pc: an unmapped or unvisited pc is not checked; otherwise the step is
defined, rsp is agreeing and the listed slots are 8-byte cells on base 0/1 (`tableOk`), exits
satisfy `exitOk` (after the step), and the stepped tags are below every successor's tags
(`leqTags`). -/
def tagAt (n : Nat) (segs : List (Nat × Option Fact)) (TT : TagSegs) (cs : List Nat)
    (p : Nat) (i : Instr) : Bool :=
  match at? segs p, atT TT p with
  | none, _ => true
  | some _, none => true
  | some f, some T =>
    statusOf T (.reg 4) = none && (f.saved = none || statusOf T (.reg 5) = none) && tableOk T &&
    match tagStep f i T with
    | none => false
    | some T' =>
      (!isExit i || exitOk cs T') &&
      (nexts p i).all fun q => q < n && (match atT TT q with | some Tq => leqTags T' Tq | none => false)

def tagAux (n : Nat) (segs : List (Nat × Option Fact)) (TT : TagSegs) (cs : List Nat) :
    Nat → List Instr → Bool
  | _, [] => true
  | p, i :: rest => tagAt n segs TT cs p i && tagAux n segs TT cs (p + 1) rest

/-- **The frame-slot certificate check**: entry tags, and `tagAt` at every pc (a linear sweep). -/
def tagCert (n : Nat) (prog : Array Instr) (segs : List (Nat × Option Fact)) (TT : TagSegs)
    (cs : List Nat) : Bool :=
  atT TT 0 = some (entryTags cs) && tagAux n segs TT cs 0 prog.toList

/-! ## Computing the table -/

/-- The join: equal statuses are kept, a disagreement (tagged vs agreeing, or different sources)
becomes free. -/
def meet (T T' : Tags) : Tags :=
  let items := (T.map (·.1) ++ T'.map (·.1)).eraseDups
  items.filterMap fun i =>
    match statusOf T i, statusOf T' i with
    | some a, some b => if a = b then some (i, a) else some (i, none)
    | some _, none => some (i, none)
    | none, some _ => some (i, none)
    | none, none => none

/-- One in-order sweep. -/
def tagPass (prog : Array Instr) (segs : List (Nat × Option Fact)) (TT : Array (Option Tags)) :
    Array (Option Tags) := Id.run do
  let mut A := TT
  for p in [0:prog.size] do
    match at? segs p, A[p]!, prog[p]? with
    | some f, some T, some i =>
      match tagStep f i T with
      | some T' =>
        for q in nexts p i do
          if q < prog.size then
            A := A.set! q (match A[q]! with | some Tq => some (meet Tq T') | none => some T')
      | none => pure ()
    | _, _, _ => pure ()
  return A

/-- The tag table: `passes` sweeps from the entry tags (unvisited pcs stay `none`); `#eval` only. -/
def tagsArr (prog : Array Instr) (segs : List (Nat × Option Fact)) (cs : List Nat) (passes : Nat := 16) :
    Array (Option Tags) := Id.run do
  let mut A : Array (Option Tags) := Array.replicate prog.size none
  A := A.set! 0 (some (entryTags cs))
  for _ in [0:passes] do A := tagPass prog segs A
  return A

/-- The table as segments (runs of equal tag sets); `#eval` only, the literal goes into the proof. -/
def tags (prog : Array Instr) (segs : List (Nat × Option Fact)) (cs : List Nat) (passes : Nat := 16) :
    TagSegs := Id.run do
  let A := tagsArr prog segs cs passes
  let mut out : TagSegs := []
  let mut last : Option (Option Tags) := none
  for p in [0:A.size] do
    if last ≠ some A[p]! then
      out := out ++ [(p, A[p]!)]
      last := some A[p]!
  return out

/-- Where the step fails (for `#eval`). -/
def failures (prog : Array Instr) (segs : List (Nat × Option Fact)) (TT : TagSegs) : List Nat :=
  (List.range prog.size).filter fun p =>
    match at? segs p, atT TT p, prog[p]? with
    | some f, some T, some i => (tagStep f i T).isNone
    | _, _, _ => false


/-! ## The semantic relation and the lift statement (the proof is the next step) -/

section Semantics
open Hashtree.Asm

/-- The cells of a slot under the base values `B`. -/
def inSlot (B : Nat → Int) (sl : Slot) (a : Addr Int) : Prop :=
  a.region = rStack ∧ B sl.1 + sl.2.1 ≤ a.off ∧ a.off < B sl.1 + sl.2.1 + (sl.2.2 : Int)

/-- `a` lies in a listed (tagged or free) slot of `T`. -/
def InTagged (B : Nat → Int) (T : Tags) (a : Addr Int) : Prop :=
  ∃ sl, statusOf T (.slot sl) ≠ none ∧ inSlot B sl a

/-- The 8-byte value of a slot (as `pop` would read it). -/
def slotVal (mem0 : Addr Int → Cell W32 Int) (B : Nat → Int) (s : State W32 Int) (sl : Slot) :=
  Hashtree.Asm.loadVal mem0 s ⟨rStack, B sl.1 + sl.2.1⟩

/-- **The tag relation** at a pc with tags `T`: two runs (`s`, `s'`, from entry states `s0`, `s0'`,
over the same initial memory)
agree on every agreeing (unlisted) register and every cell outside the listed slots; a register
tagged `n` holds its own run's entry value of `n`, a slot tagged `n` holds it as its 8-byte value;
free items are unconstrained; the vector file, flags, pc, halted, tail and err agree. -/
structure TagRel (mem0 : Addr Int → Cell W32 Int) (B : Nat → Int) (T : Tags) (s0 s0' s s' : State W32 Int) : Prop where
  reg : ∀ r, statusOf T (.reg r) = none → s.getG r = s'.getG r
  tagReg : ∀ r n, statusOf T (.reg r) = some (some n) → s.getG r = s0.getG n ∧ s'.getG r = s0'.getG n
  tagSlot : ∀ sl n, statusOf T (.slot sl) = some (some n) →
    slotVal mem0 B s sl = Except.ok (s0.getG n) ∧ slotVal mem0 B s' sl = Except.ok (s0'.getG n)
  mem : ∀ a, ¬ InTagged B T a → Hashtree.Asm.lookup a s.mem = Hashtree.Asm.lookup a s'.mem
  len : s.gpr.length = s'.gpr.length
  len16 : s.gpr.length = 16
  vr : s.vr = s'.vr
  flags : s.flags = s'.flags
  pc : s.pc = s'.pc
  halted : s.halted = s'.halted
  tail : s.tail = s'.tail
  err : s.err = s'.err

/-- The rsp map, semantically: at a mapped pc, `rsp = B base + δ`, and `rbp` holds the saved rsp
value when the fact records one. -/
def RspOk (B : Nat → Int) (f : Fact) (s : State W32 Int) : Prop :=
  s.getG 4 = .ptr ⟨rStack, B f.sp.1 + f.sp.2⟩ ∧
  ∀ v, f.saved = some v → s.getG 5 = .ptr ⟨rStack, B v.1 + v.2⟩

/-- **The lift (to prove)**: under a verified rsp map and tag table, one error-free step of the
certified program from related states at a mapped pc gives related states at the successor pc,
provided the step's loads through base registers other than rsp read no cell of the frame
window `[B 0 - D, B 0)` (the kernel's own frame; a hypothesis discharged per kernel by the
model's region discipline). -/
def LiftSpec (n : Nat) (prog : Array Instr) (segs : List (Nat × Option Fact)) (TT : TagSegs)
    (cs : List Nat) (D : Int) : Prop :=
  RspMap.ok n prog segs = true → tagCert n prog segs TT cs = true →
  ∀ (mem0 : Addr Int → Cell W32 Int) (B : Nat → Int) (orc : Nat → Bool) (s0 s0' s s' : State W32 Int)
    (f : Fact) (T : Tags),
    at? segs s.pc = some f → atT TT s.pc = some T →
    RspOk B f s → TagRel mem0 B T s0 s0' s s' →
    (X86.run prog 4 mem0 orc 1 s).err = none →
    (∀ i, prog[s.pc]? = some i → ∀ m ∈ memOps i, m.1.base ≠ some 4 →
      ∀ a : Addr Int, X86.effAddr 4 s m.1 = Except.ok a → a.region = rStack → ¬ (B 0 - D ≤ a.off ∧ a.off < B 0)) →
    ∃ T', atT TT (X86.run prog 4 mem0 orc 1 s).pc = some T' ∧
      TagRel mem0 B T' s0 s0' (X86.run prog 4 mem0 orc 1 s) (X86.run prog 4 mem0 orc 1 s')

end Semantics

end Hashtree.Asm.FrameTags
