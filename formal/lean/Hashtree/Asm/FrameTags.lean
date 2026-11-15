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
* `push r` / `mov [rsp+k], r` copy the tag of `r` to the slot (after clearing every overlapping
  slot); `pop r` / `mov r, [rsp+k]` copy the slot's tag to `r`; every other write clears the tag
  of what it writes (registers in `dsts`, rsp-based memory operands by overlap);
* **no instruction reads a tagged item** except as the source of a push/save (a register) or
  of a pop/restore (a slot): registers in `srcs` must be untagged, and an rsp-based memory read
  must not overlap a tagged slot;
* at every exit (`ret`, tail jumps) every callee-saved register is tagged with itself, so the
  caller sees them restored, and rsp is never tagged.

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

/-- The tagged items of a pc with their source register. -/
abbrev Tags := List (Item × Nat)

def tagOf (T : Tags) (i : Item) : Option Nat := (T.find? (·.1 = i)).map (·.2)
def clearItem (T : Tags) (i : Item) : Tags := T.filter (·.1 ≠ i)
def setTag (T : Tags) (i : Item) : Option Nat → Tags
  | some n => (i, n) :: clearItem T i
  | none => clearItem T i

def overlaps (s t : Slot) : Bool := s.1 = t.1 && s.2.1 < t.2.1 + t.2.2 && t.2.1 < s.2.1 + s.2.2

/-- Clear every slot overlapping `s` (a write of unknown data into `s`). -/
def clearOverlap (T : Tags) (s : Slot) : Tags :=
  T.filter fun p => match p.1 with | .slot t => !overlaps s t | _ => true

/-- Some slot overlapping `s` is tagged (a read of `s` would read tagged data). -/
def hitsTagged (T : Tags) (s : Slot) : Bool :=
  T.any fun p => match p.1 with | .slot t => overlaps s t | _ => false

def regsUntagged (T : Tags) (rs : List Nat) : Bool := rs.all fun r => tagOf T (.reg r) = none

/-- The rsp-relative slot of a memory operand, if it is rsp-based and unindexed. -/
def slotOf (f : Fact) (m : MemRef) (size : Nat) : Option Slot :=
  if m.base = some 4 ∧ m.index = none then some (f.sp.1, f.sp.2 + m.disp, size) else none

/-- The rsp-based memory operands (as slots) an instruction reads, and whether it has a non-rsp or
indexed memory operand (whose cells are outside the frame by the lift's hypothesis). -/
def readSlots (f : Fact) : Instr → List Slot
  | .pop _ => [(f.sp.1, f.sp.2, 8)]
  | .ret => [(f.sp.1, f.sp.2, 8)]
  | .vstore _ _ _ => []
  | .movst _ _ _ => []
  | i => (memOps i).filterMap fun (m, sz) => slotOf f m sz

/-- One instruction's effect on the tags; `none` = the certificate fails here (a tagged item is
read other than by a copy). -/
def tagStep (f : Fact) (i : Instr) (T : Tags) : Option Tags :=
  match i with
  | .push r =>
    if tagOf T (.reg 4) ≠ none then none else
    let s : Slot := (f.sp.1, f.sp.2 - 8, 8)
    some (setTag (clearOverlap T s) (.slot s) (tagOf T (.reg r)))
  | .pop r =>
    if tagOf T (.reg 4) ≠ none ∨ r = 4 then none else
    some (setTag T (.reg r) (tagOf T (.slot (f.sp.1, f.sp.2, 8))))
  | .movst 64 m s =>
    if !regsUntagged T (memRegs m) then none else
    match slotOf f m 8 with
    | some sl => some (setTag (clearOverlap T sl) (.slot sl) (tagOf T (.reg s)))
    | none => if tagOf T (.reg s) ≠ none then none else some T
  | .mov 64 d (.mem m) =>
    if !regsUntagged T (memRegs m) then none else
    match slotOf f m 8 with
    | some sl => some (setTag T (.reg d) (tagOf T (.slot sl)))
    | none => some (clearItem T (.reg d))
  | _ =>
    -- a general instruction: every register it reads is untagged, every rsp-based read misses the
    -- tagged slots; its register writes clear, its rsp-based writes clear by overlap
    if !regsUntagged T (srcs i) then none else
    if (readSlots f i).any (hitsTagged T) then none else
    let T1 := (dsts i).foldl (fun acc r => clearItem acc (.reg r)) T
    let T2 := match i with
      | .vstore w m _ => match slotOf f m (4 * w) with | some sl => clearOverlap T1 sl | none => T1
      | .movst w m _ => match slotOf f m (w / 8) with | some sl => clearOverlap T1 sl | none => T1
      | _ => T1
    some T2

/-- The exit condition: every callee-saved register tagged with itself, rsp untagged. -/
def exitOk (cs : List Nat) (T : Tags) : Bool :=
  cs.all (fun r => tagOf T (.reg r) = some r) && tagOf T (.reg 4) = none

def isExit : Instr → Bool
  | .ret => true | .jmpTail _ => true | .jccTail _ _ => true | _ => false

/-- `T ⊆ T'` as tag maps. -/
def subTags (T T' : Tags) : Bool := T.all fun p => tagOf T' p.1 = some p.2

/-- The entry tags of a callee-saved set. -/
def entryTags (cs : List Nat) : Tags := cs.map fun r => (.reg r, r)

/-- The tag table as segments `(start pc, tags)` (as the rsp map: a pc takes the value of the last
segment starting at or before it; `none` = unvisited). -/
abbrev TagSegs := List (Nat × Option Tags)

def atT (TT : TagSegs) (p : Nat) : Option Tags :=
  TT.foldl (fun acc s => if s.1 ≤ p then s.2 else acc) none

/-- The check at one pc: an unmapped or unvisited pc is not checked; otherwise the step is
defined, exits satisfy `exitOk` (after the step), and every successor's tags are contained in the
stepped tags. -/
def tagAt (n : Nat) (segs : List (Nat × Option Fact)) (TT : TagSegs) (cs : List Nat)
    (p : Nat) (i : Instr) : Bool :=
  match at? segs p, atT TT p with
  | none, _ => true
  | some _, none => true
  | some f, some T =>
    match tagStep f i T with
    | none => false
    | some T' =>
      (!isExit i || exitOk cs T') &&
      (nexts p i).all fun q => q < n && (match atT TT q with | some Tq => subTags Tq T' | none => false)

def tagAux (n : Nat) (segs : List (Nat × Option Fact)) (TT : TagSegs) (cs : List Nat) :
    Nat → List Instr → Bool
  | _, [] => true
  | p, i :: rest => tagAt n segs TT cs p i && tagAux n segs TT cs (p + 1) rest

/-- **The frame-slot certificate check**: entry tags, and `tagAt` at every pc (a linear sweep). -/
def tagCert (n : Nat) (prog : Array Instr) (segs : List (Nat × Option Fact)) (TT : TagSegs)
    (cs : List Nat) : Bool :=
  atT TT 0 = some (entryTags cs) && tagAux n segs TT cs 0 prog.toList

/-! ## Computing the table -/

/-- Intersection of tag maps (a join of the must-analysis). -/
def meet (T T' : Tags) : Tags := T.filter fun p => tagOf T' p.1 = some p.2

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

/-- `a` lies in a tagged slot of `T`. -/
def InTagged (B : Nat → Int) (T : Tags) (a : Addr Int) : Prop :=
  ∃ p ∈ T, ∃ sl, p.1 = .slot sl ∧ inSlot B sl a

/-- The 8-byte value of a slot (as `pop` would read it). -/
def slotVal (mem0 : Addr Int → Cell W32 Int) (B : Nat → Int) (s : State W32 Int) (sl : Slot) :=
  Hashtree.Asm.loadVal mem0 s ⟨rStack, B sl.1 + sl.2.1⟩

/-- **The tag relation** at a pc with tags `T`: two runs (`s`, `s'`, from entry states `s0`, `s0'`)
agree on every untagged register and every cell outside the tagged slots; a register tagged `n`
holds its own run's entry value of `n`, a slot tagged `n` holds it as its 8-byte value; the
vector file, flags, pc, halted, tail and err agree. -/
structure TagRel (mem0 mem0' : Addr Int → Cell W32 Int) (B : Nat → Int) (T : Tags) (s0 s0' s s' : State W32 Int) : Prop where
  reg : ∀ r, tagOf T (.reg r) = none → s.getG r = s'.getG r
  tagReg : ∀ r n, tagOf T (.reg r) = some n → s.getG r = s0.getG n ∧ s'.getG r = s0'.getG n
  tagSlot : ∀ sl n, tagOf T (.slot sl) = some n →
    slotVal mem0 B s sl = Except.ok (s0.getG n) ∧ slotVal mem0' B s' sl = Except.ok (s0'.getG n)
  mem : ∀ a, ¬ InTagged B T a → Hashtree.Asm.lookup a s.mem = Hashtree.Asm.lookup a s'.mem
  len : s.gpr.length = s'.gpr.length
  vr : s.vr = s'.vr
  flags : s.flags = s'.flags
  pc : s.pc = s'.pc
  halted : s.halted = s'.halted
  tail : s.tail = s'.tail
  err : s.err = s'.err

/-- The rsp map, semantically: at a mapped pc, `rsp = B base + δ`. -/
def RspOk (B : Nat → Int) (f : Fact) (s : State W32 Int) : Prop :=
  s.getG 4 = .ptr ⟨rStack, B f.sp.1 + f.sp.2⟩

/-- **The lift (to prove)**: under a verified rsp map and tag table, one error-free step of the
certified program from related states at a mapped pc gives related states at the successor pc,
provided the step's loads through base registers other than rsp read no cell of the frame
window `[B 0 - D, B 0)` (the kernel's own frame; a hypothesis discharged per kernel by the
model's region discipline). -/
def LiftSpec (n : Nat) (prog : Array Instr) (segs : List (Nat × Option Fact)) (TT : TagSegs)
    (cs : List Nat) (D : Int) : Prop :=
  RspMap.ok n prog segs = true → tagCert n prog segs TT cs = true →
  ∀ (mem0 mem0' : Addr Int → Cell W32 Int) (B : Nat → Int) (orc : Nat → Bool) (s0 s0' s s' : State W32 Int)
    (f : Fact) (T : Tags),
    at? segs s.pc = some f → atT TT s.pc = some T →
    RspOk B f s → TagRel mem0 mem0' B T s0 s0' s s' →
    (X86.run prog 4 mem0 orc 1 s).err = none →
    (∀ i, prog[s.pc]? = some i → ∀ m ∈ memOps i, m.1.base ≠ some 4 →
      ∀ a : Addr Int, X86.effAddr 4 s m.1 = Except.ok a → a.region = rStack → ¬ (B 0 - D ≤ a.off ∧ a.off < B 0)) →
    ∃ T', atT TT (X86.run prog 4 mem0 orc 1 s).pc = some T' ∧
      TagRel mem0 mem0' B T' s0 s0' (X86.run prog 4 mem0 orc 1 s) (X86.run prog 4 mem0' orc 1 s')

end Semantics

end Hashtree.Asm.FrameTags
