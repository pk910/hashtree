import Hashtree.Asm.Core

/-!
# x86-64: the instructions the hashtree kernels use

Semantics follow the Intel SDM (Vol. 2) for the operand forms the shipped objects contain
(`results/isa_census.md`). Vector registers hold 16 lanes (zmm); `xmm`/`ymm` operands use the
low 4/8. VEX/EVEX-encoded writes zero the lanes above the operand width; legacy SSE writes
leave them unchanged. General registers hold data (two lanes) or a pointer/count; 32-bit data
operations write the low lane and zero the high lane, as the machine does.

Flags are only modelled for comparisons of pointers/counts (`cmp`, `test`, and `sub`/`add` on a
pointer/count register, which set them from the result); every data operation clobbers them.
-/

namespace Hashtree.Asm.X86
open Hashtree.Asm

/-- A memory operand `[base + index*scale + disp]`; `ro = some o`: rip-relative, `.rodata + o`. -/
structure MemRef where
  base : Option Nat := none
  index : Option Nat := none
  scale : Nat := 1
  disp : Int := 0
  ro : Option Int := none
  deriving DecidableEq, Repr, Inhabited

/-- A vector source: a register or memory. -/
inductive VSrc where
  | reg (i : Nat)
  | mem (m : MemRef)
  deriving DecidableEq, Repr, Inhabited

/-- A 32/64-bit GPR source operand. -/
inductive GSrc where
  | reg (i : Nat)
  | imm (v : Int)
  | mem (m : MemRef)
  deriving DecidableEq, Repr, Inhabited

/-- Lane-wise binary operations. -/
inductive LOp where
  | add | xor | and | or
  deriving DecidableEq, Repr, Inhabited

inductive Shift where
  | shl | shr | sar
  deriving DecidableEq, Repr, Inhabited

/-- Branch conditions (on the last comparison `a - b` of control values). -/
inductive CC where
  | e | ne | l | ge | le | g | b | ae | be | a
  deriving DecidableEq, Repr, Inhabited

inductive Instr where
  | nop
  -- vector
  | vop (op : LOp) (vex : Bool) (w : Nat) (d : Nat) (s1 : Nat) (s2 : VSrc)
  | vshift (k : Shift) (vex : Bool) (w : Nat) (d : Nat) (s : Nat) (n : Nat)
  | vshiftq (vex : Bool) (w : Nat) (d : Nat) (s : Nat) (n : Nat)       -- psrlq / vpsrlq
  | vror (w : Nat) (d : Nat) (s : Nat) (n : Nat)                       -- vprord
  | vtern (w : Nat) (d : Nat) (s1 : Nat) (s2 : Nat) (imm : Nat)          -- vpternlogd
  | vload (vex : Bool) (w : Nat) (d : Nat) (s : VSrc)                    -- mov* reg <- reg/mem
  | vstore (w : Nat) (m : MemRef) (s : Nat)                              -- mov* mem <- reg
  | pshufd (vex : Bool) (d : Nat) (s : Nat) (imm : Nat)
  | pshufb (vex : Bool) (w : Nat) (d : Nat) (s : Nat) (mask : Nat)
  | palignr (vex : Bool) (d : Nat) (s1 : Nat) (s2 : Nat) (imm : Nat)
  | pblendw (d : Nat) (s : Nat) (imm : Nat)
  | shufps (w : Nat) (d : Nat) (s1 : Nat) (s2 : Nat) (imm : Nat)
  | perm2f128 (d : Nat) (s1 : Nat) (s2 : Nat) (imm : Nat)
  | inserti128 (d : Nat) (s1 : Nat) (m : MemRef) (imm : Nat)
  | inserti64x4 (d : Nat) (s1 : Nat) (m : MemRef) (imm : Nat)
  | permi2d (d : Nat) (s1 : Nat) (s2 : Nat)
  | permi2q (d : Nat) (s1 : Nat) (s2 : Nat)
  | sha256rnds2 (d : Nat) (s : Nat)
  | sha256msg1 (d : Nat) (s : Nat)
  | sha256msg2 (d : Nat) (s : Nat)
  -- general registers (w = 32 or 64)
  | mov (w : Nat) (d : Nat) (s : GSrc)
  | movst (w : Nat) (m : MemRef) (s : Nat)
  | alu (op : LOp) (w : Nat) (d : Nat) (s : GSrc)
  | sub (w : Nat) (d : Nat) (s : GSrc)
  | lea (d : Nat) (m : MemRef)
  | ror (w : Nat) (d : Nat) (n : Nat)
  | shld (w : Nat) (d : Nat) (s : Nat) (n : Nat)
  | shl (w : Nat) (d : Nat) (n : Nat)
  | bswap (w : Nat) (d : Nat)
  | push (r : Nat)
  | pop (r : Nat)
  | cmp (w : Nat) (a : Nat) (b : GSrc)
  | test (w : Nat) (a : Nat) (b : Nat)
  | jcc (c : CC) (t : Nat)
  | jmp (t : Nat)
  | jccTail (c : CC) (name : String)
  | jmpTail (name : String)
  | ret
  deriving DecidableEq, Repr, Inhabited

/-! ## Helpers -/

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

def rsp : Nat := 4

def zeroLanes (n : Nat) : List α := List.replicate n (Lane.const 0)

/-- Write the low `w` lanes of a vector register; VEX zeroes the rest, legacy keeps it. -/
def setVec (s : State α γ) (vex : Bool) (w : Nat) (d : Nat) (v : List α) : State α γ :=
  let old := s.getV d
  let v := v.take w
  s.setV d (if vex then v ++ zeroLanes (16 - w) else v ++ old.drop w)

/-- A register holding a pointer. -/
def regPtr (s : State α γ) (r : Nat) : Except String (Addr γ) :=
  match s.getG r with
  | .ptr a => .ok a
  | .num _ _ => .error "data register as address"

/-- The base of a memory operand: rip-relative rodata, a base register, or absolute. -/
def baseAddr (ro : Region) (s : State α γ) (m : MemRef) : Except String (Addr γ) :=
  match m.ro with
  | some o => .ok ⟨ro, Ctl.ofInt o⟩
  | none => match m.base with
    | some b => regPtr s b
    | none => .ok ⟨rNum, Ctl.ofInt 0⟩

/-- Effective address `base + disp + index*scale` (the index must be a number). -/
def effAddr (ro : Region) (s : State α γ) (m : MemRef) : Except String (Addr γ) :=
  match baseAddr ro s m with
  | .error e => .error e
  | .ok b =>
    let b := b.plusI m.disp
    match m.index with
    | none => .ok b
    | some i => match s.getG i with
      | .ptr ⟨0, n⟩ => .ok (b.plus (Ctl.smul m.scale n))
      | _ => .error "index is not a number"

def readVSrc (ro : Region) (mem0 : Addr γ → Cell α γ) (s : State α γ) (w : Nat) : VSrc → Except String (List α)
  | .reg i => pure ((s.getV i).take w)
  | .mem m => do loadLanes mem0 s (← effAddr ro s m) w

def lanes2 (f : α → α → α) (a b : List α) : List α := List.zipWith f a b

def lanes3 (f : α → α → α → α) : List α → List α → List α → List α
  | a :: as, b :: bs, c :: cs => f a b c :: lanes3 f as bs cs
  | _, _, _ => []

/-- `x & -m` for a power of two `m` (alignment), else `x & y` on naturals. -/
def andInt (x y : Int) : Option Int :=
  if y < 0 then
    let m := (-y).toNat
    if m ≠ 0 ∧ m &&& (m - 1) = 0 then some (x - x % (m : Int)) else none
  else if x ≥ 0 then some ((x.toNat &&& y.toNat : Nat) : Int) else none

def lop : LOp → α → α → α
  | .add => Lane.add
  | .xor => Lane.xor
  | .and => Lane.and
  | .or => Lane.or

def shiftL : Shift → α → Nat → α
  | .shl => fun x n => if n < 32 then Lane.shl x n else Lane.const 0
  | .shr => fun x n => if n < 32 then Lane.shr x n else Lane.const 0
  | .sar => fun x n => Lane.sar x (min n 31)

/-- 64-bit right shift of pairs of lanes. -/
def shrQ (lo hi : α) (n : Nat) : α × α :=
  if n = 0 then (lo, hi)
  else if n < 32 then (Lane.or (Lane.shr lo n) (Lane.shl hi (32 - n)), Lane.shr hi n)
  else if n < 64 then (Lane.shr hi (n - 32), Lane.const 0)
  else (Lane.const 0, Lane.const 0)

def pairs : List α → List (α × α)
  | a :: b :: rest => (a, b) :: pairs rest
  | _ => []

def unpairs : List (α × α) → List α
  | (a, b) :: rest => a :: b :: unpairs rest
  | [] => []

/-- Byte `j` (0..15 within a 128-bit lane group `g`) of a lane list. -/
def vbyte (v : List α) (g j : Nat) : α := byteOf (v.getD (4 * g + j / 4) (Lane.const 0)) (j % 4)

/-- Assemble a lane from four bytes (each in [0,256)). -/
def ofBytes (b0 b1 b2 b3 : α) : α :=
  Lane.or (Lane.or b0 (Lane.shl b1 8)) (Lane.or (Lane.shl b2 16) (Lane.shl b3 24))

/-- The values of lanes that must be constants (shuffle masks, permute indices). -/
def constsOf : List α → Except String (List W32)
  | [] => .ok []
  | x :: xs => match Lane.asConst x with
    | some v => match constsOf xs with
      | .ok vs => .ok (v :: vs)
      | .error e => .error e
    | none => .error "control lane not constant"

/-- The first `w` lanes of a control register, as constants. -/
def ctlLanes (v : List α) (w : Nat) : Except String (List W32) :=
  constsOf ((List.range w).map (fun i => v.getD i (Lane.const 0)))

/-- `pshufb` with constant mask lanes `ms` on lane groups of 4 (128 bits). -/
def pshufbP (v : List α) (ms : List W32) : List α :=
  (List.range ms.length).map fun i =>
    let m := ms.getD i 0
    let sel (k : Nat) : α :=
      let mb := (m >>> (8 * k)).toNat % 256
      if mb ≥ 128 then Lane.const 0 else vbyte v (i / 4) (mb % 16)
    ofBytes (sel 0) (sel 1) (sel 2) (sel 3)

/-- `pshufb` on lane groups of 4 (128 bits); the mask must be constant. -/
def pshufbL (v : List α) (mask : List α) (w : Nat) : Except String (List α) := do
  pure (pshufbP v (← ctlLanes mask w))

/-- `vpermi2d`: lane `i` from table `a` (index < 16) or `b`, by the constant index lanes. -/
def permi2dP (a b : List α) (idx : List W32) : List α :=
  idx.map fun k => let k := k.toNat % 32
    (if k < 16 then a else b).getD (k % 16) (Lane.const 0)

/-- `vpermi2q`: qword `q` (lanes 2q, 2q+1) by the index in the low lane of qword `q`. -/
def permi2qP (a b : List α) (idx : List W32) : List α :=
  ((List.range 8).map fun q =>
    let k := (idx.getD (2 * q) 0).toNat % 16
    let t := if k < 8 then a else b
    [t.getD (2 * (k % 8)) (Lane.const 0), t.getD (2 * (k % 8) + 1) (Lane.const 0)]).flatten

/-- Byte `j` of the 32-byte concatenation `hi:lo` (128-bit each, as lane lists). -/
def catByte (hi lo : List α) (j : Nat) : α :=
  if j < 16 then vbyte lo 0 j else if j < 32 then vbyte hi 0 (j - 16) else Lane.const 0

/-- `palignr`: `(hi:lo) >> 8·imm`, low 128 bits. -/
def palignrL (hi lo : List α) (imm : Nat) : List α :=
  if imm % 4 = 0 then
    (List.range 4).map fun i => let j := i + imm / 4
      if j < 4 then lo.getD j (Lane.const 0) else if j < 8 then hi.getD (j - 4) (Lane.const 0) else Lane.const 0
  else
    (List.range 4).map fun i =>
      ofBytes (catByte hi lo (4 * i + imm)) (catByte hi lo (4 * i + 1 + imm))
        (catByte hi lo (4 * i + 2 + imm)) (catByte hi lo (4 * i + 3 + imm))

/-- `pblendw`: 16-bit words from `s` where the immediate bit is set. -/
def pblendwL (d s : List α) (imm : Nat) : List α :=
  (List.range 4).map fun i =>
    let lo := imm.testBit (2 * i)
    let hi := imm.testBit (2 * i + 1)
    let x := d.getD i (Lane.const 0)
    let y := s.getD i (Lane.const 0)
    if lo && hi then y else if !lo && !hi then x
    else
      let (a, b) := if lo then (y, x) else (x, y)
      Lane.or (Lane.and a (Lane.const 0x0000ffff)) (Lane.and b (Lane.const 0xffff0000))

/-! ## SHA extensions (Intel SDM, SHA256RNDS2 / SHA256MSG1 / SHA256MSG2) -/

def rotr (x : α) (n : Nat) : α := Lane.ror x n
def bsig0 (x : α) : α := Lane.xor (Lane.xor (rotr x 2) (rotr x 13)) (rotr x 22)
def bsig1 (x : α) : α := Lane.xor (Lane.xor (rotr x 6) (rotr x 11)) (rotr x 25)
def ssig0 (x : α) : α := Lane.xor (Lane.xor (rotr x 7) (rotr x 18)) (Lane.shr x 3)
def ssig1 (x : α) : α := Lane.xor (Lane.xor (rotr x 17) (rotr x 19)) (Lane.shr x 10)
def chF (e f g : α) : α := Lane.xor (Lane.and e f) (Lane.and (Lane.not e) g)
def majF (a b c : α) : α := Lane.xor (Lane.xor (Lane.and a b) (Lane.and a c)) (Lane.and b c)

/-- SHA256RNDS2 xmm1, xmm2, <xmm0>: two rounds; `d` = xmm1 (C D G H), `s` = xmm2 (A B E F). -/
def rnds2 (d s k : List α) : List α :=
  let g (v : List α) (i : Nat) := v.getD i (Lane.const 0)
  let a0 := g s 3; let b0 := g s 2; let c0 := g d 3; let d0 := g d 2
  let e0 := g s 1; let f0 := g s 0; let g0 := g d 1; let h0 := g d 0
  let wk0 := g k 0; let wk1 := g k 1
  let t0 := Lane.add (Lane.add (Lane.add (chF e0 f0 g0) (bsig1 e0)) wk0) h0
  let a1 := Lane.add (Lane.add t0 (majF a0 b0 c0)) (bsig0 a0)
  let e1 := Lane.add t0 d0
  let b1 := a0; let c1 := b0; let f1 := e0; let g1 := f0
  let t1 := Lane.add (Lane.add (Lane.add (chF e1 f1 g1) (bsig1 e1)) wk1) g0
  let a2 := Lane.add (Lane.add t1 (majF a1 b1 c1)) (bsig0 a1)
  let e2 := Lane.add t1 c0
  [e1, e2, a1, a2]

/-- SHA256MSG1 xmm1, xmm2. -/
def msg1 (d s : List α) : List α :=
  let g (v : List α) (i : Nat) := v.getD i (Lane.const 0)
  let w4 := g s 0; let w3 := g d 3; let w2 := g d 2; let w1 := g d 1; let w0 := g d 0
  [Lane.add w0 (ssig0 w1), Lane.add w1 (ssig0 w2), Lane.add w2 (ssig0 w3), Lane.add w3 (ssig0 w4)]

/-- SHA256MSG2 xmm1, xmm2. -/
def msg2 (d s : List α) : List α :=
  let g (v : List α) (i : Nat) := v.getD i (Lane.const 0)
  let w14 := g s 2; let w15 := g s 3
  let w16 := Lane.add (g d 0) (ssig1 w14)
  let w17 := Lane.add (g d 1) (ssig1 w15)
  let w18 := Lane.add (g d 2) (ssig1 w16)
  let w19 := Lane.add (g d 3) (ssig1 w17)
  [w16, w17, w18, w19]

/-! ## General registers -/

/-- A 32-bit data operand (reg low lane, immediate, or memory dword). -/
def gData32 (ro : Region) (mem0 : Addr γ → Cell α γ) (s : State α γ) : GSrc → Except String α
  | .reg i => match s.getG i with
    | .num lo _ => pure lo
    | .ptr ⟨0, n⟩ => match Ctl.asInt n with
      | some v => pure (Lane.const (BitVec.ofInt 32 v))
      | none => throw "symbolic count as data"
    | .ptr _ => throw "pointer as data"
  | .imm v => pure (Lane.const (BitVec.ofInt 32 v))
  | .mem m => do loadLane mem0 s (← effAddr ro s m)

/-- A 64-bit control operand (pointer/count/constant). -/
def gCtl (s : State α γ) : GSrc → Except String (Addr γ)
  | .reg i => match s.getG i with
    | .ptr a => pure a
    | .num lo hi => match Lane.asConst lo, Lane.asConst hi with
      | some l, some h => pure ⟨rNum, Ctl.ofInt ((h.toNat * 2 ^ 32 + l.toNat : Nat) : Int)⟩
      | _, _ => throw "data as pointer/count"
  | .imm v => pure ⟨rNum, Ctl.ofInt v⟩
  | .mem _ => throw "memory control operand"

def ccCond (c : CC) (a b : γ) : Cond γ :=
  match c with
  | .e => .eq a b | .ne => .not (.eq a b)
  | .l => .lt a b | .ge => .not (.lt a b) | .le => .le a b | .g => .not (.le a b)
  | .b => .lt a b | .ae => .not (.lt a b) | .be => .le a b | .a => .not (.le a b)

def setData32 (s : State α γ) (d : Nat) (x : α) : State α γ := s.setG d (.num x (Lane.const 0))

/-- Flags: clobbered by a data operation / set to the comparison `(a, b)`. -/
def clearFlags (s : State α γ) : State α γ := { s with flags := none }
def setFlags (s : State α γ) (a b : γ) : State α γ := { s with flags := some (a, b) }
/-- Returned to the caller. -/
def halt (s : State α γ) : State α γ := { s with halted := true }

/-- The result of a step, or the failed state. -/
def okOr (s : State α γ) (r : Except String (State α γ)) : State α γ :=
  match r with
  | .ok s' => s'
  | .error e => s.fail e

/-- Effect of one instruction (`orc`: directions of undecided branches). -/
def exec (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr) (s : State α γ) : State α γ :=
  if s.halted then s else
  match i with
  | .nop => s.next
  | .vop op vex w d s1 s2 => okOr s do
    let b ← readVSrc ro mem0 s w s2
    let a := (s.getV s1).take w
    let r := lanes2 (lop op) a b
    pure (setVec s vex w d r).next
  | .vshift k vex w d src n => okOr s do
    pure (setVec s vex w d (((s.getV src).take w).map (fun x => shiftL k x n))).next
  | .vshiftq vex w d src n => okOr s do
    let r := unpairs ((pairs ((s.getV src).take w)).map (fun (lo, hi) => shrQ lo hi n))
    pure (setVec s vex w d r).next
  | .vror w d src n => okOr s do
    pure (setVec s true w d (((s.getV src).take w).map (fun x => Lane.ror x (n % 32)))).next
  | .vtern w d s1 s2 imm => okOr s do
    let a := (s.getV d).take w
    let b := (s.getV s1).take w
    let c := (s.getV s2).take w
    pure (setVec s true w d (lanes3 (Lane.tern imm) a b c)).next
  | .vload vex w d src => okOr s do
    let v ← readVSrc ro mem0 s w src
    pure (setVec s vex w d v).next
  | .vstore w m src => okOr s do
    let a ← effAddr ro s m
    pure (storeLanes s a ((s.getV src).take w)).next
  | .pshufd vex d src imm => okOr s do
    let v := s.getV src
    let r := (List.range 4).map (fun i => v.getD ((imm >>> (2 * i)) % 4) (Lane.const 0))
    pure (setVec s vex 4 d r).next
  | .pshufb vex w d src mask => okOr s do
    let r ← pshufbL ((s.getV src).take w) (s.getV mask) w
    pure (setVec s vex w d r).next
  | .palignr vex d s1 s2 imm => okOr s do
    pure (setVec s vex 4 d (palignrL (s.getV s1) (s.getV s2) imm)).next
  | .pblendw d src imm => okOr s do
    pure (setVec s false 4 d (pblendwL (s.getV d) (s.getV src) imm)).next
  | .shufps w d s1 s2 imm => okOr s do
    let a := s.getV s1; let b := s.getV s2
    let r := (List.range w).map (fun i =>
      let g := i / 4; let j := i % 4
      let sel := (imm >>> (2 * j)) % 4
      (if j < 2 then a else b).getD (4 * g + sel) (Lane.const 0))
    pure (setVec s true w d r).next
  | .perm2f128 d s1 s2 imm => okOr s do
    let a := s.getV s1; let b := s.getV s2
    let half (ctl : Nat) : List α :=
      if ctl.testBit 3 then zeroLanes 4
      else match ctl % 4 with
        | 0 => a.take 4 | 1 => (a.drop 4).take 4 | 2 => b.take 4 | _ => (b.drop 4).take 4
    pure (setVec s true 8 d (half imm ++ half (imm >>> 4))).next
  | .inserti128 d s1 m imm => okOr s do
    let x ← loadLanes mem0 s (← effAddr ro s m) 4
    let a := (s.getV s1).take 8
    let r := if imm % 2 = 0 then x ++ a.drop 4 else a.take 4 ++ x
    pure (setVec s true 8 d r).next
  | .inserti64x4 d s1 m imm => okOr s do
    let x ← loadLanes mem0 s (← effAddr ro s m) 8
    let a := s.getV s1
    let r := if imm % 2 = 0 then x ++ a.drop 8 else a.take 8 ++ x
    pure (setVec s true 16 d r).next
  | .permi2d d s1 s2 => okOr s do
    let idx ← ctlLanes (s.getV d) 16
    pure (setVec s true 16 d (permi2dP (s.getV s1) (s.getV s2) idx)).next
  | .permi2q d s1 s2 => okOr s do
    let idx ← ctlLanes (s.getV d) 16
    pure (setVec s true 16 d (permi2qP (s.getV s1) (s.getV s2) idx)).next
  | .sha256rnds2 d src => okOr s do
    pure (setVec s false 4 d (rnds2 (s.getV d) (s.getV src) (s.getV 0))).next
  | .sha256msg1 d src => okOr s do
    pure (setVec s false 4 d (msg1 (s.getV d) (s.getV src))).next
  | .sha256msg2 d src => okOr s do
    pure (setVec s false 4 d (msg2 (s.getV d) (s.getV src))).next
  | .mov w d src => okOr s do
    if w = 64 then
      match src with
      | .reg r => pure (s.setG d (s.getG r)).next
      | .imm v => pure (s.setG d (.ptr ⟨rNum, Ctl.ofInt v⟩)).next
      | .mem m => pure (s.setG d (← loadVal mem0 s (← effAddr ro s m))).next
    else pure (setData32 s d (← gData32 ro mem0 s src)).next
  | .movst w m src => okOr s do
    let a ← effAddr ro s m
    if w = 64 then pure (storeVal s a (s.getG src)).next
    else match s.getG src with
      | .num lo _ => pure (storeLane s a lo).next
      | _ => throw "32-bit store of a pointer"
  | .alu op w d src => okOr s do
    if w = 64 then
      -- the zeroing idiom `xor r, r` (a number 0); pointer/count arithmetic (`add rsi, 64`,
      -- `add rdx, rdi` with a number in rdx); `and` aligns a pointer (`and rsp, -32`)
      if op = .xor ∧ src = .reg d then
        pure (clearFlags (s.setG d (.ptr ⟨rNum, Ctl.ofInt 0⟩))).next
      else
      let a ← gCtl s (.reg d)
      let b ← gCtl s src
      match op with
      | .add =>
        if b.region = rNum ∨ a.region = rNum then
          let r : Addr γ := ⟨if b.region = rNum then a.region else b.region, Ctl.add a.off b.off⟩
          pure (setFlags (s.setG d (.ptr r)) r.off (Ctl.ofInt 0)).next
        else throw "pointer + pointer"
      | .and => match Ctl.asInt a.off, Ctl.asInt b.off with
        | some x, some y =>
          match andInt x y with
          | some r =>
            if b.region = rNum ∧ (a.region = rNum ∨ (-64 ≤ y ∧ y < 0)) then
              pure (clearFlags (s.setG d (.ptr ⟨a.region, Ctl.ofInt r⟩))).next
            else throw "and on pointer"
          | none => throw "and form"
        | _, _ => throw "and on symbolic pointer"
      | _ => throw "64-bit data operation"
    else
      -- 32-bit data; `xor r, r` is the zeroing idiom
      if op = .xor ∧ src = .reg d then pure (clearFlags (setData32 s d (Lane.const 0))).next
      else
        let a ← gData32 ro mem0 s (.reg d)
        let b ← gData32 ro mem0 s src
        pure (clearFlags (setData32 s d (lop op a b))).next
  | .sub w d src => okOr s do
    if w = 64 then
      let a ← gCtl s (.reg d)
      let b ← gCtl s src
      if b.region = rNum then
        let r : Addr γ := a.plus (Ctl.smul (-1) b.off)
        pure (setFlags (s.setG d (.ptr r)) a.off b.off).next
      else throw "pointer - pointer"
    else throw "32-bit sub"
  | .lea d m => okOr s do
    pure (s.setG d (.ptr (← effAddr ro s m))).next
  | .ror w d n => okOr s do
    if w = 32 then
      let a ← gData32 ro mem0 s (.reg d)
      pure (clearFlags (setData32 s d (Lane.ror a (n % 32)))).next
    else throw "64-bit ror"
  | .shld w d src n => okOr s do
    if w = 32 then
      let a ← gData32 ro mem0 s (.reg d)
      let b ← gData32 ro mem0 s (.reg src)
      let n := n % 32
      let r := if n = 0 then a else Lane.or (Lane.shl a n) (Lane.shr b (32 - n))
      pure (clearFlags (setData32 s d r)).next
    else throw "64-bit shld"
  | .shl w d n => okOr s do
    if w = 64 then
      let a ← gCtl s (.reg d)
      if a.region = rNum then
        pure (clearFlags (s.setG d (.ptr ⟨rNum, Ctl.smul (2 ^ (n % 64)) a.off⟩))).next
      else throw "shl of a pointer"
    else
      let a ← gData32 ro mem0 s (.reg d)
      pure (clearFlags (setData32 s d (shiftL .shl a (n % 32)))).next
  | .bswap w d => okOr s do
    if w = 32 then
      let a ← gData32 ro mem0 s (.reg d)
      pure (setData32 s d (ofBytes (byteOf a 3) (byteOf a 2) (byteOf a 1) (byteOf a 0))).next
    else throw "64-bit bswap"
  | .push r => okOr s do
    match s.getG rsp with
    | .ptr sp =>
      let sp' := sp.plusI (-8)
      pure ((storeVal s sp' (s.getG r)).setG rsp (.ptr sp')).next
    | _ => throw "rsp not a pointer"
  | .pop r => okOr s do
    match s.getG rsp with
    | .ptr sp =>
      let v ← loadVal mem0 s sp
      pure ((s.setG r v).setG rsp (.ptr (sp.plusI 8))).next
    | _ => throw "rsp not a pointer"
  | .cmp w a b => okOr s do
    if w = 64 then
      let x ← gCtl s (.reg a)
      let y ← gCtl s b
      if y.region = rNum ∨ y.region = x.region then pure (setFlags s x.off y.off).next
      else throw "cmp of unrelated pointers"
    else throw "32-bit cmp"
  | .test w a b => okOr s do
    if w = 64 ∧ a = b then
      let x ← gCtl s (.reg a)
      if x.region = rNum then pure (setFlags s x.off (Ctl.ofInt 0)).next
      else throw "test of a pointer"
    else throw "test form"
  | .jcc c t => okOr s do
    match s.flags with
    | some (a, b) => pure (s.branch orc (ccCond c a b) t)
    | none => throw "branch on clobbered flags"
  | .jmp t => { s with pc := t }
  | .jccTail c name => okOr s do
    match s.flags with
    | some (a, b) =>
      let s' := s.branch orc (ccCond c a b) 1000000000
      if s'.pc = 1000000000 then pure { s' with pc := s.pc, halted := true, tail := some name }
      else pure s'
    | none => throw "branch on clobbered flags"
  | .jmpTail name => { s with halted := true, tail := some name }
  | .ret => okOr s do
    match s.getG rsp with
    | .ptr sp =>
      match ← loadVal mem0 s sp with
      | .ptr ⟨5, _⟩ => pure (halt (s.setG rsp (.ptr (sp.plusI 8))))
      | _ => throw "ret to unknown address"
    | _ => throw "rsp not a pointer"

/-- Fetch-execute `n` steps. -/
def run (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    Nat → State α γ → State α γ
  | 0, s => s
  | n + 1, s =>
    if s.halted then s
    else match prog[s.pc]? with
      | some i => run prog ro mem0 orc n (exec ro mem0 orc i s)
      | none => s.fail "pc out of program"

end

end Hashtree.Asm.X86
