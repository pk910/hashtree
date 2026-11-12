import Hashtree.Asm.Core

/-!
# AArch64: the instructions the hashtree kernels use

Semantics follow the Arm Architecture Reference Manual for A-profile (DDI 0487, the
`Operation` pseudocode of each instruction) for exactly the operand forms the shipped objects
contain (`sha256_armv8_crypto.o`, `sha256_armv8_neon_x1.o`, `sha256_armv8_neon_x4.o`, Linux ELF
and macOS Mach-O; `tools/arm_to_lean.py` rejects every other form):

* general registers: `mov xd, #imm` (MOVZ/MOVN), `add/sub xd|sp, xn|sp, #imm`,
  `add xd, xn, xm, lsl #k`, `adrp xd, sym` + `add xd, xn, :lo12:sym` (relocated to `.rodata` /
  `__const`), `add/eor/and/orr/bic wd, wn, wm`, `ror wd, wn, #k`, `rev32 xd, xn`,
  `cmp xn, xm`, `cmp xn, #imm`, `b.cond`, `b` (inside the function, or to another symbol = tail
  call), `ret`;
* loads/stores: `ldr/str` of `w`, `q` (unsigned offset), `ldp/stp` of `w`, `x`, `d`, `q`
  (signed offset, post-index), `ld1/st1 {vt.4s … }` (multiple structures, one to four
  registers, offset or post-index immediate), `ld4/st4 {vt.s … vt+3.s}[i]` (single structure,
  post-index register or immediate);
* vector: `add .4s`, `eor/orr/and/bic .16b` (`mov vd.16b, vn.16b` is `orr vd, vn, vn`),
  `movi .4s`, `shl/ushr .4s` and `.2d`, `ext .16b`, `zip1/zip2/uzp1 .4s`, `xtn .2s, .2d`,
  `rev32 .16b`, `sha256h`, `sha256h2`, `sha256su0`, `sha256su1`.

## Registers
General registers: `gpr` index `i` is `xi` for `i ≤ 30`; index **31 is SP** (the stack pointer).
The zero register (`xzr`/`wzr`, also encoded as 31) is not used by the kernels: every form that
would read or write it as register 31 is an error here. A register holds data (`num lo hi`, two
32-bit lanes) or a pointer/count (`ptr`); writes of a `w` register zero the upper half
(`X[d] = ZeroExtend(result)`).

Vector registers: `vr` index `i` is `vi` (`i < 32`), lanes 0..3 = the 128-bit register
(lane 0 = bits 31:0). A write of a 64-bit (`d`, `.2s`) result zeroes bits 127:64; every write
zeroes the padding lanes 4..15 (AArch64 `V[n] = value` zero-extends to the register size).

## Memory, flags, branches
Effective addresses are `base + offset` on `Addr`; a base register must hold a pointer. A load or
store with base SP checks SP alignment first (`CheckSPAlignment`: SP<3:0> must be 0; Linux and
macOS enable the check for EL0): a misaligned SP is a fault (error state).

Flags (NZCV) are written only by `cmp` (SUBS to the zero register) and only for comparisons of
two control values of one region (two pointers of one buffer, or two numbers); they are kept as
the pair `(a, b)` and every condition is evaluated as a comparison of mathematical integers:
`lo`/`hs`/`hi`/`ls` (unsigned) as `<`, `≥`, `>`, `≤` — valid because counts and pointers never
wrap (precondition shared with the x86 model). No other modelled instruction touches NZCV.
-/

namespace Hashtree.Asm.Arm
open Hashtree.Asm

/-- Addressing modes: `[xn, #imm]`, `[xn, #imm]!`, `[xn], #imm`, `[xn], xm`. -/
inductive Idx where
  | off (imm : Int)
  | pre (imm : Int)
  | post (imm : Int)
  | postR (m : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Register sizes of loads/stores: 32/64-bit general (`w`/`x`), 64/128-bit SIMD&FP (`d`/`q`). -/
inductive Sz where
  | w | x | d | q
  deriving DecidableEq, Repr, Inhabited

def Sz.bytes : Sz → Nat
  | .w => 4 | .x => 8 | .d => 8 | .q => 16

/-- Vector lane-wise operations: `add` on `.4s`; the bitwise ones on `.16b` (= on 32-bit lanes). -/
inductive VOp where
  | add | eor | orr | and | bic
  deriving DecidableEq, Repr, Inhabited

/-- 32-bit general data operations (register forms, no shift). -/
inductive WOp where
  | add | eor | and | orr | bic
  deriving DecidableEq, Repr, Inhabited

/-- Branch conditions. -/
inductive CC where
  | eq | ne | hs | lo | hi | ls | ge | lt | gt | le
  deriving DecidableEq, Repr, Inhabited

inductive Instr where
  | nop
  -- general registers
  | movz (d : Nat) (imm : Int)                -- mov xd, #imm (MOVZ/MOVN alias)
  | addi (d n : Nat) (imm : Nat)              -- add xd|sp, xn|sp, #imm
  | subi (d n : Nat) (imm : Nat)              -- sub xd|sp, xn|sp, #imm
  | addr (d n m : Nat) (sh : Nat)             -- add xd, xn, xm, lsl #sh
  | adrp (d : Nat) (off : Int)                -- adrp xd, rodata+off      (ADR_PREL_PG_HI21 / PAGE21)
  | addLo12 (d n : Nat) (off : Int)           -- add xd, xn, :lo12:rodata+off (ADD_ABS_LO12_NC / PAGEOFF12)
  | wop (op : WOp) (d n m : Nat)              -- op wd, wn, wm
  | rorw (d n : Nat) (k : Nat)                -- ror wd, wn, #k (EXTR alias)
  | rev32x (d n : Nat)                        -- rev32 xd, xn
  | cmpr (n m : Nat)                          -- cmp xn, xm
  | cmpi (n : Nat) (imm : Nat)                -- cmp xn|sp, #imm
  | bcc (c : CC) (t : Nat)
  | b (t : Nat)
  | bTail (name : String)
  | ret
  -- loads / stores
  | ldr (sz : Sz) (t n : Nat) (i : Idx)
  | str (sz : Sz) (t n : Nat) (i : Idx)
  | ldp (sz : Sz) (t1 t2 n : Nat) (i : Idx)
  | stp (sz : Sz) (t1 t2 n : Nat) (i : Idx)
  | ld1 (t k n : Nat) (i : Idx)               -- ld1 {vt.4s .. vt+k-1.4s}, [xn] ...
  | st1 (t k n : Nat) (i : Idx)
  | ld4s (t e n : Nat) (i : Idx)              -- ld4 {vt.s .. vt+3.s}[e], [xn] ...
  | st4s (t e n : Nat) (i : Idx)
  -- vector
  | vop (op : VOp) (d n m : Nat)
  | movi (d : Nat) (imm : Nat)                -- movi vd.4s, #imm8, lsl #s (imm = imm8 << s)
  | shl (esz d n k : Nat)                     -- shl vd.4s|2d, vn, #k   (esz = 32 | 64)
  | ushr (esz d n k : Nat)                    -- ushr vd.4s|2d, vn, #k
  | ext (d n m imm : Nat)                     -- ext vd.16b, vn.16b, vm.16b, #imm
  | zip1 (d n m : Nat)                        -- .4s
  | zip2 (d n m : Nat)
  | uzp1 (d n m : Nat)
  | xtn (d n : Nat)                           -- xtn vd.2s, vn.2d
  | rev32 (d n : Nat)                         -- rev32 vd.16b, vn.16b
  | sha256h (d n m : Nat)                     -- sha256h qd, qn, vm.4s
  | sha256h2 (d n m : Nat)
  | sha256su0 (d n : Nat)
  | sha256su1 (d n m : Nat)
  deriving DecidableEq, Repr, Inhabited

/-! ## Helpers -/

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

/-- gpr index of SP. -/
def sp : Nat := 31

def zeroLanes (n : Nat) : List α := List.replicate n (Lane.const 0)
def lane (v : List α) (i : Nat) : α := v.getD i (Lane.const 0)

/-- The 128-bit register `vi` as four lanes. -/
def getQ (s : State α γ) (i : Nat) : List α :=
  let v := s.getV i
  [lane v 0, lane v 1, lane v 2, lane v 3]

/-- The low 64 bits (`di`). -/
def getD (s : State α γ) (i : Nat) : List α :=
  let v := s.getV i
  [lane v 0, lane v 1]

/-- `V[d] = v` for a 128-bit value (upper padding lanes zero). -/
def setQ (s : State α γ) (d : Nat) (v : List α) : State α γ :=
  s.setV d ([lane v 0, lane v 1, lane v 2, lane v 3] ++ zeroLanes 12)

/-- `V[d] = v` for a 64-bit value: bits 127:64 become zero. -/
def setD (s : State α γ) (d : Nat) (v : List α) : State α γ :=
  s.setV d ([lane v 0, lane v 1] ++ zeroLanes 14)

/-- `X[d] = ZeroExtend(x)` for a 32-bit result. -/
def setW (s : State α γ) (d : Nat) (x : α) : State α γ := s.setG d (.num x (Lane.const 0))

/-- A 32-bit data operand (`wi`). -/
def getW (s : State α γ) (i : Nat) : Except String α :=
  if i = sp then throw "register 31 as w register" else
  match s.getG i with
  | .num lo _ => pure lo
  | .ptr ⟨0, n⟩ => match Ctl.asInt n with
    | some v => pure (Lane.const (BitVec.ofInt 32 v))
    | none => throw "symbolic count as data"
  | .ptr _ => throw "pointer as data"

/-- A 64-bit data operand as (lo, hi). -/
def getX (s : State α γ) (i : Nat) : Except String (α × α) :=
  if i = sp then throw "register 31 as x data register" else
  match s.getG i with
  | .num lo hi => pure (lo, hi)
  | .ptr ⟨0, n⟩ => match Ctl.asInt n with
    | some v => pure (Lane.const (BitVec.ofInt 32 v), Lane.const (BitVec.ofInt 32 (v / 2 ^ 32)))
    | none => throw "symbolic count as data"
  | .ptr _ => throw "pointer as data"

/-- A 64-bit control operand (pointer/count; constant data counts as a number). -/
def getC (s : State α γ) (i : Nat) : Except String (Addr γ) :=
  match s.getG i with
  | .ptr a => pure a
  | .num lo hi => match Lane.asConst lo, Lane.asConst hi with
    | some l, some h => pure ⟨rNum, Ctl.ofInt ((h.toNat * 2 ^ 32 + l.toNat : Nat) : Int)⟩
    | _, _ => throw "data as pointer/count"

/-- The base register of an address (`CheckSPAlignment` when it is SP). -/
def baseAddr (s : State α γ) (n : Nat) : Except String (Addr γ) :=
  match s.getG n with
  | .ptr a =>
    if a.region = rNum then throw "number as address"
    else if n = sp then
      match Ctl.asInt a.off with
      | some o => if o % 16 = 0 then pure a else throw "SP alignment fault"
      | none => throw "SP alignment undetermined"
    else pure a
  | .num _ _ => throw "data register as address"

/-- Access address and the written-back base (if any). -/
def addrWB (s : State α γ) (n : Nat) (i : Idx) : Except String (Addr γ × Option (Addr γ)) :=
  match baseAddr s n with
  | .error e => .error e
  | .ok b =>
    match i with
    | .off k => .ok (b.plusI k, none)
    | .pre k => .ok (b.plusI k, some (b.plusI k))
    | .post k => .ok (b, some (b.plusI k))
    | .postR m =>
      if m = sp then .error "post-index by register 31" else
      match getC s m with
      | .error e => .error e
      | .ok x => if x.region = rNum then .ok (b, some (b.plus x.off)) else .error "post-index by a pointer"

def writeBack (s : State α γ) (n : Nat) : Option (Addr γ) → State α γ
  | none => s
  | some a => s.setG n (.ptr a)

def Idx.wb : Idx → Bool
  | .off _ => false
  | _ => true

/-- Byte `j` (0..15) of a 128-bit lane list. -/
def vbyte (v : List α) (j : Nat) : α := byteOf (lane v (j / 4)) (j % 4)

/-- A lane from four bytes (each in [0,256)), byte 0 least significant. -/
def ofBytes (b0 b1 b2 b3 : α) : α :=
  Lane.or (Lane.or b0 (Lane.shl b1 8)) (Lane.or (Lane.shl b2 16) (Lane.shl b3 24))

/-- Reverse the bytes of a 32-bit lane. -/
def bswap (x : α) : α := ofBytes (byteOf x 3) (byteOf x 2) (byteOf x 1) (byteOf x 0)

def vop : VOp → α → α → α
  | .add => Lane.add
  | .eor => Lane.xor
  | .orr => Lane.or
  | .and => Lane.and
  | .bic => fun a b => Lane.and a (Lane.not b)

def wop : WOp → α → α → α
  | .add => Lane.add
  | .eor => Lane.xor
  | .and => Lane.and
  | .orr => Lane.or
  | .bic => fun a b => Lane.and a (Lane.not b)

/-- 32-bit shifts (`shl` 0..31, `ushr` 1..32: a shift by 32 gives 0). -/
def shl32 (x : α) (k : Nat) : α := if k < 32 then Lane.shl x k else Lane.const 0
def shr32 (x : α) (k : Nat) : α := if k < 32 then Lane.shr x k else Lane.const 0

/-- 64-bit element (lo, hi) shifted left / logically right. -/
def shl64 (lo hi : α) (k : Nat) : α × α :=
  if k = 0 then (lo, hi)
  else if k < 32 then (Lane.shl lo k, Lane.or (Lane.shl hi k) (Lane.shr lo (32 - k)))
  else if k < 64 then (Lane.const 0, shl32 lo (k - 32))
  else (Lane.const 0, Lane.const 0)

def shr64 (lo hi : α) (k : Nat) : α × α :=
  if k = 0 then (lo, hi)
  else if k < 32 then (Lane.or (Lane.shr lo k) (Lane.shl hi (32 - k)), Lane.shr hi k)
  else if k < 64 then (shr32 hi (k - 32), Lane.const 0)
  else (Lane.const 0, Lane.const 0)

/-- `EXT`: bytes `imm ..` of `Vm:Vn` (Vn the low half). -/
def extL (n m : List α) (imm : Nat) : List α :=
  let cat (j : Nat) : α := if j < 16 then vbyte n j else if j < 32 then vbyte m (j - 16) else Lane.const 0
  if imm % 4 = 0 then
    (List.range 4).map fun i => let j := i + imm / 4
      if j < 4 then lane n j else lane m (j - 4)
  else
    (List.range 4).map fun i =>
      ofBytes (cat (4 * i + imm)) (cat (4 * i + 1 + imm)) (cat (4 * i + 2 + imm)) (cat (4 * i + 3 + imm))

/-! ## SHA-256 (Arm ARM: SHA256H, SHA256H2, SHA256SU0, SHA256SU1 and the shared functions
`SHA256hash`, `SHAchoose`, `SHAmajority`, `SHAhashSIGMA0/1`) -/

def shaChoose (x y z : α) : α := Lane.xor (Lane.and (Lane.xor y z) x) z
def shaMajority (x y z : α) : α := Lane.or (Lane.and x y) (Lane.and (Lane.or x y) z)
def shaSigma0 (x : α) : α := Lane.xor (Lane.xor (Lane.ror x 2) (Lane.ror x 13)) (Lane.ror x 22)
def shaSigma1 (x : α) : α := Lane.xor (Lane.xor (Lane.ror x 6) (Lane.ror x 11)) (Lane.ror x 25)

/-- One iteration of the `SHA256hash` loop: `X = [a,b,c,d]`, `Y = [e,f,g,h]`, word `w`;
then `<Y, X> = ROL(Y : X, 32)`. -/
def shaStep (xy : List α × List α) (w : α) : List α × List α :=
  let x := xy.1
  let y := xy.2
  let chs := shaChoose (lane y 0) (lane y 1) (lane y 2)
  let maj := shaMajority (lane x 0) (lane x 1) (lane x 2)
  let t := Lane.add (Lane.add (Lane.add (lane y 3) (shaSigma1 (lane y 0))) chs) w
  let x3 := Lane.add t (lane x 3)
  let y3 := Lane.add (Lane.add t (shaSigma0 (lane x 0))) maj
  ([y3, lane x 0, lane x 1, lane x 2], [x3, lane y 0, lane y 1, lane y 2])

def sha256hash (x y w : List α) (part1 : Bool) : List α :=
  let r := [lane w 0, lane w 1, lane w 2, lane w 3].foldl shaStep (x, y)
  if part1 then r.1 else r.2

def ssig0 (x : α) : α := Lane.xor (Lane.xor (Lane.ror x 7) (Lane.ror x 18)) (Lane.shr x 3)
def ssig1 (x : α) : α := Lane.xor (Lane.xor (Lane.ror x 17) (Lane.ror x 19)) (Lane.shr x 10)

/-- `SHA256SU0`: `T = operand2<31:0> : operand1<127:32>`; `result[e] = σ0(T[e]) + operand1[e]`. -/
def su0 (d n : List α) : List α :=
  let t := [lane d 1, lane d 2, lane d 3, lane n 0]
  (List.range 4).map fun e => Lane.add (ssig0 (lane t e)) (lane d e)

/-- `SHA256SU1`: `T0 = operand3<31:0> : operand2<127:32>`, `T1 = operand3<127:64>`; elements 2, 3
use the first two results. -/
def su1 (d n m : List α) : List α :=
  let t0 := [lane n 1, lane n 2, lane n 3, lane m 0]
  let r0 := Lane.add (Lane.add (ssig1 (lane m 2)) (lane d 0)) (lane t0 0)
  let r1 := Lane.add (Lane.add (ssig1 (lane m 3)) (lane d 1)) (lane t0 1)
  let r2 := Lane.add (Lane.add (ssig1 r0) (lane d 2)) (lane t0 2)
  let r3 := Lane.add (Lane.add (ssig1 r1) (lane d 3)) (lane t0 3)
  [r0, r1, r2, r3]

/-! ## Loads and stores -/

/-- Load one register of size `sz` at `a`. -/
def loadReg (mem0 : Addr γ → Cell α γ) (s0 s : State α γ) (sz : Sz) (t : Nat) (a : Addr γ) :
    Except String (State α γ) :=
  match sz with
  | .w => if t = sp then throw "register 31 as load target" else do
    let x ← loadLane mem0 s0 a
    pure (setW s t x)
  | .x => if t = sp then throw "register 31 as load target" else do
    let v ← loadVal mem0 s0 a
    pure (s.setG t v)
  | .d => do
    let v ← loadLanes mem0 s0 a 2
    pure (setD s t v)
  | .q => do
    let v ← loadLanes mem0 s0 a 4
    pure (setQ s t v)

/-- Store register `t` (read in `s0`) of size `sz` at `a`. -/
def storeReg (s0 s : State α γ) (sz : Sz) (t : Nat) (a : Addr γ) : Except String (State α γ) :=
  match sz with
  | .w => do
    let x ← getW s0 t
    pure (storeLane s a x)
  | .x => if t = sp then throw "register 31 as store source" else pure (storeVal s a (s0.getG t))
  | .d => pure (storeLanes s a (getD s0 t))
  | .q => pure (storeLanes s a (getQ s0 t))

/-- One register of `ld1` (`j`-th of the list; reads in `s`). -/
def ld1Step (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) (t : Nat) (st : State α γ) (j : Nat) :
    Except String (State α γ) := do
  let v ← loadLanes mem0 s (a.plusI (16 * (j : Int))) 4
  pure (setQ st ((t + j) % 32) v)

/-- One register of `st1` (register values read in `s`). -/
def st1Step (s : State α γ) (a : Addr γ) (t : Nat) (st : State α γ) (j : Nat) : State α γ :=
  storeLanes st (a.plusI (16 * (j : Int))) (getQ s ((t + j) % 32))

/-- One element of `ld4` (single structure, lane `e`; memory read in `s`). -/
def ld4Step (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) (t e : Nat) (st : State α γ) (r : Nat) :
    Except String (State α γ) := do
  let x ← loadLane mem0 s (a.plusI (4 * (r : Int)))
  let v := getQ st ((t + r) % 32)
  pure (setQ st ((t + r) % 32) (v.set e x))

/-- One element of `st4` (single structure, lane `e`; register values read in `s`). -/
def st4Step (s : State α γ) (a : Addr γ) (t e : Nat) (st : State α γ) (r : Nat) : State α γ :=
  storeLane st (a.plusI (4 * (r : Int))) (lane (getQ s ((t + r) % 32)) e)

def isGpr : Sz → Bool
  | .w => true | .x => true | _ => false

/-- Condition of `b.cond` on the last comparison `a - b`. -/
def ccCond (c : CC) (a b : γ) : Cond γ :=
  match c with
  | .eq => .eq a b | .ne => .not (.eq a b)
  | .lo => .lt a b | .hs => .not (.lt a b) | .ls => .le a b | .hi => .not (.le a b)
  | .lt => .lt a b | .ge => .not (.lt a b) | .le => .le a b | .gt => .not (.le a b)

/-- Flags: set to the comparison `(a, b)` (only `cmp` writes NZCV). -/
def setFlags (s : State α γ) (a b : γ) : State α γ := { s with flags := some (a, b) }
/-- Returned to the caller. -/
def halt (s : State α γ) : State α γ := { s with halted := true }

/-- The result of a step, or the failed state. -/
def okOr (s : State α γ) (r : Except String (State α γ)) : State α γ :=
  match r with
  | .ok s' => s'
  | .error e => s.fail e

/-- Effect of one instruction (`ro`: region of this program's read-only data; `orc`: directions
of undecided branches). -/
def exec (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr) (s : State α γ) :
    State α γ :=
  if s.halted then s else
  match i with
  | .nop => s.next
  -- general registers
  | .movz d imm => okOr s do
    if d = sp then throw "register 31 as mov target" else
    pure (s.setG d (.ptr ⟨rNum, Ctl.ofInt imm⟩)).next
  | .addi d n imm => okOr s do
    let a ← getC s n
    pure (s.setG d (.ptr (a.plusI imm))).next
  | .subi d n imm => okOr s do
    let a ← getC s n
    pure (s.setG d (.ptr (a.plusI (-(imm : Int))))).next
  | .addr d n m sh => okOr s do
    if d = sp ∨ n = sp ∨ m = sp then throw "register 31 (zr) in add (shifted register)" else
    let a ← getC s n
    let b ← getC s m
    if b.region = rNum then pure (s.setG d (.ptr (a.plus (Ctl.smul (2 ^ sh) b.off)))).next
    else if a.region = rNum ∧ sh = 0 then pure (s.setG d (.ptr (b.plus a.off))).next
    else throw "pointer + pointer"
  | .adrp d off => okOr s do
    if d = sp then throw "register 31 as adrp target" else
    -- the region base is taken page aligned for the relocated pair: adrp gives the page of
    -- `rodata + off`, the following `add :lo12:` adds the rest (sum = rodata + off exactly)
    pure (s.setG d (.ptr ⟨ro, Ctl.ofInt (off - off % 4096)⟩)).next
  | .addLo12 d n off => okOr s do
    let a ← getC s n
    pure (s.setG d (.ptr (a.plusI (off % 4096)))).next
  | .wop op d n m => okOr s do
    if d = sp then throw "register 31 as w target" else
    let a ← getW s n
    let b ← getW s m
    pure (setW s d (wop op a b)).next
  | .rorw d n k => okOr s do
    if d = sp then throw "register 31 as w target" else
    let a ← getW s n
    pure (setW s d (Lane.ror a (k % 32))).next
  | .rev32x d n => okOr s do
    if d = sp then throw "register 31 as x target" else
    let p ← getX s n
    pure (s.setG d (.num (bswap p.1) (bswap p.2))).next
  | .cmpr n m => okOr s do
    if n = sp ∨ m = sp then throw "register 31 (zr) in cmp (shifted register)" else
    let a ← getC s n
    let b ← getC s m
    if a.region = b.region then pure (setFlags s a.off b.off).next
    else throw "cmp of unrelated values"
  | .cmpi n imm => okOr s do
    let a ← getC s n
    if a.region = rNum then pure (setFlags s a.off (Ctl.ofInt imm)).next
    else throw "cmp of a pointer with a number"
  | .bcc c t => okOr s do
    match s.flags with
    | some (a, b) => pure (s.branch orc (ccCond c a b) t)
    | none => throw "branch on undefined flags"
  | .b t => { s with pc := t }
  | .bTail name => { s with halted := true, tail := some name }
  | .ret => okOr s do
    match s.getG 30 with
    | .ptr ⟨5, _⟩ => pure (halt s)
    | _ => throw "ret to unknown address"
  -- loads / stores
  | .ldr sz t n idx => okOr s do
    if isGpr sz ∧ idx.wb ∧ t = n then throw "load with writeback to its base" else
    let aw ← addrWB s n idx
    let s' ← loadReg mem0 s (writeBack s n aw.2) sz t aw.1
    pure s'.next
  | .str sz t n idx => okOr s do
    if isGpr sz ∧ idx.wb ∧ t = n then throw "store with writeback of its base" else
    let aw ← addrWB s n idx
    let s' ← storeReg s (writeBack s n aw.2) sz t aw.1
    pure s'.next
  | .ldp sz t1 t2 n idx => okOr s do
    if t1 = t2 then throw "ldp to one register twice" else
    if isGpr sz ∧ idx.wb ∧ (t1 = n ∨ t2 = n) then throw "load with writeback to its base" else
    let aw ← addrWB s n idx
    let s1 ← loadReg mem0 s (writeBack s n aw.2) sz t1 aw.1
    let s2 ← loadReg mem0 s s1 sz t2 (aw.1.plusI sz.bytes)
    pure s2.next
  | .stp sz t1 t2 n idx => okOr s do
    if isGpr sz ∧ idx.wb ∧ (t1 = n ∨ t2 = n) then throw "store with writeback of its base" else
    let aw ← addrWB s n idx
    let s1 ← storeReg s (writeBack s n aw.2) sz t1 aw.1
    let s2 ← storeReg s s1 sz t2 (aw.1.plusI sz.bytes)
    pure s2.next
  | .ld1 t k n idx => okOr s do
    let aw ← addrWB s n idx
    let s' ← (List.range k).foldlM (ld1Step mem0 s aw.1 t) (writeBack s n aw.2)
    pure s'.next
  | .st1 t k n idx => okOr s do
    let aw ← addrWB s n idx
    let s' := (List.range k).foldl (st1Step s aw.1 t) (writeBack s n aw.2)
    pure s'.next
  | .ld4s t e n idx => okOr s do
    if e ≥ 4 then throw "lane index" else
    let aw ← addrWB s n idx
    let s' ← (List.range 4).foldlM (ld4Step mem0 s aw.1 t e) (writeBack s n aw.2)
    pure s'.next
  | .st4s t e n idx => okOr s do
    if e ≥ 4 then throw "lane index" else
    let aw ← addrWB s n idx
    let s' := (List.range 4).foldl (st4Step s aw.1 t e) (writeBack s n aw.2)
    pure s'.next
  -- vector
  | .vop op d n m =>
    (setQ s d (List.zipWith (vop op) (getQ s n) (getQ s m))).next
  | .movi d imm =>
    let c : α := Lane.const (BitVec.ofNat 32 imm)
    (setQ s d [c, c, c, c]).next
  | .shl esz d n k => okOr s do
    let v := getQ s n
    if esz = 32 then pure (setQ s d (v.map (shl32 · k))).next
    else if esz = 64 then
      let p := shl64 (lane v 0) (lane v 1) k
      let q := shl64 (lane v 2) (lane v 3) k
      pure (setQ s d [p.1, p.2, q.1, q.2]).next
    else throw "shl element size"
  | .ushr esz d n k => okOr s do
    let v := getQ s n
    if esz = 32 then pure (setQ s d (v.map (shr32 · k))).next
    else if esz = 64 then
      let p := shr64 (lane v 0) (lane v 1) k
      let q := shr64 (lane v 2) (lane v 3) k
      pure (setQ s d [p.1, p.2, q.1, q.2]).next
    else throw "ushr element size"
  | .ext d n m imm => okOr s do
    if imm ≥ 16 then throw "ext index" else
    pure (setQ s d (extL (getQ s n) (getQ s m) imm)).next
  | .zip1 d n m =>
    let a := getQ s n; let b := getQ s m
    (setQ s d [lane a 0, lane b 0, lane a 1, lane b 1]).next
  | .zip2 d n m =>
    let a := getQ s n; let b := getQ s m
    (setQ s d [lane a 2, lane b 2, lane a 3, lane b 3]).next
  | .uzp1 d n m =>
    let a := getQ s n; let b := getQ s m
    (setQ s d [lane a 0, lane a 2, lane b 0, lane b 2]).next
  | .xtn d n =>
    let a := getQ s n
    (setD s d [lane a 0, lane a 2]).next
  | .rev32 d n =>
    (setQ s d ((getQ s n).map bswap)).next
  | .sha256h d n m =>
    (setQ s d (sha256hash (getQ s d) (getQ s n) (getQ s m) true)).next
  | .sha256h2 d n m =>
    (setQ s d (sha256hash (getQ s n) (getQ s d) (getQ s m) false)).next
  | .sha256su0 d n =>
    (setQ s d (su0 (getQ s d) (getQ s n))).next
  | .sha256su1 d n m =>
    (setQ s d (su1 (getQ s d) (getQ s n) (getQ s m))).next

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

end Hashtree.Asm.Arm
