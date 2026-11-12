import Hashtree.Asm.Core

/-!
# RV64: the instructions the hashtree RISC-V objects use

Semantics follow the RISC-V Unprivileged ISA (20240411) for RV64I, the C extension (every
compressed instruction is defined as its expansion into a base instruction, chapter "C"
§ 27.1), Zbb/Zbkb (`roriw`, `rev8`) and Zknh (`sha256sum0/1`, `sha256sig0/1`, Scalar
Cryptography v1.0.1 § 3.x: on RV64 they read `rs1[31:0]` and write the 32-bit result
sign-extended).  The translator (`tools/riscv_to_lean.py`) maps each disassembled instruction
of the SHIPPED object (`objdump -d -r -M no-aliases`) to exactly one `Instr`; it never
interprets a sequence.  Forms the objects do not contain are not modelled.

## Registers
`x0 … x31` are `gpr` indices 0 … 31.  `x0` reads as zero; writes to it are dropped.  A register
holds data (`Val.num lo hi`: the 64-bit value `hi·2³² + lo`) or a pointer/count (`Val.ptr`).
Every 64-bit operation on data is computed exactly on the lane pair:
* `*W` operations (`addw`, `slliw`, `srliw`, `sraiw`, `roriw`) and the Zknh instructions
  compute a 32-bit result `r` from the low lane and write `num r (sar r 31)` (sign extension,
  ISA § 4.2.1 "32-bit operations sign-extend their results");
* `lwu` writes `num w 0` (zero extension), `lui` writes `num v (sar v 31)`;
* `and`/`or`/`xor` act on both lanes; `srai`/`slli` are 64-bit shifts across the pair; `rev8`
  reverses all eight bytes (`lo' = bswap hi`, `hi' = bswap lo`); `add`/`addi` on data
  propagate the carry out of the low lane.
A constant count is accepted where data is expected (and vice versa); a symbolic count or a
pointer used as data is an error, as is a non-constant datum used as an address or compared.
Counts are integers (`Ctl`): `slli` multiplies a count by `2 ^ n`; a concrete result outside the
signed 64-bit range is an error ("count overflow"), and for a symbolic count the range is
recorded in `assume` (`noWrap`), like the direction of an undecided branch, so that theorems
about symbolic runs (`RiscvRunHom.run_hom`) carry it as a hypothesis.

## Code, relocations, calls
Branch and jump targets inside the function are instruction indices.  A link register written
by `jal`/`jalr` holds `ptr ⟨code, index⟩`.  An `auipc` carrying a `%pcrel_hi`/`%got_pcrel_hi`
relocation yields the full link-time address (`Target`) and its `%pcrel_lo` partner has
immediate 0 (the translator checks the partner and that the `auipc` result is dead after it), so
`hi + lo` is the address the linker produces.  A GOT entry is eight bytes in the program's GOT
region holding a pointer to the symbol.  A jump to a named function symbol (`jalr x0`) is a tail
call (`tail = some name`); a call (`jalr ra`) stops with `tail = some ("call:" ++ name)` and
`pc` at the return point, for the harness to model the callee.  A return (`jalr x0, 0(ra)`)
to a pointer in region `rRet` halts normally.
-/

namespace Hashtree.Asm.Riscv
open Hashtree.Asm

/-- ISA extensions (for the per-instruction ISA tag). -/
inductive Ext where
  | rv64i | c | zbb | zbkb | zknh
  deriving DecidableEq, Repr, Inhabited

/-- A link-time address named by a relocation. -/
inductive Target where
  /-- this program's `.rodata` + offset -/
  | ro (off : Int)
  /-- this program's GOT entry number `slot` (8 bytes each) -/
  | got (slot : Nat)
  /-- a named symbol (function or data object) + offset -/
  | sym (name : String) (off : Int)
  deriving DecidableEq, Repr, Inhabited

inductive BOp where
  | and | or | xor
  deriving DecidableEq, Repr, Inhabited

/-- 32-bit operations with a shift amount. -/
inductive WOp where
  | slliw | srliw | sraiw | roriw
  deriving DecidableEq, Repr, Inhabited

/-- Zknh SHA-256 functions. -/
inductive ShaOp where
  | sum0 | sum1 | sig0 | sig1
  deriving DecidableEq, Repr, Inhabited

/-- Branch conditions. -/
inductive BC where
  | eq | ne
  deriving DecidableEq, Repr, Inhabited

inductive Instr where
  /-- `addi x0, x0, 0` -/
  | nop
  /-- `c.unimp` / any illegal encoding: traps -/
  | unimp
  /-- `lui rd, imm20` (`imm20` = the instruction's 20-bit field) -/
  | lui (d : Nat) (imm20 : Nat)
  /-- `auipc rd, %…_hi(t)` (with its `%pcrel_lo` partner of immediate 0) -/
  | auipc (d : Nat) (t : Target)
  | addi (d s : Nat) (imm : Int)
  | add (d a b : Nat)
  | bop (op : BOp) (d a b : Nat)
  /-- `andi`/`ori`/`xori` (sign-extended 12-bit immediate) -/
  | bopi (op : BOp) (d a : Nat) (imm : Int)
  | slli (d s n : Nat)
  | srai (d s n : Nat)
  | wop (op : WOp) (d s n : Nat)
  | addw (d a b : Nat)
  | rev8 (d s : Nat)
  | sha (op : ShaOp) (d s : Nat)
  | lwu (d b : Nat) (off : Int)
  | ld (d b : Nat) (off : Int)
  | sw (src b : Nat) (off : Int)
  | sd (src b : Nat) (off : Int)
  /-- `beq`/`bne rs1, rs2, target` (target = instruction index) -/
  | br (c : BC) (a b : Nat) (t : Nat)
  /-- `jal rd, target` inside the function -/
  | jal (d : Nat) (t : Nat)
  | jalr (d s : Nat) (off : Int)
  deriving DecidableEq, Repr, Inhabited

/-- The extensions any one of which makes the (uncompressed) instruction legal. -/
def Instr.isa : Instr → List Ext
  | .wop .roriw .. => [.zbb, .zbkb]
  | .rev8 .. => [.zbb, .zbkb]
  | .sha .. => [.zknh]
  | .unimp => []
  | _ => [.rv64i]

/-- Static description of the program being executed. -/
structure Env where
  /-- region of this program's `.rodata` -/
  ro : Region
  /-- region of this program's GOT -/
  got : Region
  /-- region of code addresses (instruction indices) of this program -/
  code : Region
  /-- regions of named symbols (functions, data objects) -/
  syms : List (String × Region)
  deriving Inhabited

def Env.nameOf (e : Env) (r : Region) : Option String :=
  (e.syms.find? (·.2 = r)).map (·.1)

def ra : Nat := 1
def sp : Nat := 2

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

def Env.target (e : Env) : Target → Except String (Addr γ)
  | .ro o => pure ⟨e.ro, Ctl.ofInt o⟩
  | .got k => pure ⟨e.got, Ctl.ofInt (8 * (k : Int))⟩
  | .sym n o => match e.syms.find? (·.1 = n) with
    | some (_, r) => pure ⟨r, Ctl.ofInt o⟩
    | none => throw s!"unknown symbol {n}"

def zeroV : Val α γ := .num (Lane.const 0) (Lane.const 0)

/-- Read `x i` (`x0` is zero). -/
def rget (s : State α γ) (i : Nat) : Val α γ := if i = 0 then zeroV else s.getG i

/-- Write `x i` (writes to `x0` are dropped). -/
def rset (s : State α γ) (i : Nat) (v : Val α γ) : State α γ := if i = 0 then s else s.setG i v

/-- The 64-bit two's complement lanes of an integer. -/
def lanesOfInt (k : Int) : α × α :=
  (Lane.const (BitVec.ofInt 32 k), Lane.const (BitVec.ofInt 32 (k / 4294967296)))

/-- A register as 64-bit data (a constant count is its two's complement bits). -/
def dataOf (v : Val α γ) : Except String (α × α) :=
  match v with
  | .num lo hi => pure (lo, hi)
  | .ptr ⟨0, n⟩ => match Ctl.asInt n with
    | some k => pure (lanesOfInt k)
    | none => throw "symbolic count as data"
  | .ptr _ => throw "pointer as data"

/-- The signed 64-bit integer with low lane `l` and high lane `h`. -/
def sint64 (l h : W32) : Int :=
  let u : Nat := h.toNat * 2 ^ 32 + l.toNat
  if u ≥ 2 ^ 63 then (u : Int) - 2 ^ 64 else (u : Int)

/-- A register as a control value (address; numbers in region 0, constant data read as a signed
64-bit integer). -/
def ctlOf (v : Val α γ) : Except String (Addr γ) :=
  match v with
  | .ptr a => pure a
  | .num lo hi => match Lane.asConst lo, Lane.asConst hi with
    | some l, some h => pure ⟨rNum, Ctl.ofInt (sint64 l h)⟩
    | _, _ => throw "data as pointer/count"

/-- Sign extension of a 32-bit result. -/
def sext (r : α) : Val α γ := .num r (Lane.sar r 31)

def bop : BOp → α → α → α
  | .and => Lane.and
  | .or => Lane.or
  | .xor => Lane.xor

/-- 64-bit addition on lane pairs: the carry out of the low lane is bit 31 of
`(a & b) | ((a | b) & ~(a + b))`. -/
def add64 (a b : α × α) : α × α :=
  let s := Lane.add a.1 b.1
  let carry := Lane.shr (Lane.or (Lane.and a.1 b.1) (Lane.and (Lane.or a.1 b.1) (Lane.not s))) 31
  (s, Lane.add (Lane.add a.2 b.2) carry)

/-- 64-bit logical left shift (`n < 64`). -/
def shl64 (x : α × α) (n : Nat) : α × α :=
  if n = 0 then x
  else if n < 32 then (Lane.shl x.1 n, Lane.or (Lane.shl x.2 n) (Lane.shr x.1 (32 - n)))
  else if n = 32 then (Lane.const 0, x.1)
  else (Lane.const 0, Lane.shl x.1 (n - 32))

/-- 64-bit arithmetic right shift (`n < 64`). -/
def sra64 (x : α × α) (n : Nat) : α × α :=
  if n = 0 then x
  else if n < 32 then (Lane.or (Lane.shr x.1 n) (Lane.shl x.2 (32 - n)), Lane.sar x.2 n)
  else if n = 32 then (x.2, Lane.sar x.2 31)
  else (Lane.sar x.2 (n - 32), Lane.sar x.2 31)

/-- Byte reversal of a lane. -/
def bswap32 (x : α) : α :=
  Lane.or (Lane.or (byteOf x 3) (Lane.shl (byteOf x 2) 8))
    (Lane.or (Lane.shl (byteOf x 1) 16) (Lane.shl (byteOf x 0) 24))

/-- 32-bit operation with shift amount `n` (`n < 32`). -/
def wop (op : WOp) (x : α) (n : Nat) : α :=
  match op with
  | .slliw => Lane.shl x n
  | .srliw => Lane.shr x n
  | .sraiw => Lane.sar x n
  | .roriw => Lane.ror x n

def shaF (op : ShaOp) (x : α) : α :=
  match op with
  | .sum0 => Lane.xor (Lane.xor (Lane.ror x 2) (Lane.ror x 13)) (Lane.ror x 22)
  | .sum1 => Lane.xor (Lane.xor (Lane.ror x 6) (Lane.ror x 11)) (Lane.ror x 25)
  | .sig0 => Lane.xor (Lane.xor (Lane.ror x 7) (Lane.ror x 18)) (Lane.shr x 3)
  | .sig1 => Lane.xor (Lane.xor (Lane.ror x 17) (Lane.ror x 19)) (Lane.shr x 10)

/-- 64-bit `a + b`: pointer/count arithmetic when one side is a pointer or a count (the other
must then be a number), otherwise data addition.  `x0` as an operand is the identity (`c.mv`). -/
def addVal (a b : Val α γ) : Except String (Val α γ) :=
  match a, b with
  | .ptr p, .ptr q =>
    if q.region = rNum then pure (.ptr (p.plus q.off))
    else if p.region = rNum then pure (.ptr (q.plus p.off))
    else throw "pointer + pointer"
  | .ptr p, .num _ _ => do let q ← ctlOf b; pure (.ptr (p.plus q.off))
  | .num _ _, .ptr q => do let p ← ctlOf a; pure (.ptr (q.plus p.off))
  | .num _ _, .num _ _ => do
    let x ← dataOf a
    let y ← dataOf b
    let r := add64 x y
    pure (.num r.1 r.2)

/-- Effective address `x b + off` (the base must be a pointer). -/
def ea (s : State α γ) (b : Nat) (off : Int) : Except String (Addr γ) :=
  match rget s b with
  | .ptr a => if a.region = rNum then throw "number as address" else pure (a.plusI off)
  | .num _ _ => throw "data as address"

/-- Stores into the program's read-only regions fault. -/
def checkWritable (env : Env) (a : Addr γ) : Except String Unit :=
  if a.region = env.ro ∨ a.region = env.got then throw "store to read-only data" else pure ()

/-- The null pointer (the number 0). -/
def isNullA (a : Addr γ) : Prop := a.region = rNum ∧ Ctl.asInt a.off = some 0

instance (a : Addr γ) : Decidable (isNullA a) := inferInstanceAs (Decidable (_ ∧ _))

/-- Equality of two control values: same region → compare offsets; a non-null pointer never
equals the number 0; anything else is undetermined (error). -/
def eqCond (x y : Addr γ) : Except String (Cond γ) :=
  if x.region = y.region then pure (.eq x.off y.off)
  else if (isNullA x ∧ y.region ≠ rNum) ∨ (isNullA y ∧ x.region ≠ rNum) then pure (.not .tt)
  else throw "comparison of unrelated values"

/-! Named state updates (proof-friendly: no record updates inside `exec`). -/

def halt (s : State α γ) : State α γ := { s with halted := true }
def setPc (s : State α γ) (k : Nat) : State α γ := { s with pc := k }
/-- Left by a tail call to `name`. -/
def haltTail (s : State α γ) (name : String) : State α γ := { s with halted := true, tail := some name }
/-- Stopped at a call of an external function (`pc` = the return point). -/
def callOut (s : State α γ) (pc : Nat) (name : String) : State α γ :=
  { s with pc := pc, halted := true, tail := some name }
/-- Record conditions the rest of the run relies on (like undecided branches). -/
def assumeC (s : State α γ) (cs : List (Cond γ × Bool)) : State α γ := { s with assume := cs ++ s.assume }

/-- `x d := return address` (the instruction after the current one). -/
def link (env : Env) (s : State α γ) (d : Nat) : State α γ :=
  rset s d (.ptr ⟨env.code, Ctl.ofInt ((s.pc : Int) + 1)⟩)

/-- Transfer of control to address `t` (from `jalr`), linking `d`. -/
def jumpTo (env : Env) (s : State α γ) (d : Nat) (t : Addr γ) : Except String (State α γ) :=
  if t.region = rRet then
    if d = 0 then pure (halt s) else throw "call to the return address"
  else if t.region = env.code then
    match Ctl.asInt t.off with
    | some k => if k ≥ 0 then pure (setPc (link env s d) k.toNat) else throw "bad code address"
    | none => throw "symbolic code address"
  else match env.nameOf t.region, Ctl.asInt t.off with
    | some name, some k =>
      if k = 0 then
        if d = 0 then pure (haltTail s name)
        else pure (callOut (link env s d) (s.pc + 1) ("call:" ++ name))
      else throw "jump to unknown address"
    | _, _ => throw "jump to unknown address"

/-- A count stays in the signed 64-bit range (the conditions recorded for a symbolic count). -/
def noWrap (r : γ) : List (Cond γ × Bool) :=
  [(.lt r (Ctl.ofInt (2 ^ 63)), true), (.le (Ctl.ofInt (-(2 ^ 63))) r, true)]

/-- `slli d, ·, n` on the value `v` (`n < 64`): a count is multiplied by `2 ^ n` (counts never
wrap: a concrete overflow is reported, for a symbolic count the range is recorded as an
assumption, see `noWrap`); data is shifted across the lane pair. -/
def slliV (s : State α γ) (d : Nat) (v : Val α γ) (n : Nat) : Except String (State α γ) :=
  match v with
  | .ptr ⟨0, k⟩ =>
    let r : γ := Ctl.smul (2 ^ n) k
    match Ctl.asInt r with
    | some v => if v ≥ 2 ^ 63 ∨ v < -(2 ^ 63) then throw "count overflow" else
      pure (rset s d (.ptr ⟨rNum, r⟩)).next
    | none => pure (rset (assumeC s (noWrap r)) d (.ptr ⟨rNum, r⟩)).next
  -- `dataOf` of a pointer
  | .ptr ⟨_ + 1, _⟩ => throw "pointer as data"
  | .num lo hi =>
    let y := shl64 (lo, hi) n
    pure (rset s d (.num y.1 y.2)).next

/-- The result of a step, or the failed state. -/
def okOr (s : State α γ) (r : Except String (State α γ)) : State α γ :=
  match r with
  | .ok s' => s'
  | .error e => s.fail e

/-- Effect of one instruction (`orc`: directions of undecided branches). -/
def exec (env : Env) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr) (s : State α γ) :
    State α γ :=
  if s.halted then s else
  match i with
  | .nop => s.next
  | .unimp => s.fail "illegal instruction"
  | .lui d imm20 =>
    let v : α := Lane.const (BitVec.ofNat 32 ((imm20 % 2 ^ 20) * 2 ^ 12))
    (rset s d (sext v)).next
  | .auipc d t => okOr s do
    let a ← env.target t
    pure (rset s d (.ptr a)).next
  | .addi d r imm => okOr s do
    let c : α × α := lanesOfInt imm
    let v ← addVal (rget s r) (.num c.1 c.2)
    pure (rset s d v).next
  | .add d a b => okOr s do
    let v ← if a = 0 then pure (rget s b) else if b = 0 then pure (rget s a)
      else addVal (rget s a) (rget s b)
    pure (rset s d v).next
  | .bop op d a b => okOr s do
    let x ← dataOf (rget s a)
    let y ← dataOf (rget s b)
    pure (rset s d (.num (bop op x.1 y.1) (bop op x.2 y.2))).next
  | .bopi op d a imm => okOr s do
    let x ← dataOf (rget s a)
    let y : α × α := lanesOfInt imm
    pure (rset s d (.num (bop op x.1 y.1) (bop op x.2 y.2))).next
  | .slli d r n => okOr s (if n ≥ 64 then throw "shift amount" else slliV s d (rget s r) n)
  | .srai d r n => okOr s do
    if n ≥ 64 then throw "shift amount" else
    let x ← dataOf (rget s r)
    let y := sra64 x n
    pure (rset s d (.num y.1 y.2)).next
  | .wop op d r n => okOr s do
    if n ≥ 32 then throw "shift amount" else
    let x ← dataOf (rget s r)
    pure (rset s d (sext (wop op x.1 n))).next
  | .addw d a b => okOr s do
    let x ← dataOf (rget s a)
    let y ← dataOf (rget s b)
    pure (rset s d (sext (Lane.add x.1 y.1))).next
  | .rev8 d r => okOr s do
    let x ← dataOf (rget s r)
    pure (rset s d (.num (bswap32 x.2) (bswap32 x.1))).next
  | .sha op d r => okOr s do
    let x ← dataOf (rget s r)
    pure (rset s d (sext (shaF op x.1))).next
  | .lwu d b off => okOr s do
    let a ← ea s b off
    let w ← loadLane mem0 s a
    pure (rset s d (.num w (Lane.const 0))).next
  | .ld d b off => okOr s do
    let a ← ea s b off
    let v ← loadVal mem0 s a
    pure (rset s d v).next
  | .sw src b off => okOr s do
    let a ← ea s b off
    checkWritable env a
    let x ← dataOf (rget s src)
    pure (storeLane s a x.1).next
  | .sd src b off => okOr s do
    let a ← ea s b off
    checkWritable env a
    pure (storeVal s a (rget s src)).next
  | .br c a b t => okOr s do
    let x ← ctlOf (rget s a)
    let y ← ctlOf (rget s b)
    let e ← eqCond x y
    pure (s.branch orc (if c = .eq then e else .not e) t)
  | .jal d t => setPc (link env s d) t
  | .jalr d r off => okOr s do
    let t ← ctlOf (rget s r)
    jumpTo env s d (t.plusI off)

/-- Fetch-execute `n` steps. -/
def run (prog : Array Instr) (env : Env) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    Nat → State α γ → State α γ
  | 0, s => s
  | n + 1, s =>
    if s.halted then s
    else match prog[s.pc]? with
      | some i => run prog env mem0 orc n (exec env mem0 orc i s)
      | none => s.fail "pc out of program"

end

end Hashtree.Asm.Riscv
