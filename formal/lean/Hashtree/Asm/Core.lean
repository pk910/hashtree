/-!
# Machine core: values, control, memory, state

Shared by the x86-64, AArch64 and RISC-V models of the hashtree kernels.

* **Data** are 32-bit lanes (SHA-256 is a 32-bit algorithm). A 64-bit general register holding
  data is a pair of lanes; byte shuffles are expressed with shifts and masks. The lane type is a
  parameter (`Lane α`): `BitVec 32` gives the executable machine, `E` (expressions over
  variables) the symbolic executor.
* **Control values** — pointers and counts — are integers (`Ctl γ`): `Int` concretely, `Lin`
  (linear forms over a few symbols, e.g. "input base + 64") symbolically, so one symbolic run of a
  loop body covers every iteration.  An address is a region and an offset; region bases are
  64-byte aligned (the offset carries the low bits, so `and rsp, -32` is computable).
* **Memory** is byte-addressed: a write log over an initial memory.  Reading a byte compares
  addresses; an address that may or may not equal a logged write (different symbols) is an error,
  never a guess.
* **Branches** on a condition that is not a constant take the direction of an oracle and record
  the condition; theorems about such runs assume the recorded conditions.

The concrete instances (`BitVec 32`, `Int`) are the machine model a reader has to trust; the
symbolic instances are proof tools whose agreement with it is proved (`Hom.lean`).
-/

namespace Hashtree.Asm

abbrev W32 := BitVec 32

/-! ## Data lanes -/

/-- `vpternlogd imm`: bitwise `imm[a b c]` (sum of the selected minterms). -/
def ternW (imm : Nat) (a b c : W32) : W32 :=
  let lit (x : W32) (bit : Bool) := if bit then x else ~~~ x
  (List.range 8).foldl (fun acc i =>
    if imm.testBit i then acc ||| (lit a (i.testBit 2) &&& (lit b (i.testBit 1) &&& lit c (i.testBit 0)))
    else acc) 0#32

/-! ## Control values -/

/-- Pointwise sum of coefficient lists (padded). -/
def addC : List Int → List Int → List Int
  | a :: as, b :: bs => (a + b) :: addC as bs
  | [], bs => bs
  | as, [] => as

/-- `k + Σ cᵢ·sᵢ`. -/
structure Lin where
  k : Int
  c : List Int
  deriving DecidableEq, Repr, Inhabited

def Lin.ofInt (k : Int) : Lin := ⟨k, []⟩
def Lin.sym (i : Nat) : Lin := ⟨0, List.replicate i 0 ++ [1]⟩
def Lin.add (a b : Lin) : Lin := ⟨a.k + b.k, addC a.c b.c⟩
def Lin.smul (n : Int) (a : Lin) : Lin := ⟨n * a.k, a.c.map (n * ·)⟩
def Lin.sub (a b : Lin) : Lin := a.add (b.smul (-1))
def Lin.asInt (a : Lin) : Option Int := if a.c.all (· == 0) then some a.k else none

def dotC : List Int → Nat → (Nat → Int) → Int
  | [], _, _ => 0
  | c :: cs, i, σ => c * σ i + dotC cs (i + 1) σ

def Lin.eval (σ : Nat → Int) (a : Lin) : Int := a.k + dotC a.c 0 σ

/-- Variable keys: numbered variables (registers, cuts) and the initial memory byte at a
symbolic address (region, offset). -/
inductive Key where
  | n (i : Nat)
  | m (r : Nat) (off : Lin)
  deriving DecidableEq, Repr, Inhabited

/-- Symbolic 32-bit lane expressions. -/
inductive E where
  | var (k : Key)
  | const (v : W32)
  | add (a b : E)
  | xor (a b : E)
  | and (a b : E)
  | or (a b : E)
  | not (a : E)
  | shl (a : E) (n : Nat)
  | shr (a : E) (n : Nat)
  | sar (a : E) (n : Nat)
  | ror (a : E) (n : Nat)
  | tern (imm : Nat) (a b c : E)
  deriving DecidableEq, Repr, Inhabited

def E.eval (env : Key → W32) : E → W32
  | .var i => env i
  | .const v => v
  | .add a b => a.eval env + b.eval env
  | .xor a b => a.eval env ^^^ b.eval env
  | .and a b => a.eval env &&& b.eval env
  | .or a b => a.eval env ||| b.eval env
  | .not a => ~~~ a.eval env
  | .shl a n => a.eval env <<< n
  | .shr a n => a.eval env >>> n
  | .sar a n => (a.eval env).sshiftRight n
  | .ror a n => (a.eval env).rotateRight n
  | .tern i a b c => ternW i (a.eval env) (b.eval env) (c.eval env)

/-- The lane operations the models use. -/
class Lane (α : Type) where
  const : W32 → α
  add : α → α → α
  xor : α → α → α
  and : α → α → α
  or : α → α → α
  not : α → α
  shl : α → Nat → α
  shr : α → Nat → α
  sar : α → Nat → α
  ror : α → Nat → α
  tern : Nat → α → α → α → α
  /-- the value, if it is a known constant -/
  asConst : α → Option W32
  /-- syntactic identity (only used to keep reassembled loads small; never needed for truth) -/
  same : α → α → Bool

instance : Lane W32 where
  const := id
  add := (· + ·)
  xor := (· ^^^ ·)
  and := (· &&& ·)
  or := (· ||| ·)
  not := (~~~ ·)
  shl := (· <<< ·)
  shr := (· >>> ·)
  sar := fun x n => x.sshiftRight n
  ror := BitVec.rotateRight
  tern := ternW
  asConst := some
  -- the machine never needs the shortcut: reassembling the bytes gives the same value
  same := fun _ _ => false

/-- Symbolic lanes, folding constants. -/
instance : Lane E where
  const := .const
  add a b := match a, b with
    | .const x, .const y => .const (x + y)
    | _, _ => .add a b
  xor a b := match a, b with
    | .const x, .const y => .const (x ^^^ y)
    | _, _ => .xor a b
  and a b := match a, b with
    | .const x, .const y => .const (x &&& y)
    | _, _ => .and a b
  or a b := match a, b with
    | .const x, .const y => .const (x ||| y)
    | _, _ => .or a b
  not a := match a with
    | .const x => .const (~~~ x)
    | _ => .not a
  shl a n := match a with
    | .const x => .const (x <<< n)
    | _ => .shl a n
  shr a n := match a with
    | .const x => .const (x >>> n)
    | _ => .shr a n
  sar a n := match a with
    | .const x => .const (x.sshiftRight n)
    | _ => .sar a n
  ror a n := match a with
    | .const x => .const (x.rotateRight n)
    | _ => .ror a n
  tern i a b c := match a, b, c with
    | .const x, .const y, .const z => .const (ternW i x y z)
    | _, _, _ => .tern i a b c
  asConst e := match e with
    | .const v => some v
    | _ => none
  same a b := decide (a = b)

/-- Control-value operations. -/
class Ctl (γ : Type) where
  ofInt : Int → γ
  add : γ → γ → γ
  smul : Int → γ → γ
  asInt : γ → Option Int

instance : Ctl Int where
  ofInt := id
  add := (· + ·)
  smul := (· * ·)
  asInt := some

instance : Ctl Lin where
  ofInt := Lin.ofInt
  add := Lin.add
  smul := Lin.smul
  asInt := Lin.asInt

def Ctl.sub {γ : Type} [Ctl γ] (a b : γ) : γ := Ctl.add a (Ctl.smul (-1) b)

/-! ## Values, addresses, memory cells -/

/-- Region 0: plain numbers; 1 input, 2 output, 3 stack, 4 read-only data, 5 return target,
6.. other symbols (e.g. tail-call targets). Bases are 64-byte aligned. -/
abbrev Region := Nat

def rNum : Region := 0
def rIn : Region := 1
def rOut : Region := 2
def rStack : Region := 3
def rRo : Region := 4
def rRet : Region := 5

structure Addr (γ : Type) where
  region : Region
  off : γ
  deriving DecidableEq, Repr, Inhabited

/-- A 64-bit general register: data (two lanes, low first) or a pointer/count. -/
inductive Val (α γ : Type) where
  | num (lo hi : α)
  | ptr (a : Addr γ)
  deriving DecidableEq, Repr, Inhabited

/-- A memory byte: byte `k` (0 = least significant) of a data lane, or of a pointer/count. -/
inductive Cell (α γ : Type) where
  | dat (x : α) (k : Nat)
  | pb (a : Addr γ) (k : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Not a poison cell (a pointer byte with index ≥ 8, which no load accepts). -/
def Cell.okC {α γ : Type} : Cell α γ → Prop
  | .dat _ _ => True
  | .pb _ k => k < 8

/-- Address comparison: `some true` same byte, `some false` different, `none` undetermined. -/
class AddrEq (γ : Type) where
  same : Addr γ → Addr γ → Option Bool

instance : AddrEq Int where
  same a b := some (a.region == b.region && a.off == b.off)

instance : AddrEq Lin where
  same a b := if a.region != b.region then some false
    else match (a.off.sub b.off).asInt with
      | some 0 => some true
      | some _ => some false
      | none => none

/-! ## Conditions and flags -/

/-- A comparison of two control values (mathematical integers). -/
inductive Cond (γ : Type) where
  | eq (a b : γ)
  | lt (a b : γ)
  | le (a b : γ)
  | not (c : Cond γ)
  | tt
  deriving DecidableEq, Repr, Inhabited

def Cond.decideC {γ : Type} [Ctl γ] : Cond γ → Option Bool
  | .eq a b => (Ctl.asInt (Ctl.sub a b)).map (· == 0)
  | .lt a b => (Ctl.asInt (Ctl.sub a b)).map (· < 0)
  | .le a b => (Ctl.asInt (Ctl.sub a b)).map (· ≤ 0)
  | .not c => c.decideC.map (! ·)
  | .tt => some true

/-! ## Machine state -/

/-- A machine state. `gpr`: general registers; `vr`: vector registers as lane lists (16 lanes,
the low part aliasing xmm/q registers); `flags`: the last comparison (x86 `cmp a b` / ARM `cmp`:
`a - b` as integers; `none` after a flag-setting data operation); `mem`: the write log, newest
first, over the initial memory `mem0` (a run parameter); `assume`: the recorded branch conditions
with the directions taken. -/
structure State (α γ : Type) where
  gpr : List (Val α γ)
  vr : List (List α)
  flags : Option (γ × γ)
  mem : List (Addr γ × Cell α γ)
  pc : Nat
  halted : Bool
  /-- `some name`: left by a jump to another function (tail call) -/
  tail : Option String
  err : Option String
  assume : List (Cond γ × Bool)
  deriving Inhabited, DecidableEq

section Ops
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

def State.fail (s : State α γ) (msg : String) : State α γ :=
  if s.err.isSome then { s with halted := true } else { s with err := some msg, halted := true }

def State.getG (s : State α γ) (i : Nat) : Val α γ := s.gpr.getD i (.num (Lane.const 0) (Lane.const 0))
def State.setG (s : State α γ) (i : Nat) (v : Val α γ) : State α γ := { s with gpr := s.gpr.set i v }
def State.getV (s : State α γ) (i : Nat) : List α := s.vr.getD i (List.replicate 16 (Lane.const 0))
def State.setV (s : State α γ) (i : Nat) (v : List α) : State α γ := { s with vr := s.vr.set i v }
def State.next (s : State α γ) : State α γ := { s with pc := s.pc + 1 }

/-- `a + n` for an address. -/
def Addr.plus (a : Addr γ) (n : γ) : Addr γ := ⟨a.region, Ctl.add a.off n⟩
def Addr.plusI (a : Addr γ) (n : Int) : Addr γ := a.plus (Ctl.ofInt n)

/-- Byte `k` of a lane, as a lane in `[0, 256)`. -/
def byteOf (x : α) (k : Nat) : α := Lane.and (Lane.shr x (8 * k)) (Lane.const 0xff)

/-- Find the newest logged write to `a`; `none` = not written; error if undetermined. -/
def lookup (a : Addr γ) : List (Addr γ × Cell α γ) → Except String (Option (Cell α γ))
  | [] => .ok none
  | (b, c) :: rest => match AddrEq.same a b with
    | some true => .ok (some c)
    | some false => lookup a rest
    | none => .error "may alias"

/-- Read one byte cell. -/
def readCell (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) : Except String (Cell α γ) :=
  match lookup a s.mem with
  | .ok (some c) => .ok c
  | .ok none => .ok (mem0 a)
  | .error e => .error e

/-- The data byte of a cell (pointer bytes are not data: error). -/
def cellData (c : Cell α γ) : Except String α :=
  match c with
  | .dat x k => .ok (byteOf x k)
  | .pb _ _ => .error "pointer byte read as data"

/-- Four cells that are bytes 0..3 of lanes (in order). -/
def lanePat : Cell α γ → Cell α γ → Cell α γ → Cell α γ → Option (α × α × α × α)
  | .dat x k0, .dat y k1, .dat z k2, .dat w k3 =>
    if k0 = 0 ∧ k1 = 1 ∧ k2 = 2 ∧ k3 = 3 then some (x, y, z, w) else none
  | _, _, _, _ => none

/-- Load a 32-bit little-endian lane at `a`. Four bytes of one lane in order give that lane back
(symbolically; the value is the same as reassembling the bytes). -/
def loadLane (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) : Except String α := do
  let c0 ← readCell mem0 s a
  let c1 ← readCell mem0 s (a.plusI 1)
  let c2 ← readCell mem0 s (a.plusI 2)
  let c3 ← readCell mem0 s (a.plusI 3)
  match lanePat c0 c1 c2 c3 with
  | some (x, y, z, w) =>
    if Lane.same x y && Lane.same x z && Lane.same x w then return x
    else
      let lo := Lane.or (byteOf x 0) (Lane.shl (byteOf y 1) 8)
      let hi := Lane.or (Lane.shl (byteOf z 2) 16) (Lane.shl (byteOf w 3) 24)
      return Lane.or lo hi
  | none =>
    let b0 ← cellData c0
    let b1 ← cellData c1
    let b2 ← cellData c2
    let b3 ← cellData c3
    let lo := Lane.or b0 (Lane.shl b1 8)
    let hi := Lane.or (Lane.shl b2 16) (Lane.shl b3 24)
    return Lane.or lo hi

/-- Load `n` consecutive lanes. -/
def loadLanes (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) : Nat → Except String (List α)
  | 0 => .ok []
  | n + 1 => do
    let x ← loadLane mem0 s a
    let xs ← loadLanes mem0 s (a.plusI 4) n
    return x :: xs

/-- Store a lane: four byte cells. -/
def storeLane (s : State α γ) (a : Addr γ) (x : α) : State α γ :=
  { s with mem := (a.plusI 3, .dat x 3) :: (a.plusI 2, .dat x 2) :: (a.plusI 1, .dat x 1) :: (a, .dat x 0) :: s.mem }

def storeLanes (s : State α γ) (a : Addr γ) : List α → State α γ
  | [] => s
  | x :: xs => storeLanes (storeLane s a x) (a.plusI 4) xs

/-- Is the cell byte `k` of pointer `p`? -/
def isPb (p : Addr γ) (k : Nat) : Cell α γ → Bool
  | .pb q j => AddrEq.same p q == some true && j == k
  | .dat _ _ => false

/-- Bytes `k … 7` at `a + k …` are the bytes of pointer `p`. -/
def pbRest (mem0 : Addr γ → Cell α γ) (s : State α γ) (p a : Addr γ) : Nat → Nat → Except String Bool
  | 0, _ => .ok true
  | n + 1, k => do
    let c ← readCell mem0 s (a.plusI k)
    if isPb p k c then pbRest mem0 s p a n (k + 1) else return false

/-- Load a 64-bit register value: the eight bytes of one pointer give it back, else data. -/
def loadVal (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) : Except String (Val α γ) := do
  let c0 ← readCell mem0 s a
  match c0 with
  | .pb p 0 =>
    if (← pbRest mem0 s p a 7 1) then return .ptr p else throw "partial pointer"
  | _ =>
    let lo ← loadLane mem0 s a
    let hi ← loadLane mem0 s (a.plusI 4)
    return .num lo hi

/-- Store a 64-bit register value. -/
def storeVal (s : State α γ) (a : Addr γ) (v : Val α γ) : State α γ :=
  match v with
  | .num lo hi => storeLane (storeLane s a lo) (a.plusI 4) hi
  | .ptr p => { s with mem := ((List.range 8).reverse.map (fun (i : Nat) => (a.plusI (Int.ofNat i), Cell.pb p i))) ++ s.mem }

/-- Branch on a condition: decided, or the oracle's direction, recorded. -/
def State.branch (orc : Nat → Bool) (s : State α γ) (c : Cond γ) (target : Nat) : State α γ :=
  let taken := match c.decideC with
    | some b => b
    | none => orc s.pc
  let s := if c.decideC.isNone then { s with assume := (c, taken) :: s.assume } else s
  if taken then { s with pc := target } else s.next

end Ops

end Hashtree.Asm
