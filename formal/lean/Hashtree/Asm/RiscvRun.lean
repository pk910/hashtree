import Hashtree.Asm.Riscv
import Hashtree.Spec
import Std.Data.HashMap

/-!
# Concrete runs of the RV64 models (validation harness)

An LP64D entry state (`a0` = output, `a1` = input, `a2` = count, `ra` = a pointer into the return
region `rRet`, `sp` 16-byte aligned), the input bytes in region `rIn`, each program's `.rodata`
and GOT in their own regions; tail calls (`jalr x0` to a named function) continue in the named
program, calls to external functions (`syscall`) are answered by a stub.  Used by `rvcheck`
(compare with `Spec.node`, with qemu, and the dispatcher's selection).

`runP` is `Riscv.run` with two harness-only additions that do not change the result:
* every `foldEvery` steps the write log is folded into a hash map consulted before the initial
  memory (`readCell` = newest logged write, else initial memory, so folding the log into the
  initial memory preserves every read; `selfTest` in `RvCheck` compares with `Riscv.run`);
* memory accesses are recorded to count misaligned addresses (region bases are 64-byte
  aligned, so `offset mod width` is the alignment of the real address).
-/

namespace Hashtree.Asm.RiscvRun
open Hashtree.Asm Hashtree.Asm.Riscv

abbrev CS := State W32 Int

/-- A program: its code, its GOT contents, its object's pointer-valued data words and rodata;
regions `base` (rodata), `base + 1` (GOT), `base + 2` (code). -/
structure Prog where
  name : String
  code : Array Instr
  compressed : List Nat
  got : List Target
  datarel : List (String × Int × Target)
  rodata : Array Nat
  base : Region

/-- Data objects and external functions (no program): their regions. -/
def extSyms : List (String × Region) :=
  [(".data.rel.local", 60), ("__stack_chk_guard", 61), ("syscall", 62), ("__stack_chk_fail", 63)]

def symsOf (progs : List Prog) : List (String × Region) :=
  progs.map (fun p => (p.name, p.base + 2)) ++ extSyms

def Prog.env (progs : List Prog) (p : Prog) : Env := ⟨p.base, p.base + 1, p.base + 2, symsOf progs⟩

/-- The stack canary value (bytes of `__stack_chk_guard`). -/
def canary (k : Nat) : Nat := (0x5a + 17 * k) % 256

/-- Placement of the buffers: byte offsets of input and output inside their 64-byte aligned
regions (so any alignment can be exercised), and the entry stack pointer offset. -/
structure Layout where
  inOff : Int := 0
  outOff : Int := 0
  sp0 : Int := 0
  /-- the output buffer lies in the input buffer (in place / lagging output): region `rIn` -/
  alias : Bool := false

def Layout.outR (L : Layout) : Region := if L.alias then rIn else rOut

/-- Concrete initial memory. -/
def mem0 (progs : List Prog) (input : Array Nat) (L : Layout) : Addr Int → Cell W32 Int := fun a =>
  let resolve (p : Prog) (t : Target) : Addr Int :=
    match (p.env progs).target (γ := Int) t with
    | .ok x => x
    | .error _ => ⟨rNum, 0⟩
  if a.region = rIn then
    let i := a.off - L.inOff
    if 0 ≤ i then .dat (BitVec.ofNat 32 (input.getD i.toNat 0)) 0 else .dat 0 0
  else if a.region = 61 then .dat (BitVec.ofNat 32 (canary (a.off % 8).toNat)) 0
  else if a.region = 60 then
    match progs.findSome? (fun p => (p.datarel.find? (fun (sec, o, _) =>
        sec = ".data.rel.local" ∧ o ≤ a.off ∧ a.off < o + 8)).map (p, ·)) with
    | some (p, (_, o, t)) => .pb (resolve p t) (a.off - o).toNat
    | none => .dat 0 0
  else match progs.find? (·.base = a.region) with
    | some p => .dat (BitVec.ofNat 32 (p.rodata.getD a.off.toNat 0)) 0
    | none => match progs.find? (·.base + 1 = a.region) with
      | some p => match p.got[(a.off / 8).toNat]? with
        | some t => .pb (resolve p t) (a.off % 8).toNat
        | none => .dat 0 0
      | none => .dat 0 0

def junk (i : Nat) : Val W32 Int := .num (BitVec.ofNat 32 (0x1000 + i)) (BitVec.ofNat 32 (0x2000 + i))

/-- LP64D entry: `a0` = output, `a1` = input, `a2` = count, `ra` = return, `sp`. -/
def entry (count : Nat) (L : Layout) : CS :=
  let g := (List.range 32).map junk
  let g := g.set ra (.ptr ⟨rRet, 0⟩)
  let g := g.set sp (.ptr ⟨rStack, L.sp0⟩)
  let g := g.set 10 (.ptr ⟨L.outR, L.outOff⟩)
  let g := g.set 11 (.ptr ⟨rIn, L.inOff⟩)
  let g := g.set 12 (.ptr ⟨rNum, count⟩)
  { gpr := g, vr := [], flags := none, mem := [], pc := 0,
    halted := false, tail := none, err := none, assume := [] }

/-- Callee-saved registers of the LP64D ABI (plus `sp`, `gp`, `tp`). -/
def calleeSaved : List Nat := [2, 3, 4, 8, 9] ++ (List.range 10).map (· + 18)

/-! ## The stepping runner -/

/-- Memory access of an instruction: base register, offset, width, store? -/
def accessOf : Instr → Option (Nat × Int × Nat × Bool)
  | .lwu _ b o => some (b, o, 4, false)
  | .ld _ b o => some (b, o, 8, false)
  | .sw _ b o => some (b, o, 4, true)
  | .sd _ b o => some (b, o, 8, true)
  | _ => none

/-- Per region (input, output, stack, other): accesses and misaligned accesses. -/
structure Stats where
  steps : Nat := 0
  acc : Array Nat := #[0, 0, 0, 0]
  mis : Array Nat := #[0, 0, 0, 0]
  /-- first misaligned accesses: (program, pc, region, offset) -/
  firstMis : List (String × Nat × Region × Int) := []
  /-- executed instructions whose ISA tag or encoding is outside `allowed` -/
  isaViol : List (String × Nat) := []
  deriving Inhabited

def regionSlot (r : Region) : Nat := if r = rIn then 0 else if r = rOut then 1 else if r = rStack then 2 else 3

/-- Folded memory: initial memory overlaid with the folded writes. -/
abbrev FMap := Std.HashMap (Nat × Int) (Cell W32 Int)

def overlay (m0 : Addr Int → Cell W32 Int) (fm : FMap) : Addr Int → Cell W32 Int :=
  fun a => fm.getD (a.region, a.off) (m0 a)

def fold (fm : FMap) (log : List (Addr Int × Cell W32 Int)) : FMap :=
  log.reverse.foldl (fun m (a, c) => m.insert (a.region, a.off) c) fm

def foldEvery : Nat := 2048

/-- Run `p` from `s` for at most `fuel` steps. -/
def runP (progs : List Prog) (allowed : List Riscv.Ext) (m0 : Addr Int → Cell W32 Int) (p : Prog) :
    Nat → FMap → Stats → CS → CS × FMap × Stats
  | 0, fm, st, s => (s, fm, st)
  | n + 1, fm, st, s =>
    if s.halted then (s, fm, st) else
    match p.code[s.pc]? with
    | none => (s.fail "pc out of program", fm, st)
    | some i =>
      let env := p.env progs
      let mem := overlay m0 fm
      let st := { st with steps := st.steps + 1 }
      let st := if i.isa.any (allowed.contains ·) ∧ (¬ p.compressed.contains s.pc ∨ allowed.contains .c)
        then st else { st with isaViol := (p.name, s.pc) :: st.isaViol }
      let st := match accessOf i with
        | some (b, o, w, _) => match ea s b o with
          | .ok a =>
            let k := regionSlot a.region
            let st := { st with acc := st.acc.modify k (· + 1) }
            if a.off % (w : Int) = 0 then st
            else { st with mis := st.mis.modify k (· + 1),
                           firstMis := if st.firstMis.length < 4 then st.firstMis ++ [(p.name, s.pc, a.region, a.off)] else st.firstMis }
          | .error _ => st
        | none => st
      let s' := exec env mem (fun _ => false) i s
      if s'.mem.length ≥ foldEvery then
        runP progs allowed m0 p n (fold fm s'.mem) st { s' with mem := [] }
      else runP progs allowed m0 p n fm st s'

/-- Answer of the `riscv_hwprobe` stub: `none` = the syscall fails (returns -1). -/
abbrev Probe := Option Nat

/-- The `syscall` stub: `riscv_hwprobe(pairs, 1, 0, NULL, 0)` (a0 = 258) with one pair whose
key is 4 (`RISCV_HWPROBE_KEY_IMA_EXT_0`): store the value, return 0; caller-saved registers are
clobbered. -/
def syscallStub (probe : Probe) (m0 : Addr Int → Cell W32 Int) (s : CS) : CS :=
  let clobber (s : CS) : CS :=
    ([5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] : List Nat).foldl
      (fun s r => rset s r (junk (r + 100))) s
  match ctlOf (rget s 10), rget s 11, ctlOf (rget s 12) with
  | .ok nr, .ptr pa, .ok cnt =>
    if nr.region = rNum ∧ nr.off = 258 ∧ cnt.region = rNum ∧ cnt.off = 1 then
      match loadVal m0 s pa with
      | .ok (.num k0 k1) =>
        if k0 = 4 ∧ k1 = 0 then
          match probe with
          | some v =>
            let s := storeVal s (pa.plusI 8) (.num (BitVec.ofNat 32 v) (BitVec.ofNat 32 (v / 2 ^ 32)))
            rset (clobber s) 10 (.num 0 0)
          | none => rset (clobber s) 10 (.num (BitVec.ofInt 32 (-1)) (BitVec.ofInt 32 (-1)))
        else s.fail "hwprobe key"
      | _ => s.fail "hwprobe pairs"
    else s.fail "unexpected syscall"
  | _, _, _ => s.fail "unexpected syscall"

/-- Run `name` from `s`, following tail calls and answering calls (at most `hops`). -/
def runChain (progs : List Prog) (allowed : List Riscv.Ext) (probe : Probe) (m0 : Addr Int → Cell W32 Int)
    (fuel : Nat) : Nat → String → FMap → Stats → CS → CS × FMap × Stats × List String
  | 0, _, fm, st, s => (s.fail "too many tail calls", fm, st, [])
  | hops + 1, name, fm, st, s =>
    match progs.find? (·.name = name) with
    | none => (s.fail ("unknown program " ++ name), fm, st, [])
    | some p =>
      let (s', fm, st) := runP progs allowed m0 p fuel fm st s
      match s'.tail, s'.err with
      | some t, none =>
        if t.startsWith "call:" then
          let callee := (t.drop 5).toString
          if callee = "syscall" then
            let s'' := syscallStub probe (overlay m0 fm) { s' with halted := false, tail := none }
            let (r, fm, st, path) := runChain progs allowed probe m0 fuel hops name fm st s''
            (r, fm, st, name :: ("call:" ++ callee) :: path)
          else ({ s' with err := some ("call to " ++ callee) }, fm, st, [name])
        else
          let (r, fm, st, path) := runChain progs allowed probe m0 fuel hops t fm st
            { s' with pc := 0, halted := false, tail := none }
          (r, fm, st, name :: path)
      | _, _ => (s', fm, st, [name])

/-- The output bytes (`none` if a byte cannot be read as data). -/
def outBytes (m : Addr Int → Cell W32 Int) (s : CS) (L : Layout) (n : Nat) : Option (List Nat) :=
  (List.range n).mapM fun (i : Nat) => match readCell m s ⟨L.outR, L.outOff + (i : Int)⟩ with
    | .ok (.dat x k) => some (byteOf x k).toNat
    | _ => none

/-- Expected output: SHA-256 of each 64-byte block. -/
def expected (input : Array Nat) (count : Nat) : List Nat :=
  (List.range count).flatMap fun b =>
    (Spec.node (fun i => BitVec.ofNat 8 (input.getD (64 * b + i.val) 0))).map (·.toNat)

/-- Writes outside the output buffer and the stack window `[sp0 - depth, sp0)` (data objects of
the dispatcher allowed when `dataOk`). -/
def badWrites (fm : FMap) (s : CS) (L : Layout) (count depth : Nat) (dataOk : Bool) : List (Nat × Int) :=
  let ws := fm.toList.map (·.1) ++ s.mem.map (fun (a, _) => (a.region, a.off))
  ws.filter fun (r, o) =>
    ¬ ((r = L.outR ∧ L.outOff ≤ o ∧ o < L.outOff + 32 * count) ∨
       (r = rStack ∧ L.sp0 - depth ≤ o ∧ o < L.sp0) ∨ (dataOk ∧ r = 60))

/-- Deepest stack byte written, relative to the entry stack pointer. -/
def stackDepth (fm : FMap) (s : CS) (L : Layout) : Int :=
  let ws := fm.toList.map (·.1) ++ s.mem.map (fun (a, _) => (a.region, a.off))
  ws.foldl (fun d (r, o) => if r = rStack ∧ L.sp0 - o > d then L.sp0 - o else d) 0

end Hashtree.Asm.RiscvRun
