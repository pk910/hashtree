import Hashtree.Asm.X86
import Hashtree.Spec

/-!
# Concrete runs of the x86 kernel models (validation harness)

An ABI entry state (System V or Win64 argument registers, return address on the stack), the
input bytes in region `rIn`, each program's `.rodata` in its own region; tail calls continue in
the named program.  Used by `x86check` (compare with `Spec.node` and with the real CPU).
-/

namespace Hashtree.Asm.X86Run
open Hashtree.Asm Hashtree.Asm.X86

abbrev CS := State W32 Int

/-- A kernel program and the region of its `.rodata`. -/
structure Prog where
  name : String
  code : Array Instr
  ro : Region
  rodata : Array Nat

/-- Concrete initial memory: input bytes, each program's rodata, the return address at the
stack offset `sp0`, zeros elsewhere. -/
def mem0 (progs : List Prog) (input : Array Nat) (sp0 : Int) : Addr Int → Cell W32 Int := fun a =>
  if a.region = rIn then .dat (BitVec.ofNat 32 (input.getD a.off.toNat 0)) 0
  else if a.region = rStack ∧ sp0 ≤ a.off ∧ a.off < sp0 + 8 then .pb ⟨rRet, 0⟩ (a.off - sp0).toNat
  else match progs.find? (·.ro = a.region) with
    | some p => .dat (BitVec.ofNat 32 (p.rodata.getD a.off.toNat 0)) 0
    | none => .dat 0 0

/-- System V entry: rdi = output, rsi = input, rdx = count; `win`: rcx, rdx, r8. -/
def entry (win : Bool) (count : Nat) (sp0 : Int) : CS :=
  let junk (i : Nat) : Val W32 Int := .num (BitVec.ofNat 32 (0x1000 + i)) (BitVec.ofNat 32 (0x2000 + i))
  let g := (List.range 16).map junk
  let set (g : List (Val W32 Int)) (i : Nat) (v : Val W32 Int) := g.set i v
  let g := if win then set (set (set g 1 (.ptr ⟨rOut, 0⟩)) 2 (.ptr ⟨rIn, 0⟩)) 8 (.ptr ⟨rNum, count⟩)
    else set (set (set g 7 (.ptr ⟨rOut, 0⟩)) 6 (.ptr ⟨rIn, 0⟩)) 2 (.ptr ⟨rNum, count⟩)
  let g := set g 4 (.ptr ⟨rStack, sp0⟩)
  let vr := (List.range 32).map fun r => (List.range 16).map fun l => BitVec.ofNat 32 (0x51000000 + 256 * r + l)
  { gpr := g, vr := vr, flags := none, mem := [], pc := 0,
    halted := false, tail := none, err := none, assume := [] }

/-- Run `name`, following tail calls (at most `hops`). -/
def runChain (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (fuel : Nat) :
    Nat → String → CS → CS × List String
  | 0, _, s => (s.fail "too many tail calls", [])
  | hops + 1, name, s =>
    match progs.find? (·.name = name) with
    | none => (s.fail ("unknown program " ++ name), [])
    | some p =>
      let s' := run p.code p.ro m0 (fun _ => false) fuel s
      match s'.tail, s'.err with
      | some t, none =>
        let (r, path) := runChain progs m0 fuel hops t { s' with pc := 0, halted := false, tail := none }
        (r, name :: path)
      | _, _ => (s', [name])

/-- The output bytes the run wrote (`none` if a byte cannot be read as data). -/
def outBytes (m0 : Addr Int → Cell W32 Int) (s : CS) (n : Nat) : Option (List Nat) :=
  (List.range n).mapM fun (i : Nat) => match readCell m0 s ⟨rOut, (i : Int)⟩ with
    | .ok (.dat x k) => some (byteOf x k).toNat
    | _ => none

/-- Expected output: SHA-256 of each 64-byte block. -/
def expected (input : Array Nat) (count : Nat) : List Nat :=
  (List.range count).flatMap fun b =>
    (Spec.node (fun i => BitVec.ofNat 8 (input.getD (64 * b + i.val) 0))).map (·.toNat)

/-- ABI observations of a finished run: deepest stack byte written (bytes below the entry SP),
writes at or above the entry SP (the return address and the caller's area, Win64 home space
included), callee-saved registers whose final value differs from the entry value, final SP. -/
structure AbiObs where
  depth : Int
  callerWrites : List Int
  clobbered : List String
  spOk : Bool
  deriving Repr

def gprNames : List String := ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10",
  "r11", "r12", "r13", "r14", "r15"]

def abiObs (win : Bool) (count : Nat) (sp0 : Int) (s : CS) : AbiObs :=
  let e := entry win count sp0
  let stackOffs := s.mem.filterMap fun (a, _) => if a.region = rStack then some (a.off - sp0) else none
  let depth := stackOffs.foldl (fun m o => if o < m then o else m) 0
  let callerWrites := (stackOffs.filter (· ≥ 0)).eraseDups
  let savedG : List Nat := if win then [3, 5, 6, 7, 12, 13, 14, 15] else [3, 5, 12, 13, 14, 15]
  let gClob := savedG.filter (fun i => !(decide (s.getG i = e.getG i)))
  let vClob : List Nat := if win then (List.range 10).map (· + 6) |>.filter
      (fun i => !(decide ((s.getV i).take 4 = (e.getV i).take 4))) else []
  { depth := -depth, callerWrites := callerWrites,
    clobbered := gClob.map (fun i => gprNames.getD i "?") ++ vClob.map (fun i => s!"xmm{i}"),
    spOk := decide (s.getG 4 = .ptr ⟨rStack, sp0 + 8⟩) }

end Hashtree.Asm.X86Run
