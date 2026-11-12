import Hashtree.Asm.Arm
import Hashtree.Spec

/-!
# Concrete runs of the AArch64 kernel models (validation harness)

An AAPCS64 entry state (x0 = output, x1 = input, x2 = count, x30 = the return target in region
`rRet`, SP = `rStack + sp0`), the input bytes in region `rIn`, each program's read-only data in
its own region; tail calls continue in the named program.  Every other register holds junk; the
stack, the output buffer and everything outside the input and the read-only data are poison
(reading them before writing is an error).  Used by `armcheck`
(compare with `Spec.node`, the ABI observations, and with the real code under qemu).
-/

namespace Hashtree.Asm.ArmRun
open Hashtree.Asm Hashtree.Asm.Arm

abbrev CS := State W32 Int

/-- A kernel program and the region of its read-only data. -/
structure Prog where
  name : String
  code : Array Instr
  ro : Region
  rodata : Array Nat

/-- Region of the poison cells. -/
def rPoison : Region := 99

/-- Concrete initial memory: the input bytes `[0, input.size)` and each program's rodata; every
other byte (output, stack, the caller's frame, beyond the input or the rodata) is a poison cell —
a byte of a pointer into region `rPoison` — so that reading it as data, or as a pointer, is an
error: the run checks that the kernel reads nothing it did not write itself except its input
and its read-only data. -/
def mem0 (progs : List Prog) (input : Array Nat) : Addr Int → Cell W32 Int := fun a =>
  let poison : Cell W32 Int := .pb ⟨rPoison, a.off⟩ 0
  if a.region = rIn then
    if 0 ≤ a.off ∧ a.off < input.size then .dat (BitVec.ofNat 32 (input.getD a.off.toNat 0)) 0
    else poison
  else match progs.find? (·.ro = a.region) with
    | some p =>
      if 0 ≤ a.off ∧ a.off < p.rodata.size then .dat (BitVec.ofNat 32 (p.rodata.getD a.off.toNat 0)) 0
      else poison
    | none => poison

def junkG (i : Nat) : Val W32 Int := .num (BitVec.ofNat 32 (0x1000 + i)) (BitVec.ofNat 32 (0x2000 + i))

/-- AAPCS64 entry: x0 = output, x1 = input, x2 = count, x30 = return target, SP (index 31). -/
def entry (count : Nat) (sp0 : Int) : CS :=
  let g := (List.range 32).map junkG
  let g := g.set 0 (.ptr ⟨rOut, 0⟩)
  let g := g.set 1 (.ptr ⟨rIn, 0⟩)
  let g := g.set 2 (.ptr ⟨rNum, count⟩)
  let g := g.set 30 (.ptr ⟨rRet, 0⟩)
  let g := g.set 31 (.ptr ⟨rStack, sp0⟩)
  let vr := (List.range 32).map fun r => (List.range 16).map fun l =>
    BitVec.ofNat 32 (0x51000000 + 256 * r + l)
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

/-- ABI observations of a finished run (AAPCS64): deepest stack byte written (bytes below the
entry SP), writes at or above the entry SP (the caller's frame), writes outside output and stack,
output writes outside `[0, 32·count)`, callee-saved registers (x19..x29, low 64 bits of v8..v15)
whose final value differs from the entry value, final SP = entry SP. -/
structure AbiObs where
  depth : Int
  callerWrites : List Int
  strayWrites : List String
  outOfRange : List Int
  clobbered : List String
  spOk : Bool
  deriving Repr

def abiObs (count : Nat) (sp0 : Int) (s : CS) : AbiObs :=
  let e := entry count sp0
  let stackOffs := s.mem.filterMap fun (a, _) => if a.region = rStack then some (a.off - sp0) else none
  let depth := stackOffs.foldl (fun m o => if o < m then o else m) 0
  let callerWrites := (stackOffs.filter (· ≥ 0)).eraseDups
  let stray := (s.mem.filterMap fun (a, _) =>
    if a.region = rStack ∨ a.region = rOut then none else some s!"r{a.region}+{a.off}").eraseDups
  let outOfRange := (s.mem.filterMap fun (a, _) =>
    if a.region = rOut ∧ (a.off < 0 ∨ a.off ≥ 32 * count) then some a.off else none).eraseDups
  let gClob := ((List.range 11).map (· + 19)).filter (fun i => !(decide (s.getG i = e.getG i)))
  let vClob := ((List.range 8).map (· + 8)).filter (fun i => !(decide (getD s i = getD e i)))
  { depth := -depth, callerWrites := callerWrites, strayWrites := stray, outOfRange := outOfRange,
    clobbered := gClob.map (fun i => s!"x{i}") ++ vClob.map (fun i => s!"d{i}"),
    spOk := decide (s.getG 31 = .ptr ⟨rStack, sp0⟩) }

end Hashtree.Asm.ArmRun
