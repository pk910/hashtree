import Hashtree.Asm.X86SymW
import Hashtree.Asm.SpecQV

/-!
# Wrapper-call memory and cut states for the avx_x4 all-count proof

The `c = 4` pilot `Gen/AvxX4P` is stated at `entryS 24` (absolute stack, system-V-style caller
registers).  A wrapper call enters at `X86SymW.entryW` (stack relative to symbol 9, callee-saved
registers holding the wrapper's pointers).  This file rebases a pilot cut state on the wrapper
call state syntactically (`shiftK`) and provides the fast chunked wrapper memory `mem0qW`.

`shiftK` keeps the kernel's own registers and memory but replaces the registers the kernel never
writes (rax, rbx, rbp, r12-r15) by the wrapper's values, and moves stack addresses from absolute
offsets to offsets relative to the entry stack pointer (symbol 9, marker at `[s9, s9 + 8)`).

The dead register `rax` is given its own symbol (`15`), not the output pointer's symbol `1`: the
loop invariant is re-entered under a substitution that advances symbol 1, and only a symbol
beyond the substitution is left untouched.  `entryWx` is `entryW` with exactly that rax, and
`mapState_entryWx` shows it denotes the same concrete state as `entryW` once symbol 15 is given
the output pointer's value.
-/

namespace Hashtree.Asm.X86SymW
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym

/-- `mem0sW` with chunked rodata. -/
def mem0qW (ro : Region) (C : List (List Nat)) (push : List (Int × Cell E Lin)) :
    Addr Lin → Cell E Lin := fun a =>
  if a.region = rStack then
    match stackRel a.off with
    | some k =>
      if 0 <= k ∧ k < 8 then .pb ⟨rRet, Lin.ofInt 0⟩ k.toNat
      else match plookup k push with
        | some c => c
        | none => poison
    | none => poison
  else mem0q ro C 24 a

theorem mem0qW_eq (ro : Region) (rodata : List Nat) (push : List (Int × Cell E Lin))
    (C : List (List Nat)) (f : Nat) (hC : C = chunksF 64 f rodata)
    (hf : rodata.length <= f * 64) :
    mem0qW ro C push = mem0sW ro rodata push := by
  subst hC
  have hq : mem0q ro (chunksF 64 f rodata) 24 = mem0s ro rodata 24 :=
    mem0q_eq ro rodata 24 (chunksF 64 f rodata) f rfl hf
  funext a
  unfold mem0qW mem0sW
  by_cases hs : a.region = rStack
  · simp only [hs, ite_true]
    rfl
  · simp only [hs, ite_false]
    exact congrFun hq a

theorem mem0qW_keyed (ro : Region) (rodata : List Nat) (push : List (Int × Cell E Lin))
    (C : List (List Nat)) (f : Nat) (hC : C = chunksF 64 f rodata)
    (hf : rodata.length <= f * 64) (hp : pushKeyed push = true) :
    MemKeyed (mem0qW ro C push) := by
  rw [mem0qW_eq ro rodata push C f hC hf]
  exact mem0sW_keyed ro rodata push hp

end Hashtree.Asm.X86SymW

namespace Hashtree.Proofs.AvxX4W
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW

/-- The wrapper call state with the dead register `rax` given its own symbol (15) so that the
loop substitution (which advances symbols 0, 1, 2 and replaces the flags 3, 4) leaves it alone.
Otherwise identical to `entryW`. -/
def entryWx : State E Lin :=
  let g := (List.range 16).map fun i =>
    if i = 7 then Val.ptr ⟨rOut, Lin.sym 1⟩
    else if i = 6 then Val.ptr ⟨rIn, Lin.sym 0⟩
    else if i = 2 then Val.ptr ⟨rNum, Lin.sym 2⟩
    else if i = 4 then Val.ptr ⟨rStack, sAt 0⟩
    else if i = 0 then Val.ptr ⟨rOut, Lin.sym 15⟩
    else if i = 1 then Val.ptr ⟨rNum, Lin.sym 2⟩
    else if i = 3 then Val.ptr ⟨rStack, Lin.sym 5⟩
    else if i = 5 then Val.ptr ⟨rStack, Lin.sym 6⟩
    else if i = 12 then Val.ptr ⟨rStack, Lin.sym 7⟩
    else if i = 14 then Val.ptr ⟨rG, Lin.sym 8⟩
    else if i = 13 then Val.ptr ⟨rNum, Lin.sym 11⟩
    else if i = 15 then Val.ptr ⟨rNum, Lin.sym 12⟩
    else Val.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))
  { gpr := g, vr := (List.range 32).map (fun i => (List.range 16).map fun l => .var (.n (vId i l))),
    flags := none, mem := [], pc := 0, halted := false, tail := none, err := none, assume := [] }

/-- A stack address of the pilot (absolute offset) becomes the same address relative to
the wrapper entry stack pointer; other addresses are unchanged. -/
def shiftA (a : Addr Lin) : Addr Lin :=
  if a.region = rStack then ⟨a.region, ⟨a.off.k - 24, stkC⟩⟩ else a

def shiftV : Val E Lin → Val E Lin
  | .num lo hi => .num lo hi
  | .ptr a => .ptr (shiftA a)

def shiftC : Cell E Lin → Cell E Lin
  | .dat x j => .dat x j
  | .pb a j => .pb (shiftA a) j

/-- The wrapper entry value of a register the x4 kernel never writes. -/
def wReg : Nat → Val E Lin
  | 0 => .ptr ⟨rOut, Lin.sym 15⟩
  | 3 => .ptr ⟨rStack, Lin.sym 5⟩
  | 5 => .ptr ⟨rStack, Lin.sym 6⟩
  | 12 => .ptr ⟨rStack, Lin.sym 7⟩
  | 13 => .ptr ⟨rNum, Lin.sym 11⟩
  | 14 => .ptr ⟨rG, Lin.sym 8⟩
  | 15 => .ptr ⟨rNum, Lin.sym 12⟩
  | _ => .num (.const 0) (.const 0)

/-- A pilot cut state rebased on the wrapper call state. -/
def shiftK (K : State E Lin) : State E Lin :=
  let g := K.gpr.map shiftV
  { K with
    gpr := ((((((g.set 0 (wReg 0)).set 3 (wReg 3)).set 5 (wReg 5)).set 12 (wReg 12)).set 13 (wReg 13)).set 14 (wReg 14)).set 15 (wReg 15),
    mem := K.mem.map (fun p => (shiftA p.1, shiftC p.2)) }

theorem shiftK_pc (K : State E Lin) : (shiftK K).pc = K.pc := rfl
theorem shiftK_halted (K : State E Lin) : (shiftK K).halted = K.halted := rfl
theorem shiftK_tail (K : State E Lin) : (shiftK K).tail = K.tail := rfl
theorem shiftK_err (K : State E Lin) : (shiftK K).err = K.err := rfl
theorem shiftK_flags (K : State E Lin) : (shiftK K).flags = K.flags := rfl
theorem shiftK_assume (K : State E Lin) : (shiftK K).assume = K.assume := rfl


/-- Symbol `15` carries the (dead) `rax` of `entryWx`.  It is beyond the length of the loop
substitution, and is given the output pointer's value `σ 1`, so that `entryWx` denotes the same
concrete state as `entryW`. -/
def upd15 (σ : Nat → Int) : Nat → Int := fun i => if i = 15 then σ 1 else σ i

/-- The wrapper environment with the numbered keys taken from `e` and the memory keys read from
a concrete memory at the sigma `σ`.  This is the environment under which `entryWx` (at
`upd15 σ`) denotes exactly the `entryW` state of a caller whose environment is `e`. -/
def envM (e : Key → W32) (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) : Key → W32 :=
  fun k => match k with
    | .n _ => e k
    | .m r off => cellX (mem0c ⟨r, off.eval σ⟩)

theorem envM_n (e : Key → W32) (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) (i : Nat) :
    envM e mem0c σ (.n i) = e (.n i) := rfl

theorem envM_m (e : Key → W32) (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) (r : Nat)
    (off : Lin) : envM e mem0c σ (.m r off) = cellX (mem0c ⟨r, off.eval σ⟩) := rfl

theorem range16 : List.range 16 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := by decide

/-- `entryWx` at the sigma `upd15 σ` denotes the `entryW` call state at `σ`: symbol 15 holds the
output pointer's value, and no other register, vector or memory entry reads a symbol `≥ 15`. -/
theorem mapState_entryWx (e : Key → W32) (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) :
    mapState (envM e mem0c σ) (upd15 σ) entryWx = mapState e σ entryW := by
  simp [mapState, entryW, entryWx, range16, mapVal, Lin.eval, Lin.sym, sAt, stkC]
  repeat' constructor
  all_goals
    first
    | rfl
    | simp [mapAddr, Lin.eval, dotC, upd15]
    | (intro a ha; repeat' (all_goals (first | constructor)); all_goals simp [E.eval, envM])

end Hashtree.Proofs.AvxX4W
