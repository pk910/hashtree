import Hashtree.Asm.Cut
import Hashtree.Asm.Slice
import Hashtree.Asm.ArmRunHom

/-!
# Symbolic entry states and initial memory for the AArch64 kernels

AAPCS64 entry: x0 = output, x1 = input, x2 = count (symbols 1, 0, 2), x30 = the return target
(region `rRet`), SP = `rStack + sp0`; every other register (and every vector lane) a variable.
Initial memory: the read-only data bytes of the program's region `ro`, every other byte an
unknown keyed by its address.
-/

namespace Hashtree.Asm.ArmSym
open Hashtree.Asm Hashtree.Asm.Arm

def sIn : Nat := 0
def sOut : Nat := 1
def sCnt : Nat := 2

/-- A poison cell: no load accepts it, and `Mem0Rel` does not constrain the concrete memory there. -/
def poison : Cell E Lin := .pb ⟨rRet, Lin.ofInt 0⟩ 8

/-- Symbolic initial memory.  Input bytes (any offset) are unknowns keyed by their symbolic
address; rodata bytes of program region `ro` (constant offsets) are constants.  Everything else
is poison: the whole stack (AArch64 keeps the return address in x30), the output buffer, other
regions, symbolic offsets into rodata — a successful symbolic run never reads them, so the
kernel reads no stack byte it has not written itself. -/
def mem0s (ro : Region) (rodata : List Nat) : Addr Lin → Cell E Lin := fun a =>
  if a.region = rIn then .dat (.var (.m a.region a.off)) 0
  else match a.off.asInt with
    | some o =>
      if a.region = ro then .dat (.const (BitVec.ofNat 32 (rodata.getD o.toNat 0))) 0
      else poison
    | none => poison

/-- The data value of a concrete cell. -/
def cellX : Cell W32 Int → W32
  | .dat x _ => x
  | .pb _ _ => 0

/-- The concrete initial memory the symbolic one describes: rodata bytes, data bytes (byte 0 of
a cell) in the input. -/
def WfMem (ro : Region) (rodata : List Nat) (mem0c : Addr Int → Cell W32 Int) : Prop :=
  ro ≠ rIn ∧ ro ≠ rStack ∧
  (∀ o, mem0c ⟨ro, o⟩ = .dat (BitVec.ofNat 32 (rodata.getD o.toNat 0)) 0) ∧
  (∀ o, mem0c ⟨rIn, o⟩ = .dat (cellX (mem0c ⟨rIn, o⟩)) 0)

/-- Memory keys hold the concrete memory's data. -/
def EnvMem (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) : Prop :=
  ∀ r off, env (.m r off) = cellX (mem0c ⟨r, off.eval σ⟩)

theorem mem0Rel_of_wf (ro : Region) (rodata : List Nat) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (hw : WfMem ro rodata mem0c) (he : EnvMem env σ mem0c) :
    Mem0Rel env σ (mem0s ro rodata) mem0c := by
  obtain ⟨hri, hrs, hro, hin⟩ := hw
  intro a ha
  obtain ⟨r, off⟩ := a
  simp only [mem0s] at ha ⊢
  by_cases h1 : r = rIn
  · subst h1
    simp only [ite_true, mapCell, E.eval, mapAddr]
    rw [he]; exact hin _
  · simp only [h1, ite_false] at ha ⊢
    cases hk : off.asInt with
    | none => rw [hk] at ha; simp [poison, Cell.okC] at ha
    | some o =>
      rw [hk] at ha
      have hev : off.eval σ = o := Lin.eval_asInt σ off o hk
      by_cases h2 : r = ro
      · subst h2
        simp only [ite_true, mapCell, E.eval, mapAddr, hev]
        exact hro o
      · simp only [h2, ite_false] at ha; simp [poison, Cell.okC] at ha

def entryS (sp0 : Int) : State E Lin :=
  let g := (List.range 32).map fun i =>
    if i = 0 then Val.ptr ⟨rOut, Lin.sym sOut⟩
    else if i = 1 then Val.ptr ⟨rIn, Lin.sym sIn⟩
    else if i = 2 then Val.ptr ⟨rNum, Lin.sym sCnt⟩
    else if i = 30 then Val.ptr ⟨rRet, Lin.ofInt 0⟩
    else if i = 31 then Val.ptr ⟨rStack, Lin.ofInt sp0⟩
    else Val.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))
  { gpr := g, vr := (List.range 32).map (fun i => (List.range 16).map fun l => .var (.n (vId i l))),
    flags := none, mem := [], pc := 0, halted := false, tail := none, err := none, assume := [] }

theorem mem0s_keyed (ro : Region) (rodata : List Nat) : MemKeyed (mem0s ro rodata) := by
  intro a
  simp only [mem0s, poison]
  split
  · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
  · split
    · split
      · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- The hypotheses are satisfiable: a well-formed memory exists for any input bytes. -/
def cmem (ro : Region) (rodata : List Nat) (inp : Int → W32) : Addr Int → Cell W32 Int := fun a =>
  if a.region = ro then .dat (BitVec.ofNat 32 (rodata.getD a.off.toNat 0)) 0
  else if a.region = rIn then .dat (inp a.off) 0
  else .dat 0 0

theorem cmem_wf (ro : Region) (rodata : List Nat) (inp : Int → W32) (h1 : ro ≠ rIn) (h2 : ro ≠ rStack) :
    WfMem ro rodata (cmem ro rodata inp) := by
  refine ⟨h1, h2, ?_, ?_⟩
  · intro o; simp [cmem]
  · intro o
    have h3 : (rIn = ro) = False := propext ⟨fun h => h1 h.symm, False.elim⟩
    simp only [cmem, h3, ite_false, ite_true, cellX]

end Hashtree.Asm.ArmSym
