import Hashtree.Asm.Cut
import Hashtree.Asm.Slice
import Hashtree.Asm.X86RunHom

/-!
# Symbolic entry states and initial memory for the x86 kernels
-/

namespace Hashtree.Asm.X86Sym
open Hashtree.Asm Hashtree.Asm.X86

/-- Symbols: 0 input base, 1 output base, 2 count. -/
def sIn : Nat := 0
def sOut : Nat := 1
def sCnt : Nat := 2

/-- A poison cell: no load accepts it, and `Mem0Rel` does not constrain the concrete memory there. -/
def poison : Cell E Lin := .pb ⟨rRet, Lin.ofInt 0⟩ 8

/-- Symbolic initial memory.  Constant offsets: the rodata bytes of program region `ro`, the
return address at the entry stack offset `sp0`.
Input bytes (any offset) are unknowns keyed by their symbolic address.  Everything else is
poison: the output buffer, other stack bytes (a kernel only reads stack it wrote itself), other
regions, and symbolic offsets into rodata or the stack — a successful symbolic run never reads them. -/
def mem0s (ro : Region) (rodata : List Nat) (sp0 : Int) : Addr Lin → Cell E Lin := fun a =>
  if a.region = rIn then .dat (.var (.m a.region a.off)) 0
  else match a.off.asInt with
    | some o =>
      if a.region = ro then .dat (.const (BitVec.ofNat 32 (rodata.getD o.toNat 0))) 0
      else if a.region = rStack then
        if sp0 ≤ o ∧ o < sp0 + 8 then .pb ⟨rRet, Lin.ofInt 0⟩ (o - sp0).toNat
        else poison
      else poison
    | none => poison

/-- The data value of a concrete cell. -/
def cellX : Cell W32 Int → W32
  | .dat x _ => x
  | .pb _ _ => 0

/-- The concrete initial memory the symbolic one describes (rodata, return address, data bytes
as byte 0 of a cell). -/
def WfMem (ro : Region) (rodata : List Nat) (sp0 : Int) (mem0c : Addr Int → Cell W32 Int) : Prop :=
  ro ≠ rIn ∧ ro ≠ rStack ∧
  (∀ o, mem0c ⟨ro, o⟩ = .dat (BitVec.ofNat 32 (rodata.getD o.toNat 0)) 0) ∧
  (∀ o, sp0 ≤ o → o < sp0 + 8 → mem0c ⟨rStack, o⟩ = .pb ⟨rRet, 0⟩ (o - sp0).toNat) ∧
  (∀ o, mem0c ⟨rIn, o⟩ = .dat (cellX (mem0c ⟨rIn, o⟩)) 0)

/-- Memory keys hold the concrete memory's data. -/
def EnvMem (env : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) : Prop :=
  ∀ r off, env (.m r off) = cellX (mem0c ⟨r, off.eval σ⟩)

theorem mem0Rel_of_wf (ro : Region) (rodata : List Nat) (sp0 : Int) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (hw : WfMem ro rodata sp0 mem0c) (he : EnvMem env σ mem0c) :
    Mem0Rel env σ (mem0s ro rodata sp0) mem0c := by
  obtain ⟨hri, hrs, hro, hret, hin⟩ := hw
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
      · simp only [h2, ite_false] at ha ⊢
        by_cases h3 : r = rStack
        · subst h3
          simp only [ite_true] at ha ⊢
          by_cases h4 : sp0 ≤ o ∧ o < sp0 + 8
          · simp only [h4, and_self, ite_true, mapCell, mapAddr, hev]
            rw [hret o h4.1 h4.2]; rfl
          · simp only [h4, ite_false] at ha; simp [poison, Cell.okC] at ha
        · simp only [h3, ite_false] at ha; simp [poison, Cell.okC] at ha

/-- System V entry state: rdi = output, rsi = input, rdx = count (symbols), rsp = `sp0`, every
other register a variable. -/
def entryS (sp0 : Int) : State E Lin :=
  let g := (List.range 16).map fun i =>
    if i = 7 then Val.ptr ⟨rOut, Lin.sym sOut⟩
    else if i = 6 then Val.ptr ⟨rIn, Lin.sym sIn⟩
    else if i = 2 then Val.ptr ⟨rNum, Lin.sym sCnt⟩
    else if i = 4 then Val.ptr ⟨rStack, Lin.ofInt sp0⟩
    else Val.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))
  { gpr := g, vr := (List.range 32).map (fun i => (List.range 16).map fun l => .var (.n (vId i l))),
    flags := none, mem := [], pc := 0, halted := false, tail := none, err := none, assume := [] }

theorem mem0s_keyed (ro : Region) (rodata : List Nat) (sp0 : Int) : MemKeyed (mem0s ro rodata sp0) := by
  intro a
  simp only [mem0s, poison]
  split
  · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
  · split
    · split
      · exact Or.inl ⟨_, _, rfl⟩
      · split
        · split
          · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
          · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
        · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- The hypotheses are satisfiable: a well-formed memory exists for any input bytes. -/
def cmem (ro : Region) (rodata : List Nat) (sp0 : Int) (inp : Int → W32) : Addr Int → Cell W32 Int := fun a =>
  if a.region = ro then .dat (BitVec.ofNat 32 (rodata.getD a.off.toNat 0)) 0
  else if a.region = rStack then
    if sp0 ≤ a.off ∧ a.off < sp0 + 8 then .pb ⟨rRet, 0⟩ (a.off - sp0).toNat else .dat 0 0
  else if a.region = rIn then .dat (inp a.off) 0
  else .dat 0 0

theorem cmem_wf (rodata : List Nat) (sp0 : Int) (inp : Int → W32) : WfMem 4 rodata sp0 (cmem 4 rodata sp0 inp) := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · intro o; simp [cmem]
  · intro o h1 h2; simp [cmem, rStack, h1, h2]
  · intro o; simp [cmem, rIn, rStack, cellX]

end Hashtree.Asm.X86Sym
