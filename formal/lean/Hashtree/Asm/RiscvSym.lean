import Hashtree.Asm.Cut
import Hashtree.Asm.Slice
import Hashtree.Asm.X86Sym
import Hashtree.Asm.RiscvRunHom
import Hashtree.Asm.Chain

/-!
# Symbolic entry state and initial memory for the RV64 kernels

Same design as `X86Sym` (whose `poison`, `cellX`, `EnvMem` are reused): input bytes are unknowns
keyed by their symbolic address (any offset); at constant offsets the program's rodata bytes,
and its GOT entries (pointer bytes); everything else — the output buffer, the stack (a kernel
may only read stack bytes it wrote itself), other regions, symbolic offsets outside the input — is
poison, which no successful symbolic load reads.  RISC-V keeps the return address in `ra` (a pointer into
`rRet`), not in memory.  `WfMemR` is the concrete memory this describes; `mem0RelR_of_wf`
derives `Mem0Rel` from it, and `cmemR_wf` shows it is satisfiable.
-/

namespace Hashtree.Asm.RiscvSym
open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.X86Sym

/-- Symbolic initial memory: program regions `ro` (rodata) and `got` (GOT entries: pointers
`⟨region, offset⟩`, eight bytes each). -/
def mem0s (ro got : Region) (rodata : List Nat) (gotT : List (Region × Int)) : Addr Lin → Cell E Lin := fun a =>
  if a.region = rIn then .dat (.var (.m a.region a.off)) 0
  else match a.off.asInt with
    | some o =>
      if a.region = ro then .dat (.const (BitVec.ofNat 32 (rodata.getD o.toNat 0))) 0
      else if a.region = got then
        if 0 ≤ o then
          match gotT[(o / 8).toNat]? with
          | some (r, k) => .pb ⟨r, Lin.ofInt k⟩ (o % 8).toNat
          | none => poison
        else poison
      else poison
    | none => poison

/-- LP64D entry: `a0` = output, `a1` = input, `a2` = count (symbols 1, 0, 2), `ra` = return,
`sp` = `sp0`, every other register a variable. -/
def entryS (sp0 : Int) : State E Lin :=
  let g := (List.range 32).map fun i =>
    if i = 1 then Val.ptr ⟨rRet, Lin.ofInt 0⟩
    else if i = 2 then Val.ptr ⟨rStack, Lin.ofInt sp0⟩
    else if i = 10 then Val.ptr ⟨rOut, Lin.sym 1⟩
    else if i = 11 then Val.ptr ⟨rIn, Lin.sym 0⟩
    else if i = 12 then Val.ptr ⟨rNum, Lin.sym 2⟩
    else Val.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))
  { gpr := g, vr := [], flags := none, mem := [], pc := 0, halted := false, tail := none, err := none,
    assume := [] }

/-- The concrete initial memory the symbolic one describes. -/
def WfMemR (ro got : Region) (rodata : List Nat) (gotT : List (Region × Int)) (mem0c : Addr Int → Cell W32 Int) : Prop :=
  ro ≠ rIn ∧ got ≠ rIn ∧ got ≠ ro ∧
  (∀ o, mem0c ⟨ro, o⟩ = .dat (BitVec.ofNat 32 (rodata.getD o.toNat 0)) 0) ∧
  (∀ o r k, 0 ≤ o → gotT[(o / 8).toNat]? = some (r, k) → mem0c ⟨got, o⟩ = .pb ⟨r, k⟩ (o % 8).toNat) ∧
  (∀ o, mem0c ⟨rIn, o⟩ = .dat (cellX (mem0c ⟨rIn, o⟩)) 0)

theorem mem0RelR_of_wf (ro got : Region) (rodata : List Nat) (gotT : List (Region × Int)) (env : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (hw : WfMemR ro got rodata gotT mem0c)
    (he : EnvMem env σ mem0c) : Mem0Rel env σ (mem0s ro got rodata gotT) mem0c := by
  obtain ⟨_, _, hgr, hro, hgot, hin⟩ := hw
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
        by_cases h3 : r = got
        · subst h3
          simp only [ite_true] at ha ⊢
          by_cases h4 : 0 ≤ o
          · simp only [h4, ite_true] at ha ⊢
            cases hg : gotT[(o / 8).toNat]? with
            | none => rw [hg] at ha; simp [poison, Cell.okC] at ha
            | some p =>
              obtain ⟨rr, kk⟩ := p
              simp only [mapCell, mapAddr, hev, Lin.eval_lasInt σ (Lin.ofInt kk) kk rfl]
              exact hgot o rr kk h4 hg
          · simp only [h4, ite_false] at ha; simp [poison, Cell.okC] at ha
        · simp only [h3, ite_false] at ha; simp [poison, Cell.okC] at ha

theorem mem0s_keyed (ro got : Region) (rodata : List Nat) (gotT : List (Region × Int)) :
    MemKeyed (mem0s ro got rodata gotT) := by
  intro a
  simp only [mem0s, poison]
  split
  · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
  · split
    · split
      · exact Or.inl ⟨_, _, rfl⟩
      · split
        · split
          · split
            · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
            · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
          · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
        · exact Or.inr (Or.inr ⟨_, _, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- A well-formed memory exists for any input bytes. -/
def cmemR (ro got : Region) (rodata : List Nat) (gotT : List (Region × Int)) (inp : Int → W32) :
    Addr Int → Cell W32 Int := fun a =>
  if a.region = ro then .dat (BitVec.ofNat 32 (rodata.getD a.off.toNat 0)) 0
  else if a.region = got then
    if 0 ≤ a.off then
      match gotT[(a.off / 8).toNat]? with
      | some (r, k) => .pb ⟨r, k⟩ (a.off % 8).toNat
      | none => .dat 0 0
    else .dat 0 0
  else if a.region = rIn then .dat (inp a.off) 0
  else .dat 0 0

theorem cmemR_wf (ro got : Region) (rodata : List Nat) (gotT : List (Region × Int)) (inp : Int → W32)
    (h1 : ro ≠ rIn) (h3 : got ≠ rIn) (h5 : got ≠ ro) :
    WfMemR ro got rodata gotT (cmemR ro got rodata gotT inp) := by
  refine ⟨h1, h3, h5, ?_, ?_, ?_⟩
  · intro o; simp [cmemR]
  · intro o r k ho hg; simp [cmemR, h5, ho, hg]
  · intro o
    have e1 : ¬ (rIn = ro) := fun h => h1 h.symm
    have e2 : ¬ (rIn = got) := fun h => h3 h.symm
    simp only [cmemR, e1, e2, ite_false, ite_true, cellX]

/-- The memory keys read from a concrete memory. -/
def envOfMem (σ : Nat → Int) (m : Addr Int → Cell W32 Int) : Key → W32
  | .n _ => 0
  | .m r off => cellX (m ⟨r, off.eval σ⟩)

/-- The hypotheses of the kernel theorems are satisfiable: for every input and every symbol
valuation there is a well-formed memory holding the input, with matching memory keys. -/
theorem hyps_satR (ro got : Region) (rodata : List Nat) (gotT : List (Region × Int))
    (h1 : ro ≠ rIn) (h3 : got ≠ rIn) (h5 : got ≠ ro)
    (inp : Nat → Hashtree.Spec.Byte) (σ : Nat → Int) (nb : Nat) :
    ∃ mem0c env0, WfMemR ro got rodata gotT mem0c ∧ EnvMem env0 σ mem0c ∧ HMem nb inp env0 := by
  let m := cmemR ro got rodata gotT (fun x => (inp (x - σ 0).toNat).zeroExtend 32)
  refine ⟨m, envOfMem σ m, cmemR_wf ro got rodata gotT _ h1 h3 h5, fun _ _ => rfl, ?_⟩
  intro o _
  have e1 : ¬ (rIn = ro) := fun h => h1 h.symm
  have e2 : ¬ (rIn = got) := fun h => h3 h.symm
  simp only [envOfMem, m, cmemR, e1, e2, ite_false, ite_true, cellX, Lin.eval, dotC]
  rw [show ((o : Int) + (1 * σ 0 + 0) - σ 0).toNat = o by omega]

/-- Symbolic memory at the exit segment: like `mem0s`, except that the stack slots the prologue
saved registers in (`saves`, byte offsets below the entry stack pointer) are read back from the
memory keys of those addresses, so that the epilogue's loads are symbolic and `Mem0Rel` holds
against any memory whose cells there have the saved values (the loop's accumulated log). -/
def mem0sT (ro got : Region) (rodata : List Nat) (gotT : List (Region × Int)) (saves : List Int) :
    Addr Lin → Cell E Lin := fun a =>
  match a.off.asInt with
  | some o =>
    if a.region = rStack ∧ saves.contains o then
      .dat (.var (.m rStack a.off)) (((o + 16) % 4).toNat)
    else mem0s ro got rodata gotT a
  | none => mem0s ro got rodata gotT a

theorem mem0sT_keyed (ro got : Region) (rodata : List Nat) (gotT : List (Region × Int)) (saves : List Int) :
    MemKeyed (mem0sT ro got rodata gotT saves) := by
  intro a
  unfold mem0sT
  split
  · split
    · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
    · exact mem0s_keyed ro got rodata gotT a
  · exact mem0s_keyed ro got rodata gotT a

end Hashtree.Asm.RiscvSym
