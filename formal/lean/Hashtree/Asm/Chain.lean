import Hashtree.Asm.Slice
import Hashtree.Asm.SpecQ
import Std.Tactic.BVDecide

/-!
# Invariants at cuts, and the facts that chain slices
-/

namespace Hashtree.Asm
open Hashtree.Asm.SpecQ Hashtree.Spec

/-- At a cut: every labelled location variable holds its spec quantity. -/
def Inv (L : List (Nat × Q)) (inp : Nat → Byte) (env : Key → W32) : Prop :=
  ∀ p ∈ L, env (.n p.1) = qv inp p.2

/-- The input bytes (relative to the input base, symbol 0) are the memory keys' values. -/
def HMem (nbytes : Nat) (inp : Nat → Byte) (env : Key → W32) : Prop :=
  ∀ o, o < nbytes → env (.m rIn (⟨(o : Int), [1]⟩ : Lin)) = (inp o).zeroExtend 32

theorem inv_get {L : List (Nat × Q)} {inp : Nat → Byte} {env : Key → W32} (h : Inv L inp env) (k : Nat)
    (hk : k < L.length) : env (.n L[k].1) = qv inp L[k].2 := h _ (List.getElem_mem hk)

theorem inv_of_get (L : List (Nat × Q)) (inp : Nat → Byte) (env : Key → W32)
    (h : ∀ k (hk : k < L.length), env (.n L[k].1) = qv inp L[k].2) : Inv L inp env := by
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  exact h k hk

/-- Memory keys keep their values through cuts. -/
theorem hmem_envAbs (nbytes : Nat) (inp : Nat → Byte) (env : Key → W32) (R : State E Lin)
    (h : HMem nbytes inp env) : HMem nbytes inp (envAbs env R) := fun o ho => h o ho

/-- The tracked trees of a checked slice give the next cut's variable values. -/
theorem slice_trees (prog : Array X86.Instr) (ro : Region) (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool)
    (n : Nat) (K K' : State E Lin) (trees : List (Nat × E))
    (hc : sliceCheck prog ro mem0 orc n K K' trees = true) (env : Key → W32) :
    ∀ k (hk : k < trees.length),
      envAbs env (X86.run prog ro mem0 orc n K) (.n trees[k].1) = trees[k].2.eval env := by
  intro k hk
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  exact envAbs_treeAt env _ _ _ (hc.2 _ (List.getElem_mem hk))

/-- A location tracked as its own variable keeps its value through the slice. -/
theorem slice_keep (prog : Array X86.Instr) (ro : Region) (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool)
    (n : Nat) (K K' : State E Lin) (trees : List (Nat × E))
    (hc : sliceCheck prog ro mem0 orc n K K' trees = true) (env : Key → W32) (id : Nat)
    (hm : (id, E.var (.n id)) ∈ trees) : envAbs env (X86.run prog ro mem0 orc n K) (.n id) = env (.n id) := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  exact envAbs_treeAt env _ _ _ (hc.2 _ hm)

/-- System V callee-saved general registers (rbx, rbp, r12–r15), both halves. -/
def calleeIds : List Nat := [6, 7, 10, 11, 24, 25, 26, 27, 28, 29, 30, 31]

/-! ## Output bytes at the final cut -/

/-- Output byte `o` (relative to the output base, symbol 1) is byte `b` of the stored lane held by
location variable `id`. -/
def outCell (K : State E Lin) (o id b : Nat) : Bool :=
  match lookup (⟨rOut, ⟨(o : Int), [0, 1]⟩⟩ : Addr Lin) K.mem with
  | .ok (some (.dat (.var (.n i)) b')) => i == id && b' == b
  | _ => false

theorem outCell_sound (env : Key → W32) (σ : Nat → Int) (K : State E Lin) (o id b : Nat)
    (h : outCell K o id b = true) :
    lookup (⟨rOut, σ 1 + o⟩ : Addr Int) (mapState env σ K).mem = .ok (some (.dat (env (.n id)) b)) := by
  simp only [outCell] at h
  split at h
  · rename_i i b' heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := lookup_hom env σ _ K.mem _ heq
    simp only [mapAddr, Lin.eval, dotC] at this
    simp only [mapState]
    rw [show σ 1 + (o : Int) = (o : Int) + (0 * σ 0 + (1 * σ 1 + 0)) by omega]
    exact this
  · cases h

/-- Output byte `o` after the pointer held in `base` is byte `b` of the stored lane held by
location variable `id`.  (`outCell` is the case `base = Lin.sym 1`.) -/
def outCellAt (K : State E Lin) (base : Lin) (o id b : Nat) : Bool :=
  match lookup ((⟨rOut, base⟩ : Addr Lin).plusI (o : Int)) K.mem with
  | .ok (some (.dat (.var (.n i)) b')) => i == id && b' == b
  | _ => false

theorem outCellAt_sound (env : Key → W32) (σ : Nat → Int) (K : State E Lin) (base : Lin)
    (o id b : Nat) (h : outCellAt K base o id b = true) :
    lookup (⟨rOut, base.eval σ + (o : Int)⟩ : Addr Int) (mapState env σ K).mem =
      .ok (some (.dat (env (.n id)) b)) := by
  simp only [outCellAt] at h
  split at h
  · rename_i i b' heq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := lookup_hom env σ _ K.mem _ heq
    simp only [mapAddr, Addr.plusI, Addr.plus, Lin.eval_add, Lin.eval_ofInt] at this
    simpa [mapState, mapCell, E.eval, mapAddr] using this
  · cases h

theorem assumeOk_of (σ : Nat → Int) (K : State E Lin) (A : List (Cond Lin × Bool)) (h : K.assume = A)
    (hA : ∀ p ∈ A, (mapCond σ p.1).decideC = some p.2) : AssumeOk σ K := by
  intro p hp; rw [h] at hp; exact hA p hp

/-- A stored digest lane's byte `b` is byte `b` of the big-endian word (as SHA-256 outputs it). -/
theorem byte_bswap (w : Word) (b : Nat) (hb : b < 4) :
    byteOf (SpecQ.bswap w) b = ((wordBytes w).getD b 0).zeroExtend 32 := by
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with h | h | h | h <;> subst h <;>
    simp only [byteOf, SpecQ.bswap, wordBytes, List.getD_cons_succ, List.getD_cons_zero, W32_and, W32_shr,
      W32_const] <;> bv_decide

/-- The node bytes are the bytes of the final hash words. -/
theorem node_byte (inp : Nat → Byte) (n i b : Nat) (hi : i < 8) (hb : b < 4) :
    (node (SpecQ.blk inp n)).getD (4 * i + b) 0 = (wordBytes (SpecQ.fld (SpecQ.Hr inp n 2) i)).getD b 0 := by
  rw [node_eq]
  show ((SpecQ.Hr inp n 2).toList.flatMap wordBytes).getD (4 * i + b) 0 = _
  generalize SpecQ.Hr inp n 2 = S
  obtain ⟨a, b', c, d, e, f, g, h⟩ := S
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with hi | hi | hi | hi | hi | hi | hi | hi <;>
    subst hi <;>
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with hb | hb | hb | hb <;> subst hb <;> rfl

end Hashtree.Asm
