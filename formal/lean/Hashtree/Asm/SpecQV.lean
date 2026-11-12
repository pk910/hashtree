import Hashtree.Asm.X86Sym
import Hashtree.Asm.Chain

/-!
# Fast symbolic initial memory for kernels with large rodata (multi-lane x86 kernels)

`mem0s` reads rodata with `List.getD`; in a `decide +kernel` slice check every rodata byte read
walks the list from its head (the AVX-512 kernel's rodata is 9 KB: 64 reads cost ~40 s / 5 GB).
`mem0q` is the same memory with the rodata split into chunks (`chunksF`), so a read walks at most
`o / k + k` cells; `mem0q_eq` proves the two equal, so slice checks run on `mem0q` and the final
theorems are stated with `mem0s`.
-/

namespace Hashtree.Asm.X86Sym
open Hashtree.Asm Hashtree.Asm.X86

/-- `l` cut into chunks of `k` (fuel `f` chunks). -/
def chunksF (k : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | f + 1, l => match l with
    | [] => []
    | _ :: _ => l.take k :: chunksF k f (l.drop k)

/-- Byte `o` of the chunked list. -/
def chunkGet (k : Nat) (C : List (List Nat)) (o : Nat) : Nat := (C.getD (o / k) []).getD (o % k) 0

theorem chunkGet_eq (k : Nat) (hk : 0 < k) :
    ∀ (f : Nat) (l : List Nat), l.length ≤ f * k → ∀ o, chunkGet k (chunksF k f l) o = l.getD o 0
  | 0, l, hf, o => by
    have h0 : l.length = 0 := by rw [Nat.zero_mul] at hf; omega
    have : l = [] := List.eq_nil_of_length_eq_zero h0
    subst this; simp [chunksF, chunkGet]
  | f + 1, l, hf, o => by
    match l with
    | [] => simp [chunksF, chunkGet]
    | x :: xs =>
      simp only [chunksF]
      by_cases ho : o < k
      · have h1 : o / k = 0 := Nat.div_eq_of_lt ho
        have h2 : o % k = o := Nat.mod_eq_of_lt ho
        simp only [chunkGet, h1, h2, List.getD_cons_zero]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ho, ite_true]
      · have h1 : o / k = (o - k) / k + 1 := by
          rw [Nat.div_eq_sub_div hk (by omega)]
        have h2 : o % k = (o - k) % k := by
          rw [Nat.mod_eq_sub_mod (by omega)]
        have ih := chunkGet_eq k hk f ((x :: xs).drop k)
          (by simp only [List.length_drop]; simp only [Nat.succ_mul] at hf; omega) (o - k)
        simp only [chunkGet] at ih ⊢
        rw [h1, h2, List.getD_cons_succ, ih]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        congr 2; omega

/-- `mem0s` with chunked rodata. -/
def mem0q (ro : Region) (C : List (List Nat)) (sp0 : Int) : Addr Lin → Cell E Lin := fun a =>
  if a.region = rIn then .dat (.var (.m a.region a.off)) 0
  else match a.off.asInt with
    | some o =>
      if a.region = ro then .dat (.const (BitVec.ofNat 32 (chunkGet 64 C o.toNat))) 0
      else if a.region = rStack then
        if sp0 ≤ o ∧ o < sp0 + 8 then .pb ⟨rRet, Lin.ofInt 0⟩ (o - sp0).toNat
        else poison
      else poison
    | none => poison

theorem mem0q_eq (ro : Region) (rodata : List Nat) (sp0 : Int) (C : List (List Nat)) (f : Nat)
    (hC : C = chunksF 64 f rodata) (hf : rodata.length ≤ f * 64) :
    mem0q ro C sp0 = mem0s ro rodata sp0 := by
  subst hC
  have hg : ∀ o, chunkGet 64 (chunksF 64 f rodata) o = rodata.getD o 0 := chunkGet_eq 64 (by decide) f rodata hf
  funext a
  unfold mem0q mem0s
  by_cases h : a.region = rIn
  · simp only [h, ite_true]
  · simp only [h, ite_false]
    cases a.off.asInt with
    | none => rfl
    | some o => simp only [hg]

end Hashtree.Asm.X86Sym

/-!
## Invariants as conjunction chains

`Inv L` quantifies over the list; proving or using it entry by entry indexes a list of several
hundred entries per use (`L[k]`, ~0.5 s each for the wide kernels). `InvC` is the same invariant
unfolded into a right-nested conjunction (destructured once with `obtain`), and `InvT` pairs the
tracked trees of a slice with the next cut's labels, so a step is proved by one anonymous-constructor
term.
-/

namespace Hashtree.Asm
open Hashtree.Asm.SpecQ Hashtree.Spec Hashtree.Asm.X86

def InvC (inp : Nat → Byte) (env : Key → W32) : List (Nat × Q) → Prop
  | [] => True
  | p :: ps => env (.n p.1) = qv inp p.2 ∧ InvC inp env ps

theorem invC_iff (inp : Nat → Byte) (env : Key → W32) : ∀ L, InvC inp env L ↔ Inv L inp env
  | [] => by simp [InvC, Inv]
  | p :: ps => by
    simp only [InvC, Inv, List.mem_cons, forall_eq_or_imp]
    rw [invC_iff inp env ps]; rfl

/-- Trees `T` (of the next cut's variables, evaluated in this cut's environment `env`) against the
next cut's labels `L`. -/
def InvT (inp : Nat → Byte) (env : Key → W32) : List (Nat × E) → List (Nat × Q) → Prop
  | t :: ts, l :: ls => (t.1 = l.1 ∧ t.2.eval env = qv inp l.2) ∧ InvT inp env ts ls
  | [], [] => True
  | _, _ => False

theorem invC_of_trees (inp : Nat → Byte) (env env' : Key → W32) :
    ∀ (T : List (Nat × E)) (L : List (Nat × Q)), (∀ p ∈ T, env' (.n p.1) = p.2.eval env) →
      InvT inp env T L → InvC inp env' L
  | [], [], _, _ => trivial
  | t :: ts, l :: ls, hT, h => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨?_, invC_of_trees inp env env' ts ls (fun p hp => hT p (List.mem_cons_of_mem _ hp)) h3⟩
    rw [← h1, hT t (List.mem_cons_self ..), h2]
  | [], _ :: _, _, h => absurd h id
  | _ :: _, [], _, h => absurd h id

/-- The tracked trees of a checked slice give the next cut's variable values (membership form). -/
theorem slice_trees_mem (prog : Array Instr) (ro : Region) (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool)
    (n : Nat) (K K' : State E Lin) (trees : List (Nat × E))
    (hc : sliceCheck prog ro mem0 orc n K K' trees = true) (env : Key → W32) :
    ∀ p ∈ trees, envAbs env (run prog ro mem0 orc n K) (.n p.1) = p.2.eval env := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  exact fun p hp => envAbs_treeAt env _ _ _ (hc.2 p hp)

end Hashtree.Asm
