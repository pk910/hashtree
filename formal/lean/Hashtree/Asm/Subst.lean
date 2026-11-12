import Hashtree.Asm.Hom

/-!
# Renaming the control symbols of a symbolic state

`K.substL τ` replaces symbol `i` by the linear form `τ[i]` (symbols beyond `τ` stay) in every
address, pointer and flag of `K`.  The concrete state it denotes under `σ` is the one `K` denotes
under the evaluated substitution: a loop head reached with advanced pointers is the loop-head cut
under shifted symbols.  Lane expressions do not involve symbols and are untouched.
-/

namespace Hashtree.Asm

def tauAt (τ : List Lin) (i : Nat) : Lin := τ.getD i (Lin.sym i)

def substC (τ : List Lin) : List Int → Nat → Lin
  | [], _ => Lin.ofInt 0
  | c :: cs, i => (Lin.smul c (tauAt τ i)).add (substC τ cs (i + 1))

/-- Drop trailing zero coefficients. -/
def trimC : List Int → List Int
  | [] => []
  | x :: xs => let t := trimC xs; if x = 0 ∧ t = [] then [] else x :: t

def Lin.trim (l : Lin) : Lin := ⟨l.k, trimC l.c⟩

def Lin.subst (τ : List Lin) (l : Lin) : Lin := ((Lin.ofInt l.k).add (substC τ l.c 0)).trim

def Addr.substL (τ : List Lin) (a : Addr Lin) : Addr Lin := ⟨a.region, a.off.subst τ⟩

def Val.substL (τ : List Lin) : Val E Lin → Val E Lin
  | .num lo hi => .num lo hi
  | .ptr a => .ptr (a.substL τ)

def Cell.substL (τ : List Lin) : Cell E Lin → Cell E Lin
  | .dat x k => .dat x k
  | .pb a k => .pb (a.substL τ) k

def State.substL (τ : List Lin) (K : State E Lin) : State E Lin :=
  { K with
    gpr := K.gpr.map (Val.substL τ)
    flags := K.flags.map (fun p => (p.1.subst τ, p.2.subst τ))
    mem := K.mem.map (fun p => (p.1.substL τ, p.2.substL τ))
    assume := [] }

/-- The evaluated substitution. -/
def sigmaOf (τ : List Lin) (σ : Nat → Int) : Nat → Int := fun i => (tauAt τ i).eval σ

theorem Lin.eval_sym (σ : Nat → Int) (i : Nat) : (Lin.sym i).eval σ = σ i := by
  simp only [Lin.sym, Lin.eval]
  suffices h : ∀ j, dotC (List.replicate i 0 ++ [1]) j σ = σ (j + i) by
    rw [h 0]; simp
  intro j
  induction i generalizing j with
  | zero => simp [dotC]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, dotC]
    rw [ih (j + 1)]; simp only [Int.zero_mul, Int.zero_add]
    congr 1; omega

theorem eval_substC (τ : List Lin) (σ : Nat → Int) : ∀ (cs : List Int) (i : Nat),
    (substC τ cs i).eval σ = dotC cs i (sigmaOf τ σ)
  | [], _ => by simp [substC, dotC, Lin.eval, Lin.ofInt]
  | c :: cs, i => by
    simp only [substC, dotC]
    have h1 := Lin.eval_add σ (Lin.smul c (tauAt τ i)) (substC τ cs (i + 1))
    have h2 := Lin.eval_smul σ c (tauAt τ i)
    simp only [Ctl.add, Ctl.smul] at h1 h2
    rw [h1, h2, eval_substC τ σ cs (i + 1)]
    rfl

theorem dotC_trimC (σ : Nat → Int) : ∀ (c : List Int) (i : Nat), dotC (trimC c) i σ = dotC c i σ
  | [], _ => rfl
  | x :: xs, i => by
    simp only [trimC]
    have ih := dotC_trimC σ xs (i + 1)
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      rw [h2] at ih
      simp only [dotC, h1, Int.zero_mul, Int.zero_add]
      rw [← ih]; rfl
    · simp only [dotC, ih]

theorem Lin.eval_trim (σ : Nat → Int) (l : Lin) : l.trim.eval σ = l.eval σ := by
  simp only [Lin.trim, Lin.eval, dotC_trimC]

theorem Lin.eval_subst (τ : List Lin) (σ : Nat → Int) (l : Lin) :
    (l.subst τ).eval σ = l.eval (sigmaOf τ σ) := by
  simp only [Lin.subst, Lin.eval_trim]
  have h1 := Lin.eval_add σ (Lin.ofInt l.k) (substC τ l.c 0)
  simp only [Ctl.add] at h1
  rw [h1, eval_substC]
  simp [Lin.eval, Lin.ofInt, dotC]

theorem mapAddr_subst (τ : List Lin) (σ : Nat → Int) (a : Addr Lin) :
    mapAddr σ (a.substL τ) = mapAddr (sigmaOf τ σ) a := by
  simp [mapAddr, Addr.substL, Lin.eval_subst]

theorem mapState_subst (env : Key → W32) (τ : List Lin) (σ : Nat → Int) (K : State E Lin) :
    mapState env σ (K.substL τ) = mapState env (sigmaOf τ σ) K := by
  simp only [mapState, State.substL, List.map_map, Option.map_map]
  congr 1
  · apply List.map_congr_left
    intro v _
    cases v <;> simp [mapVal, Val.substL, mapAddr_subst]
  · cases K.flags <;> simp [Lin.eval_subst]
  · apply List.map_congr_left
    intro p _
    obtain ⟨a, c⟩ := p
    cases c <;> simp [mapCell, Cell.substL, mapAddr_subst]

end Hashtree.Asm
