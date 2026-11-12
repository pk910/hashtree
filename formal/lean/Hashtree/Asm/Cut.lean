import Hashtree.Asm.Hom

/-!
# Cuts: replacing data by variables

At a cut, every data lane of a symbolic state becomes a variable named by its location
(`abstract`); the environment `envAbs env R` gives each such variable the value its expression
had.  `abstract_sound`: the abstracted state denotes the same concrete state.  Slices are then
run from small, variable-only states, so expressions never grow beyond one slice.

Variable ids: general register `g`, half `h`: `2g + h` (< 100); vector register `i`, lane `l`:
`100 + 16i + l`; logged memory cell `j`: `1000 + j`.  Initial memory bytes keep their own keys.
-/

set_option linter.unusedVariables false

namespace Hashtree.Asm

def gId (g : Nat) (h : Nat) : Nat := 2 * g + h
def vId (i l : Nat) : Nat := 100 + 16 * i + l
def mId (j : Nat) : Nat := 1000 + j

/-- `map` with indices (structural). -/
def mapI {β δ : Type} (f : Nat → β → δ) : Nat → List β → List δ
  | _, [] => []
  | i, x :: xs => f i x :: mapI f (i + 1) xs

/-- A lane at a cut: constants stay (shuffle masks, round constants), the rest becomes the
location variable. -/
def absE (id : Nat) : E → E
  | .const c => .const c
  | _ => .var (.n id)

def absVal (g : Nat) : Val E Lin → Val E Lin
  | .num lo hi => .num (absE (gId g 0) lo) (absE (gId g 1) hi)
  | .ptr a => .ptr a

def absLanes (i : Nat) (v : List E) : List E := mapI (fun l x => absE (vId i l) x) 0 v

def absCell (j : Nat) : Cell E Lin → Cell E Lin
  | .dat x k => .dat (absE (mId j) x) k
  | .pb a k => .pb a k

/-- The cut of a state: data replaced by location variables. -/
def abstract (R : State E Lin) : State E Lin :=
  { R with
    gpr := mapI absVal 0 R.gpr
    vr := mapI absLanes 0 R.vr
    mem := mapI (fun j (p : Addr Lin × Cell E Lin) => (p.1, absCell j p.2)) 0 R.mem }

/-- The values of the location variables. -/
def envAbs (env : Key → W32) (R : State E Lin) : Key → W32
  | .n i =>
    if i < 100 then
      match R.gpr[i / 2]? with
      | some (.num lo hi) => if i % 2 = 0 then lo.eval env else hi.eval env
      | _ => 0
    else if i < 1000 then
      match R.vr[(i - 100) / 16]? with
      | some v => (v.getD ((i - 100) % 16) (.const 0)).eval env
      | none => 0
    else
      match R.mem[i - 1000]? with
      | some (_, .dat x _) => x.eval env
      | _ => 0
  | k => env k

/-- Bounds that make the location variables distinct. -/
def CutOk (R : State E Lin) : Prop :=
  R.gpr.length ≤ 50 ∧ R.vr.length ≤ 56 ∧ ∀ v ∈ R.vr, v.length ≤ 16

instance (R : State E Lin) : Decidable (CutOk R) := by unfold CutOk; infer_instance

theorem mapI_map {β δ ε : Type} (f : Nat → β → δ) (g : δ → ε) (h : β → ε)
    (hf : ∀ i x, ∀ (hi : i ≥ 0), g (f i x) = h x) : ∀ (l : List β) (i : Nat),
    (mapI f i l).map g = l.map h
  | [], _ => rfl
  | x :: xs, i => by simp only [mapI, List.map_cons, hf i x (Nat.zero_le _), mapI_map f g h hf xs (i + 1)]

/-- Elementwise version with the index (position `i + k` of `l` at offset `i`). -/
theorem mapI_map_idx {β δ ε : Type} (f : Nat → β → δ) (g : δ → ε) (h : β → ε) :
    ∀ (l : List β) (i : Nat), (∀ k (x : β), l[k]? = some x → g (f (i + k) x) = h x) →
      (mapI f i l).map g = l.map h
  | [], _, _ => rfl
  | x :: xs, i, hf => by
    simp only [mapI, List.map_cons]
    rw [show g (f i x) = h x from by simpa using hf 0 x rfl]
    rw [mapI_map_idx f g h xs (i + 1) (fun k y hy => by
      have := hf (k + 1) y (by simpa using hy)
      rwa [show i + (k + 1) = i + 1 + k by omega] at this)]

theorem absE_eval (env env' : Key → W32) (id : Nat) (x : E)
    (hid : (∀ c, x ≠ .const c) → env' (.n id) = x.eval env) : (absE id x).eval env' = x.eval env := by
  cases x <;> simp only [absE, E.eval] <;> first | rfl | exact hid (by simp)

theorem abstract_sound (env : Key → W32) (σ : Nat → Int) (R : State E Lin) (hR : CutOk R) :
    mapState (envAbs env R) σ (abstract R) = mapState env σ R := by
  obtain ⟨hg, hv, hl⟩ := hR
  simp only [mapState, abstract, State.mk.injEq, and_true, true_and]
  refine ⟨?_, ?_, ?_⟩
  · -- general registers
    apply mapI_map_idx
    intro k x hx
    have hk : k < R.gpr.length := by
      rcases Nat.lt_or_ge k R.gpr.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hx; cases hx
    cases x with
    | ptr a => rfl
    | num lo hi =>
      simp only [absVal, mapVal, envAbs, gId, Val.num.injEq]
      have c1 : 2 * (0 + k) + 0 < 100 := by omega
      have c2 : 2 * (0 + k) + 1 < 100 := by omega
      have h1 : (2 * (0 + k) + 0) / 2 = k := by omega
      have h2 : (2 * (0 + k) + 1) / 2 = k := by omega
      have m1 : (2 * (0 + k) + 0) % 2 = 0 := by omega
      have m2 : ¬ (2 * (0 + k) + 1) % 2 = 0 := by omega
      constructor
      · apply absE_eval
        intro _; simp only [envAbs, gId, c1, h1, m1, hx, ite_true]
      · apply absE_eval
        intro _; simp only [envAbs, gId, c2, h2, m2, hx, ite_true, ite_false]
  · -- vector registers
    apply mapI_map_idx
    intro k v hx
    have hk : k < R.vr.length := by
      rcases Nat.lt_or_ge k R.vr.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hx; cases hx
    have hvl : v.length ≤ 16 := hl v (List.mem_of_getElem? hx)
    simp only [absLanes]
    apply mapI_map_idx
    intro l x hlx
    have hll : l < v.length := by
      rcases Nat.lt_or_ge l v.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hlx; cases hlx
    apply absE_eval
    intro _
    simp only [envAbs, vId]
    have c1 : ¬ (100 + 16 * (0 + k) + (0 + l) < 100) := by omega
    have c2 : 100 + 16 * (0 + k) + (0 + l) < 1000 := by omega
    have e1 : (100 + 16 * (0 + k) + (0 + l) - 100) / 16 = k := by omega
    have e2 : (100 + 16 * (0 + k) + (0 + l) - 100) % 16 = l := by omega
    simp only [c1, c2, e1, e2, hx, ite_true, ite_false, List.getD_eq_getElem?_getD, hlx, Option.getD_some]
  · -- memory
    apply mapI_map_idx
    intro j p hp
    obtain ⟨a, c⟩ := p
    cases c with
    | pb _ _ => rfl
    | dat x k =>
      simp only [absCell, mapCell]
      congr 2
      apply absE_eval
      intro _
      simp only [envAbs, mId]
      have c1 : ¬ (1000 + (0 + j) < 100) := by omega
      have c2 : ¬ (1000 + (0 + j) < 1000) := by omega
      have e : 1000 + (0 + j) - 1000 = j := by omega
      simp only [c1, c2, e, hp, ite_false]

end Hashtree.Asm
