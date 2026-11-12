import Hashtree.Asm.Cut
import Hashtree.Asm.Subst
import Hashtree.Asm.X86Frame

/-!
# Restarting an RV64 proof at a loop-head cut

At a loop head reached again, the state is the loop-head cut under advanced symbols, with all
of the earlier memory writes moved into the frame.  For x86 the reopened cut's data lanes equal
the loop-head cut's (`mapState_reached` via `KF_shape`); with 32-bit data lanes the body can
leave arbitrary constants in dead registers, so here the reopening only requires the *pointer*
registers to match the loop head's (under the substitution) and the loop head's remaining
registers to hold their own location variables.  Those variables are evaluated by `envAbs` of
the segment's own run, so whatever the segment computed (a constant, a mask, a shuffle) is
exactly the value the loop head's variable denotes.

`GprLive` is the relation, `gprLiveRel` its decidable checker (generated per segment), and
`mapState_reached_vars` the reopening theorem.
-/

set_option linter.unusedVariables false

namespace Hashtree.Asm
open Hashtree.Asm.X86

/-- The general registers of the end cut `K` match the loop-head cut `K0` where that cut has
pointers (under the substitution `τ`), and `K0`'s remaining registers are the location variables
of their own positions. -/
def GprLive (K K0 : State E Lin) (τ : List Lin) : Prop :=
  K.gpr.length = K0.gpr.length ∧
    ∀ (i : Nat) (v : Val E Lin), K0.gpr[i]? = some v →
      (match v with
        | .ptr a => K.gpr[i]? = some (.ptr (a.substL τ))
        | .num lo hi => lo = .var (.n (2 * i)) ∧ hi = .var (.n (2 * i + 1)) ∧
            ∃ x y, K.gpr[i]? = some (.num x y))

/-- An option of a value that is numeric. -/
def optIsNum : Option (Val E Lin) → Bool
  | some (.num _ _) => true
  | _ => false

theorem optIsNum_sound : ∀ (o : Option (Val E Lin)), optIsNum o = true →
    ∃ w, o = some w ∧ ∃ x y, w = .num x y
  | some (.num x y), _ => ⟨_, rfl, x, y, rfl⟩
  | some (.ptr a), h => by simp [optIsNum] at h
  | none, h => by simp [optIsNum] at h

/-- Decidable checker for `GprLive`. -/
def gprLiveRel (K K0 : State E Lin) (τ : List Lin) : Bool :=
  (K.gpr.length == K0.gpr.length) &&
    (List.range K0.gpr.length).all (fun i =>
      match K0.gpr[i]? with
      | some (.ptr a) => K.gpr[i]? == some (.ptr (a.substL τ))
      | some (.num lo hi) =>
          (lo == (.var (.n (2 * i)))) && (hi == (.var (.n (2 * i + 1)))) && optIsNum K.gpr[i]?
      | none => K.gpr[i]? == none)

theorem getElem?_some_lt {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length :=
  (List.getElem?_eq_some_iff.mp h).choose

theorem getElem?_none_bound {α : Type} {l : List α} {i : Nat} (h : l[i]? = none) :
    l.length ≤ i :=
  List.getElem?_eq_none_iff.mp h

theorem gprLiveRel_sound {K K0 : State E Lin} {τ : List Lin} (h : gprLiveRel K K0 τ = true) :
    GprLive K K0 τ := by
  simp only [gprLiveRel, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨by simpa using hlen, ?_⟩
  intro i v hv
  have hi : i < K0.gpr.length := getElem?_some_lt hv
  have hf := hall i hi
  rw [hv] at hf
  cases v with
  | ptr a =>
    simpa using hf
  | num lo hi =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨⟨h1, h2⟩, h3⟩ := hf
    obtain ⟨w, how, x, y, hw⟩ := optIsNum_sound _ h3
    exact ⟨h1, h2, x, y, how.trans (by rw [hw])⟩

theorem gpr_map_live (env : Key → W32) (σ' : Nat → Int) (R K0 : State E Lin) (τ : List Lin)
    (hR : R.gpr.length = 32) (h0 : K0.gpr.length = 32) (h : GprLive R K0 τ) :
    R.gpr.map (mapVal env σ') = K0.gpr.map (mapVal (envAbs env R) (sigmaOf τ σ')) := by
  obtain ⟨hlen, hg⟩ := h
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map]
  cases hk : K0.gpr[i]? with
  | none =>
    have hi : K0.gpr.length ≤ i := getElem?_none_bound hk
    have hri : R.gpr[i]? = none := by
      rw [List.getElem?_eq_none (by omega)]
    simp only [hri, Option.map_none]
  | some v =>
    have hgv := hg i v hk
    cases v with
    | ptr a =>
      simp only [hgv, Option.map_some, mapVal]
      rw [mapAddr_subst]
    | num lo hi =>
      obtain ⟨h1, h2, x, y, hxy⟩ := hgv
      have hi32 : i < 32 := by
        have hlt := getElem?_some_lt hk
        omega
      have e1 : envAbs env R (.n (2 * i)) = x.eval env := by
        simp only [envAbs, show 2 * i < 100 by omega, show 2 * i / 2 = i by omega,
          show 2 * i % 2 = 0 by omega, hxy]
        simp
      have e2 : envAbs env R (.n (2 * i + 1)) = y.eval env := by
        simp only [envAbs, show 2 * i + 1 < 100 by omega, show (2 * i + 1) / 2 = i by omega,
          show (2 * i + 1) % 2 ≠ 0 by omega, hxy]
        simp
      simp only [hxy, h1, h2, Option.map_some, mapVal]
      simp only [E.eval]
      rw [e1, e2]

/-- A segment's end cut, restarted as the loop-head cut `K0` under the substitution `τ`. -/
theorem mapState_reached_vars (env : Key → W32) (σ' : Nat → Int) (R K0 : State E Lin)
    (τ : List Lin) (hR : CutOk R) (h0 : K0.gpr.length = 32) (hgl : GprLive R K0 τ)
    (hpc : R.pc = K0.pc) (hhl : R.halted = K0.halted) (herr : R.err = K0.err)
    (htail : R.tail = K0.tail) (hvrR : R.vr = []) (hvrK : K0.vr = [])
    (hflR : R.flags = none) (hflK : K0.flags = none) (hm : K0.mem = []) :
    mapState (envAbs env R) σ' (abstract R) =
      fr (R.mem.map (fun p => (mapAddr σ' p.1, mapCell env σ' p.2)))
        (mapState (envAbs env R) (sigmaOf τ σ') K0) := by
  have hR32 : R.gpr.length = 32 := by have := hgl.1; omega
  have hgl' := gpr_map_live env σ' R K0 τ hR32 h0 hgl
  rw [abstract_sound env σ' R hR]
  rw [show mapState env σ' R =
      fr (R.mem.map (fun p => (mapAddr σ' p.1, mapCell env σ' p.2)))
        (mapState env σ' { R with mem := [] }) from rfl]
  congr 1
  simp only [mapState, hvrR, hvrK, hflR, hflK, hm, List.map_nil, Option.map_none]
  rw [hgl']
  simp only [hpc, hhl, herr, htail]

theorem sigmaOf_nil (σ : Nat → Int) : sigmaOf [] σ = σ := by
  funext i
  simp only [sigmaOf, tauAt]
  exact Lin.eval_sym σ i

end Hashtree.Asm
