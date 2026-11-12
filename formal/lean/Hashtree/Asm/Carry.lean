import Hashtree.Asm.Chain

/-!
# Carried labels

Most labelled locations of a cut are carried unchanged through a slice (spilled message words,
untouched registers): their tree is the variable of a labelled location of the previous cut with
the same label.  `carryOk` checks a whole list of them at once (decided by the kernel), so the step
proof needs one case only per location whose value was computed in the slice.
-/

namespace Hashtree.Asm
open Hashtree.Asm.SpecQ Hashtree.Spec

/-- `Tc[i]` is `(Lk[i].1, var v)` and `L[C[i]] = (v, Lk[i].2)`. -/
def carryOk (L : List (Nat × Q)) : List (Nat × E) → List (Nat × Q) → List Nat → Bool
  | [], [], [] => true
  | t :: ts, p :: ps, i :: is =>
    decide (t.1 = p.1) &&
      (match t.2, L[i]? with
        | .var (.n v), some r => decide (r.1 = v) && decide (r.2 = p.2)
        | _, _ => false) &&
      carryOk L ts ps is
  | _, _, _ => false

theorem inv_carry (L : List (Nat × Q)) (inp : Nat → Byte) (env env' : Key → W32) (hI : Inv L inp env) :
    ∀ (Tc : List (Nat × E)) (Lk : List (Nat × Q)) (C : List Nat),
      (∀ t ∈ Tc, env' (.n t.1) = t.2.eval env) → carryOk L Tc Lk C = true → Inv Lk inp env'
  | [], [], [], _, _ => fun p hp => by cases hp
  | t :: ts, p :: ps, i :: is, hT, hc => by
    simp only [carryOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have rest := inv_carry L inp env env' hI ts ps is (fun t' ht' => hT t' (List.mem_cons_of_mem _ ht')) h3
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · have ht := hT t (List.mem_cons_self ..)
      split at h2
      · rename_i v r htv hr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        obtain ⟨hv, hq2⟩ := h2
        rw [← h1, ht, htv]
        simp only [E.eval]
        rw [← hv, ← hq2]
        exact hI r (List.mem_of_getElem? hr)
      · cases h2
    · exact rest q hq'
  | [], _ :: _, _, _, hc => by simp [carryOk] at hc
  | [], [], _ :: _, _, hc => by simp [carryOk] at hc
  | _ :: _, [], _, _, hc => by simp [carryOk] at hc
  | _ :: _, _ :: _, [], _, hc => by simp [carryOk] at hc

theorem inv_append (A B : List (Nat × Q)) (inp : Nat → Byte) (env : Key → W32)
    (ha : Inv A inp env) (hb : Inv B inp env) : Inv (A ++ B) inp env := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact ha p h
  · exact hb p h

end Hashtree.Asm
