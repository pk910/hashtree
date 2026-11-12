import Hashtree.Spec

/-!
# Characterisations of the schedule and the rounds

`W M t` (the schedule word) satisfies the recurrence of FIPS 180-4 §6.2.2 step 1, and the
state after `n` rounds (`rs`) unfolds one round at a time.  Implementations are compared with
the specification through these two facts.
-/

namespace Hashtree.Spec

/-- Schedule word `W_t` of block `M`. -/
def W (M : List Word) (t : Nat) : Word := (schedule M).getD t 0

/-- One schedule extension step (the body of `schedule`'s fold). -/
def schedStep (W : List Word) (i : Nat) : List Word :=
  W ++ [sigma1 (W.getD (i + 16 - 2) 0) + W.getD (i + 16 - 7) 0 + sigma0 (W.getD (i + 16 - 15) 0) +
    W.getD (i + 16 - 16) 0]

/-- The schedule after `n` extension steps. -/
def sch (M : List Word) (n : Nat) : List Word := (List.range n).foldl schedStep M

theorem schedule_eq (M : List Word) : schedule M = sch M 48 := rfl

theorem getD_append_left {l₁ l₂ : List Word} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {l₁ l₂ : List Word} {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem sch_succ (M : List Word) (n : Nat) : sch M (n + 1) = schedStep (sch M n) n := by
  simp [sch, List.range_succ, List.foldl_append]

theorem sch_length (M : List Word) (n : Nat) : (sch M n).length = M.length + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sch_succ]; simp [schedStep, ih]; omega

/-- Entries already present are never changed by later steps. -/
theorem sch_stable (M : List Word) (n m t : Nat) (hnm : n ≤ m) (ht : t < M.length + n) :
    (sch M m).getD t 0 = (sch M n).getD t 0 := by
  induction m with
  | zero => have : n = 0 := by omega
            subst this; rfl
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with h | h
    · rw [sch_succ, schedStep, getD_append_left (by rw [sch_length]; omega), ih (by omega)]
    · have : n = m + 1 := by omega
      subst this; rfl

theorem sch_new (M : List Word) (n : Nat) :
    (sch M (n + 1)).getD (M.length + n) 0 =
      sigma1 ((sch M n).getD (n + 16 - 2) 0) + (sch M n).getD (n + 16 - 7) 0 +
        sigma0 ((sch M n).getD (n + 16 - 15) 0) + (sch M n).getD (n + 16 - 16) 0 := by
  rw [sch_succ, schedStep, getD_append_right (by rw [sch_length]; omega)]
  simp [sch_length]

theorem W_lt16 (M : List Word) (hM : M.length = 16) (t : Nat) (ht : t < 16) : W M t = M.getD t 0 := by
  simp only [W, schedule_eq]
  rw [sch_stable M 0 48 t (by omega) (by omega)]
  rfl

/-- The message-schedule recurrence (FIPS 180-4 §6.2.2 step 1). -/
theorem W_rec (M : List Word) (hM : M.length = 16) (t : Nat) (h1 : 16 ≤ t) (h2 : t < 64) :
    W M t = sigma1 (W M (t - 2)) + W M (t - 7) + sigma0 (W M (t - 15)) + W M (t - 16) := by
  have key : ∀ u, u < t → W M u = (sch M (t - 16)).getD u 0 := by
    intro u hu
    simp only [W, schedule_eq]
    exact sch_stable M (t - 16) 48 u (by omega) (by omega)
  have hW : W M t = (sch M (t - 16 + 1)).getD (M.length + (t - 16)) 0 := by
    simp only [W, schedule_eq]
    rw [sch_stable M (t - 16 + 1) 48 _ (by omega) (by omega)]
    congr 1; omega
  rw [hW, sch_new, key (t - 2) (by omega), key (t - 7) (by omega), key (t - 15) (by omega),
    key (t - 16) (by omega)]
  have e1 : t - 16 + 16 - 2 = t - 2 := by omega
  have e2 : t - 16 + 16 - 7 = t - 7 := by omega
  have e3 : t - 16 + 16 - 15 = t - 15 := by omega
  have e4 : t - 16 + 16 - 16 = t - 16 := by omega
  rw [e1, e2, e3, e4]

/-- The state after the first `n` rounds. -/
def rs (s : State) (M : List Word) (n : Nat) : State :=
  (List.range n).foldl (fun s t => s.round (K t) (W M t)) s

theorem rs_zero (s : State) (M : List Word) : rs s M 0 = s := rfl

theorem rs_succ (s : State) (M : List Word) (n : Nat) :
    rs s M (n + 1) = (rs s M n).round (K n) (W M n) := by
  simp [rs, List.range_succ, List.foldl_append]

theorem compress_eq (H : State) (M : List Word) : compress H M = H.add (rs H M 64) := rfl

end Hashtree.Spec
