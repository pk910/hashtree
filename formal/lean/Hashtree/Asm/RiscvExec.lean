import Hashtree.Asm.RiscvHom

/-!
# `exec_hom`: every RV64 instruction commutes with evaluation

If the symbolic step does not fail (`err = none`) and the conditions it recorded (branch
directions, count ranges) hold under `σ`, the concrete machine started in the evaluated state
ends in the evaluated result.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Hashtree.Asm.Riscv
open Hashtree.Asm

section Exec
variable (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin) (mem0c : Addr Int → Cell W32 Int)

/-- The `okOr` wrapper of `exec`: a non-failing symbolic result is an `ok` one. -/
theorem ok_wrap (s : State E Lin) (rs : Except String (State E Lin)) (rc : Except String (State W32 Int))
    (hne : (okOr s rs).err = none)
    (hr : ∀ s', rs = .ok s' → rc = .ok (mapState env σ s')) :
    okOr (mapState env σ s) rc = mapState env σ (okOr s rs) := by
  cases rs with
  | ok s' => have := hr s' rfl; subst this; rfl
  | error e =>
    exfalso
    simp only [okOr, State.fail] at hne
    split at hne <;> simp_all

/-- `ok_wrap`, also passing on the recorded conditions of the result. -/
theorem ok_wrapA (s : State E Lin) (rs : Except String (State E Lin)) (rc : Except String (State W32 Int))
    (hne : (okOr s rs).err = none) (hA : AssumeOk σ (okOr s rs))
    (hr : ∀ s', rs = .ok s' → AssumeOk σ s' → rc = .ok (mapState env σ s')) :
    okOr (mapState env σ s) rc = mapState env σ (okOr s rs) := by
  cases rs with
  | ok s' => have := hr s' rfl hA; subst this; rfl
  | error e =>
    exfalso
    simp only [okOr, State.fail] at hne
    split at hne <;> simp_all

theorem ok_of_pure {β : Type} {x y : β} (h : (pure x : Except String β) = .ok y) : x = y := by
  simpa [pure, Except.pure] using h

theorem pure_ok {β : Type} (x : β) : (pure x : Except String β) = .ok x := rfl

/-- `(do let x ← m; f x) = .ok r` with `m = .ok a`. -/
theorem bind_ok {β δ : Type} {m : Except String β} {f : β → Except String δ} {r : δ} (h : (m >>= f) = .ok r) :
    ∃ a, m = .ok a ∧ f a = .ok r := by
  cases hm : m with
  | error e => rw [hm] at h; cases h
  | ok a => rw [hm] at h; exact ⟨a, rfl, h⟩

theorem throw_eq {β : Type} (e : String) : (throw e : Except String β) = .error e := rfl

theorem exec_hom (h0 : Mem0Rel env σ mem0s mem0c) (pe : Env) (orc orcC : Nat → Bool)
    (i : Instr) (s : State E Lin)
    (hne : (exec pe mem0s orc i s).err = none) (hA : AssumeOk σ (exec pe mem0s orc i s)) :
    exec pe mem0c orcC i (mapState env σ s) = mapState env σ (exec pe mem0s orc i s) := by
  unfold exec at hne hA ⊢
  by_cases hh : s.halted = true
  · simp only [hh, ite_true]
    simp only [mapState, hh, ite_true]
  have hh' : (mapState env σ s).halted = false := by simpa [mapState] using hh
  simp only [hh', Bool.false_eq_true, ite_false]
  simp only [hh, Bool.false_eq_true, ite_false] at hne hA ⊢
  cases i with
  | nop => rfl
  | unimp => exact (fail_hom env σ s _).symm
  | lui d imm20 =>
    dsimp only
    rw [next_hom, rset_hom, sext_hom, eval_const]
    rfl
  | auipc d t =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    rw [target_hom σ pe t a ha, ok_bind]
    have := ok_of_pure h; subst this
    rw [pure_ok, next_hom, rset_hom]
    rfl
  | addi d r imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨v, hv, h⟩ := bind_ok h
    have hc : addVal (mapVal env σ (rget s r)) (.num (lanesOfInt imm : W32 × W32).1 (lanesOfInt imm).2) =
        .ok (mapVal env σ v) := addVal_hom env σ _ _ v hv
    rw [rget_hom, hc, ok_bind]
    have := ok_of_pure h; subst this
    rw [pure_ok, next_hom, rset_hom]
  | add d a b =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases ha : a = 0
    · rw [if_pos ha] at h ⊢
      obtain ⟨v, hv, h⟩ := bind_ok h
      have := ok_of_pure h; subst this
      have := ok_of_pure hv; subst this
      rw [rget_hom, pure_ok, ok_bind, pure_ok, next_hom, rset_hom]
    · rw [if_neg ha] at h ⊢
      by_cases hb : b = 0
      · rw [if_pos hb] at h ⊢
        obtain ⟨v, hv, h⟩ := bind_ok h
        have := ok_of_pure h; subst this
        have := ok_of_pure hv; subst this
        rw [rget_hom, pure_ok, ok_bind, pure_ok, next_hom, rset_hom]
      · rw [if_neg hb] at h ⊢
        obtain ⟨v, hv, h⟩ := bind_ok h
        have := ok_of_pure h; subst this
        rw [rget_hom, rget_hom, addVal_hom env σ _ _ v hv, ok_bind, pure_ok, next_hom, rset_hom]
  | bop op d a b =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨y, hy, h⟩ := bind_ok h
    have := ok_of_pure h; subst this
    rw [rget_hom, dataOf_hom env σ _ x hx, ok_bind, rget_hom, dataOf_hom env σ _ y hy, ok_bind, pure_ok,
      next_hom, rset_hom]
    simp only [mapVal, bop_hom]
  | bopi op d a imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨x, hx, h⟩ := bind_ok h
    have := ok_of_pure h; subst this
    rw [rget_hom, dataOf_hom env σ _ x hx, ok_bind, pure_ok, next_hom, rset_hom]
    simp only [mapVal, bop_hom, lanesOfInt_ev1, lanesOfInt_ev2]
  | slli d r n =>
    dsimp only at hne hA ⊢
    apply ok_wrapA env σ s _ _ hne hA
    intro s' h hA'
    by_cases hn : n ≥ 64
    · rw [if_pos hn] at h; cases h
    · rw [if_neg hn] at h; rw [if_neg hn, rget_hom]
      exact slliV_hom env σ s d _ n s' h hA'
  | srai d r n =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hn : n ≥ 64
    · rw [if_pos hn] at h; cases h
    · rw [if_neg hn] at h; rw [if_neg hn]
      obtain ⟨x, hx, h⟩ := bind_ok h
      have := ok_of_pure h; subst this
      rw [rget_hom, dataOf_hom env σ _ x hx, ok_bind, pure_ok, next_hom, rset_hom]
      simp only [mapVal]
      rw [← sra64_hom env x n]
  | wop op d r n =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hn : n ≥ 32
    · rw [if_pos hn] at h; cases h
    · rw [if_neg hn] at h; rw [if_neg hn]
      obtain ⟨x, hx, h⟩ := bind_ok h
      have := ok_of_pure h; subst this
      rw [rget_hom, dataOf_hom env σ _ x hx, ok_bind, pure_ok, next_hom, rset_hom, sext_hom, wop_hom]
  | addw d a b =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨y, hy, h⟩ := bind_ok h
    have := ok_of_pure h; subst this
    rw [rget_hom, dataOf_hom env σ _ x hx, ok_bind, rget_hom, dataOf_hom env σ _ y hy, ok_bind, pure_ok,
      next_hom, rset_hom, sext_hom, eval_add]
    rfl
  | rev8 d r =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨x, hx, h⟩ := bind_ok h
    have := ok_of_pure h; subst this
    rw [rget_hom, dataOf_hom env σ _ x hx, ok_bind, pure_ok, next_hom, rset_hom]
    simp only [mapVal, bswap32_hom]
  | sha op d r =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨x, hx, h⟩ := bind_ok h
    have := ok_of_pure h; subst this
    rw [rget_hom, dataOf_hom env σ _ x hx, ok_bind, pure_ok, next_hom, rset_hom, sext_hom, shaF_hom]
  | lwu d b off =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨w, hw, h⟩ := bind_ok h
    have := ok_of_pure h; subst this
    rw [ea_hom env σ s b off a ha, ok_bind, loadLane_hom env σ mem0s mem0c h0 s a w hw, ok_bind, pure_ok,
      next_hom, rset_hom]
    rfl
  | ld d b off =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨v, hv, h⟩ := bind_ok h
    have := ok_of_pure h; subst this
    rw [ea_hom env σ s b off a ha, ok_bind, loadVal_hom env σ mem0s mem0c h0 s a v hv, ok_bind, pure_ok,
      next_hom, rset_hom]
  | sw src b off =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨u, hu, h⟩ := bind_ok h
    cases u
    obtain ⟨x, hx, h⟩ := bind_ok h
    have := ok_of_pure h; subst this
    rw [ea_hom env σ s b off a ha, ok_bind, checkWritable_hom σ pe a () hu, ok_bind, rget_hom,
      dataOf_hom env σ _ x hx, ok_bind, pure_ok, next_hom, storeLane_hom]
  | sd src b off =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨u, hu, h⟩ := bind_ok h
    cases u
    have := ok_of_pure h; subst this
    rw [ea_hom env σ s b off a ha, ok_bind, checkWritable_hom σ pe a () hu, ok_bind, rget_hom, pure_ok,
      next_hom, storeVal_hom]
  | br c a b t =>
    dsimp only at hne hA ⊢
    apply ok_wrapA env σ s _ _ hne hA
    intro s' h hA'
    obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨e, he, h⟩ := bind_ok h
    have := ok_of_pure h; subst this
    rw [rget_hom, ctlOf_hom env σ _ x hx, ok_bind, rget_hom, ctlOf_hom env σ _ y hy, ok_bind,
      eqCond_hom σ x y e he, ok_bind, pure_ok]
    have hc : mapCond σ (if c = .eq then e else .not e) =
        if c = .eq then mapCond σ e else .not (mapCond σ e) := by split <;> rfl
    rw [← hc, branch_hom env σ orc orcC s _ t hA']
  | jal d t =>
    dsimp only
    rw [setPc_hom, link_hom]
  | jalr d r off =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨t, ht, h⟩ := bind_ok h
    rw [rget_hom, ctlOf_hom env σ _ t ht, ok_bind, ← mapAddr_plusI]
    exact jumpTo_hom env σ pe s d _ s' h

end Exec

end Hashtree.Asm.Riscv
