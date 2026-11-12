import Hashtree.Asm.X86Exec

/-!
# Runs of the symbolic x86 model are sound

`run_hom`: a non-failing symbolic run whose recorded branch conditions hold denotes the
concrete run from the evaluated start state.  Needs two facts about single steps, proved here
generically over the `do` blocks of `exec`: a step never clears an error, and never forgets a
recorded condition.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Hashtree.Asm.X86
open Hashtree.Asm

section Mono
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

/-- A property of every `ok` result. -/
def EP (P : State α γ → Prop) (r : Except String (State α γ)) : Prop := ∀ s', r = .ok s' → P s'

theorem EP_pure (P : State α γ → Prop) (x : State α γ) (h : P x) : EP P (pure x) := by
  intro s' hs; cases hs; exact h

theorem EP_throw (P : State α γ → Prop) (e : String) : EP P (throw e) := by
  intro s' hs; cases hs

theorem EP_bind {β : Type} (P : State α γ → Prop) (m : Except String β) (f : β → Except String (State α γ))
    (h : ∀ a, EP P (f a)) : EP P (m >>= f) := by
  intro s' hs
  cases hm : m with
  | error e => rw [hm] at hs; cases hs
  | ok a => rw [hm] at hs; exact h a s' hs

theorem EP_ite (P : State α γ → Prop) (c : Prop) [Decidable c] (a b : Except String (State α γ))
    (ha : c → EP P a) (hb : ¬ c → EP P b) : EP P (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

/-- What a step keeps: the error, and every recorded condition. -/
def Keeps (s s' : State α γ) : Prop := s'.err = s.err ∧ ∀ p ∈ s.assume, p ∈ s'.assume

@[simp] theorem setG_assume (s : State α γ) (i : Nat) (v : Val α γ) : (s.setG i v).assume = s.assume := rfl
@[simp] theorem setG_err (s : State α γ) (i : Nat) (v : Val α γ) : (s.setG i v).err = s.err := rfl
@[simp] theorem setV_assume (s : State α γ) (i : Nat) (v : List α) : (s.setV i v).assume = s.assume := rfl
@[simp] theorem setV_err (s : State α γ) (i : Nat) (v : List α) : (s.setV i v).err = s.err := rfl
@[simp] theorem next_assume (s : State α γ) : s.next.assume = s.assume := rfl
@[simp] theorem next_err (s : State α γ) : s.next.err = s.err := rfl
@[simp] theorem setVec_assume (s : State α γ) (vex : Bool) (w d : Nat) (v : List α) :
    (setVec s vex w d v).assume = s.assume := rfl
@[simp] theorem setVec_err (s : State α γ) (vex : Bool) (w d : Nat) (v : List α) :
    (setVec s vex w d v).err = s.err := rfl
@[simp] theorem storeLane_assume (s : State α γ) (a : Addr γ) (x : α) : (storeLane s a x).assume = s.assume := rfl
@[simp] theorem storeLane_err (s : State α γ) (a : Addr γ) (x : α) : (storeLane s a x).err = s.err := rfl
@[simp] theorem storeLanes_assume : ∀ (xs : List α) (s : State α γ) (a : Addr γ), (storeLanes s a xs).assume = s.assume
  | [], _, _ => rfl
  | x :: xs, s, a => by simp only [storeLanes]; rw [storeLanes_assume xs]; rfl
@[simp] theorem storeLanes_err : ∀ (xs : List α) (s : State α γ) (a : Addr γ), (storeLanes s a xs).err = s.err
  | [], _, _ => rfl
  | x :: xs, s, a => by simp only [storeLanes]; rw [storeLanes_err xs]; rfl
@[simp] theorem storeVal_assume (s : State α γ) (a : Addr γ) (v : Val α γ) : (storeVal s a v).assume = s.assume := by
  cases v <;> rfl
@[simp] theorem storeVal_err (s : State α γ) (a : Addr γ) (v : Val α γ) : (storeVal s a v).err = s.err := by
  cases v <;> rfl
@[simp] theorem setData32_assume (s : State α γ) (d : Nat) (x : α) : (setData32 s d x).assume = s.assume := rfl
@[simp] theorem setData32_err (s : State α γ) (d : Nat) (x : α) : (setData32 s d x).err = s.err := rfl
@[simp] theorem clearFlags_assume (s : State α γ) : (clearFlags s).assume = s.assume := rfl
@[simp] theorem clearFlags_err (s : State α γ) : (clearFlags s).err = s.err := rfl
@[simp] theorem setFlags_assume (s : State α γ) (a b : γ) : (setFlags s a b).assume = s.assume := rfl
@[simp] theorem setFlags_err (s : State α γ) (a b : γ) : (setFlags s a b).err = s.err := rfl
@[simp] theorem halt_assume (s : State α γ) : (halt s).assume = s.assume := rfl
@[simp] theorem halt_err (s : State α γ) : (halt s).err = s.err := rfl

theorem branch_keeps (orc : Nat → Bool) (s : State α γ) (c : Cond γ) (t : Nat) : Keeps s (s.branch orc c t) := by
  simp only [Keeps, State.branch]
  repeat' split
  all_goals simp_all [State.next]

theorem okOr_keeps (s : State α γ) (r : Except String (State α γ)) (hs : s.err = none) (h : EP (Keeps s) r) :
    Keeps s (okOr s r) ∨ ∃ e, okOr s r = s.fail e := by
  cases r with
  | ok s' => left; exact h s' rfl
  | error e => right; exact ⟨e, rfl⟩

local macro "ep_tac" : tactic => `(tactic| (
  repeat (first
    | apply EP_bind; intro _
    | apply EP_throw
    | apply EP_ite <;> intro _
    | (apply EP_pure; simp [Keeps])
    | split)))

/-- A step keeps the error and the recorded conditions, or fails. -/
theorem exec_keeps (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr) (s : State α γ)
    (hs : s.err = none) : Keeps s (exec ro mem0 orc i s) ∨ ∃ e, exec ro mem0 orc i s = s.fail e := by
  unfold exec
  by_cases hh : s.halted = true
  · left; simp only [hh, ite_true]; exact ⟨rfl, fun _ h => h⟩
  simp only [hh, Bool.false_eq_true, ite_false]
  cases i <;> dsimp only
  case nop => left; exact ⟨rfl, fun _ h => h⟩
  case jmp => left; exact ⟨rfl, fun _ h => h⟩
  case jmpTail => left; exact ⟨rfl, fun _ h => h⟩
  case jcc c t =>
    apply okOr_keeps s _ hs
    split
    · apply EP_pure; exact branch_keeps orc s _ t
    · apply EP_throw
  case jccTail c name =>
    apply okOr_keeps s _ hs
    split
    · apply EP_ite <;> intro _
      · apply EP_pure; exact branch_keeps orc s _ _
      · apply EP_pure; exact branch_keeps orc s _ _
    · apply EP_throw
  all_goals (apply okOr_keeps s _ hs; ep_tac)

theorem fail_facts (s : State α γ) (e : String) (hs : s.err = none) :
    (s.fail e).halted = true ∧ (s.fail e).err.isSome ∧ (s.fail e).assume = s.assume := by
  simp [State.fail, hs]

theorem run_halted (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    ∀ (n : Nat) (s : State α γ), s.halted = true → run prog ro mem0 orc n s = s
  | 0, _, _ => rfl
  | n + 1, s, h => by simp [run, h]

/-- A run keeps every recorded condition, and an error once raised. -/
theorem run_keeps (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    ∀ (n : Nat) (s : State α γ), s.err = none → (run prog ro mem0 orc n s).err = none →
      ∀ p ∈ s.assume, p ∈ (run prog ro mem0 orc n s).assume
  | 0, _, _, _, p, hp => hp
  | n + 1, s, hs, hf, p, hp => by
    simp only [run] at hf ⊢
    by_cases hh : s.halted = true
    · simp only [hh, ite_true] at hf ⊢; exact hp
    simp only [hh, Bool.false_eq_true, ite_false] at hf ⊢
    cases hi : prog[s.pc]? with
    | none => simp only [hi] at hf ⊢; simp [State.fail, hs] at hf
    | some i =>
      simp only [hi] at hf ⊢
      rcases exec_keeps ro mem0 orc i s hs with ⟨he, ha⟩ | ⟨e, he⟩
      · exact run_keeps prog ro mem0 orc n _ (he.trans hs) hf p (ha p hp)
      · rw [he] at hf ⊢
        obtain ⟨h1, h2, _⟩ := fail_facts s e hs
        rw [run_halted prog ro mem0 orc n _ h1] at hf
        simp_all

end Mono

section RunHom
variable (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin) (mem0c : Addr Int → Cell W32 Int)

/-- Soundness of symbolic runs. -/
theorem run_hom (h0 : Mem0Rel env σ mem0s mem0c) (prog : Array Instr) (ro : Region) (orc orcC : Nat → Bool) :
    ∀ (n : Nat) (s : State E Lin), s.err = none → (run prog ro mem0s orc n s).err = none →
      AssumeOk σ (run prog ro mem0s orc n s) →
      run prog ro mem0c orcC n (mapState env σ s) = mapState env σ (run prog ro mem0s orc n s)
  | 0, _, _, _, _ => rfl
  | n + 1, s, hs, hf, hA => by
    simp only [run] at hf hA ⊢
    by_cases hh : s.halted = true
    · have : (mapState env σ s).halted = true := hh
      simp only [hh, this, ite_true]
    have hh' : (mapState env σ s).halted = false := by simpa [mapState] using hh
    simp only [hh, hh', Bool.false_eq_true, ite_false] at hf hA ⊢
    have hpc : (mapState env σ s).pc = s.pc := rfl
    rw [hpc]
    cases hi : prog[s.pc]? with
    | none => simp only [hi] at hf; simp [State.fail, hs] at hf
    | some i =>
      simp only [hi] at hf hA ⊢
      -- the step neither failed nor recorded a condition that fails later
      have hk := exec_keeps ro mem0s orc i s hs
      have hne : (exec ro mem0s orc i s).err = none := by
        rcases hk with ⟨he, _⟩ | ⟨e, he⟩
        · exact he.trans hs
        · rw [he] at hf
          obtain ⟨h1, h2, _⟩ := fail_facts s e hs
          rw [run_halted prog ro mem0s orc n _ h1] at hf
          simp_all
      have hA1 : AssumeOk σ (exec ro mem0s orc i s) := fun p hp =>
        hA p (run_keeps prog ro mem0s orc n _ hne hf p hp)
      rw [exec_hom env σ mem0s mem0c h0 ro orc orcC i s hne hA1]
      exact run_hom h0 prog ro orc orcC n _ hne hf hA

end RunHom

end Hashtree.Asm.X86
