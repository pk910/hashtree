import Hashtree.Asm.RunAgree

/-!
# Single-state step shape, body exit, and never-written registers

Companions of `Asm/RunAgree` about one run: `exec_shape` (a step either fails — `err` set, pc
and general registers untouched — or keeps `err`, keeps `halted` unless the instruction is a
`ret`/tail jump, and changes only the general registers in `dsts i`), `run_err_none` (`err` is
sticky), `run_exit` (a run from inside a body region whose static successors stay inside it or
land on its exit pc, and which later halts without error, reaches the exit pc unhalted after
some fuel, staying inside before), and `run_preserve` (a register no body instruction writes
keeps its entry value while the run stays in the body).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Hashtree.Asm.RunExit

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.BodyReads Hashtree.Asm.RunAgree

/-- Instructions whose non-failing step can halt the machine. -/
def halts : Instr → Bool
  | .ret => true
  | .jmpTail _ => true
  | .jccTail _ _ => true
  | _ => false

/-- Instructions that write memory. -/
def writesMem : Instr → Bool
  | .vstore _ _ _ => true
  | .movst _ _ _ => true
  | .push _ => true
  | _ => false

section Engine
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

/-! ### Projections of the writers -/

theorem getG_setG_of_ne (s : State α γ) (d q : Nat) (v : Val α γ) (h : ¬ q = d) :
    (s.setG d v).getG q = s.getG q := by
  simp only [State.getG, State.setG, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (fun h' => h h'.symm)]

theorem getG_next (s : State α γ) (q : Nat) : s.next.getG q = s.getG q := rfl
theorem getG_setV (s : State α γ) (i : Nat) (v : List α) (q : Nat) : (s.setV i v).getG q = s.getG q := rfl
theorem getG_setVec (s : State α γ) (vex : Bool) (w d : Nat) (v : List α) (q : Nat) :
    (setVec s vex w d v).getG q = s.getG q := rfl
theorem getG_storeLane (s : State α γ) (a : Addr γ) (x : α) (q : Nat) : (storeLane s a x).getG q = s.getG q := rfl
theorem getG_storeLanes (s : State α γ) (a : Addr γ) (xs : List α) (q : Nat) :
    (storeLanes s a xs).getG q = s.getG q := by
  induction xs generalizing s a with
  | nil => rfl
  | cons x xs ih => simp only [storeLanes, ih, getG_storeLane]
theorem getG_storeVal (s : State α γ) (a : Addr γ) (v : Val α γ) (q : Nat) :
    (storeVal s a v).getG q = s.getG q := by
  cases v with
  | num lo hi => simp only [storeVal, getG_storeLane]
  | ptr p => rfl
theorem getG_clearFlags (s : State α γ) (q : Nat) : (clearFlags s).getG q = s.getG q := rfl
theorem getG_setFlags (s : State α γ) (a b : γ) (q : Nat) : (setFlags s a b).getG q = s.getG q := rfl
theorem getG_halt (s : State α γ) (q : Nat) : (halt s).getG q = s.getG q := rfl
theorem getG_branch (s : State α γ) (orc : Nat → Bool) (c : Cond γ) (t : Nat) (q : Nat) :
    (s.branch orc c t).getG q = s.getG q := by
  simp only [State.branch]
  split <;> (try split) <;> (try split) <;> rfl

theorem err_storeLanes (s : State α γ) (a : Addr γ) (xs : List α) : (storeLanes s a xs).err = s.err := by
  induction xs generalizing s a with
  | nil => rfl
  | cons x xs ih => simp only [storeLanes, ih, storeLane]
theorem err_storeVal (s : State α γ) (a : Addr γ) (v : Val α γ) : (storeVal s a v).err = s.err := by
  cases v <;> simp [storeVal, storeLane]
theorem err_branch (s : State α γ) (orc : Nat → Bool) (c : Cond γ) (t : Nat) :
    (s.branch orc c t).err = s.err := by
  simp only [State.branch]
  split <;> (try split) <;> (try split) <;> rfl
theorem halted_storeLanes (s : State α γ) (a : Addr γ) (xs : List α) : (storeLanes s a xs).halted = s.halted := by
  induction xs generalizing s a with
  | nil => rfl
  | cons x xs ih => simp only [storeLanes, ih, storeLane]
theorem halted_storeVal (s : State α γ) (a : Addr γ) (v : Val α γ) : (storeVal s a v).halted = s.halted := by
  cases v <;> simp [storeVal, storeLane]
theorem halted_branch (s : State α γ) (orc : Nat → Bool) (c : Cond γ) (t : Nat) :
    (s.branch orc c t).halted = s.halted := by
  simp only [State.branch]
  split <;> (try split) <;> (try split) <;> rfl

theorem fail_err (s : State α γ) (e : String) : (s.fail e).err ≠ none := by
  unfold State.fail
  split
  · rename_i h; simpa [Option.isSome_iff_ne_none] using h
  · simp

theorem fail_getG (s : State α γ) (e : String) (q : Nat) : (s.fail e).getG q = s.getG q := by
  unfold State.fail; split <;> rfl

theorem fail_mem (s : State α γ) (e : String) : (s.fail e).mem = s.mem := by
  unfold State.fail; split <;> rfl

theorem mem_branch (s : State α γ) (orc : Nat → Bool) (c : Cond γ) (t : Nat) :
    (s.branch orc c t).mem = s.mem := by
  simp only [State.branch]
  split <;> (try split) <;> (try split) <;> rfl

/-! ### The lifting -/

/-- A non-failing step result keeps `err`, keeps `halted` unless `hl`, and touches only `D`. -/
def ShapeE (s : State α γ) (D : List Nat) (hl wm : Bool) : Except String (State α γ) → Prop
  | .ok x => x.err = s.err ∧ (x.halted = s.halted ∨ hl = true) ∧ (∀ q, q ∉ D → x.getG q = s.getG q) ∧
      (wm = false → x.mem = s.mem)
  | .error _ => True

variable {s : State α γ} {D : List Nat} {hl wm : Bool}

theorem ShapeE.bind {β : Type} (m : Except String β) {f : β → Except String (State α γ)}
    (h : ∀ x, m = .ok x → ShapeE s D hl wm (f x)) : ShapeE s D hl wm (m >>= f) := by
  cases m with
  | error e => exact trivial
  | ok x => exact h x rfl

theorem ShapeE.pure {x : State α γ}
    (h : x.err = s.err ∧ (x.halted = s.halted ∨ hl = true) ∧ (∀ q, q ∉ D → x.getG q = s.getG q) ∧
      (wm = false → x.mem = s.mem)) :
    ShapeE s D hl wm (pure x) := h

theorem ShapeE.throw (e : String) : ShapeE s D hl wm (throw e : Except String (State α γ)) := trivial

theorem okOr_shape {r : Except String (State α γ)} (h : ShapeE s D hl wm r) :
    ((okOr s r).err ≠ none ∧ (okOr s r).pc = s.pc ∧ (∀ q, (okOr s r).getG q = s.getG q) ∧
        (okOr s r).mem = s.mem) ∨
      ((okOr s r).err = s.err ∧ ((okOr s r).halted = s.halted ∨ hl = true) ∧
        (∀ q, q ∉ D → (okOr s r).getG q = s.getG q) ∧ (wm = false → (okOr s r).mem = s.mem)) := by
  cases r with
  | error e => exact Or.inl ⟨fail_err s e, fail_pc s e, fail_getG s e, fail_mem s e⟩
  | ok x => exact Or.inr h

local macro "shape_w" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [State.next, State.setG, State.setV, setVec, setData32, clearFlags, setFlags, halt,
      storeLane, err_storeLanes, err_storeVal, err_branch]
  · simp only [State.next, State.setG, State.setV, setVec, setData32, clearFlags, setFlags, halt,
      storeLane, halted_storeLanes, halted_storeVal, halted_branch, true_or, or_true]
  · intro q hq
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, not_or, or_false,
      not_false_eq_true, and_true] at hq
    simp only [getG_next, getG_setV, getG_setVec, getG_storeLane, getG_storeLanes, getG_storeVal,
      getG_clearFlags, getG_setFlags, getG_halt, getG_branch, setData32, getG_setG_of_ne, hq,
      not_false_eq_true]
  · intro hw
    first
      | (simp only [writesMem] at hw; exact absurd hw (by decide))
      | simp only [State.next, State.setG, State.setV, setVec, setData32, clearFlags, setFlags, halt,
          mem_branch]))

local macro "shape_lift" : tactic => `(tactic| (
  repeat first
    | (apply ShapeE.bind; intro _ _)
    | (apply ShapeE.pure; shape_w)
    | exact ShapeE.throw _
    | split))

/-- One step: failure (`err` set, pc and general registers untouched), or success (`err` kept,
`halted` kept unless the instruction halts, only `dsts i` written). -/
theorem exec_shape (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr)
    (s : State α γ) (hh : s.halted = false) :
    ((exec ro mem0 orc i s).err ≠ none ∧ (exec ro mem0 orc i s).pc = s.pc ∧
        (∀ q, (exec ro mem0 orc i s).getG q = s.getG q) ∧ (exec ro mem0 orc i s).mem = s.mem) ∨
      ((exec ro mem0 orc i s).err = s.err ∧
        ((exec ro mem0 orc i s).halted = s.halted ∨ halts i = true) ∧
        (∀ q, q ∉ dsts i → (exec ro mem0 orc i s).getG q = s.getG q) ∧
        (writesMem i = false → (exec ro mem0 orc i s).mem = s.mem)) := by
  unfold exec
  have hh' : ¬ s.halted = true := by simp [hh]
  rw [ite_eq_right hh']
  cases i with
  | nop => exact Or.inr ⟨rfl, Or.inl rfl, fun _ _ => rfl, fun _ => rfl⟩
  | jmp t => exact Or.inr ⟨rfl, Or.inl rfl, fun _ _ => rfl, fun _ => rfl⟩
  | jmpTail name => exact Or.inr ⟨rfl, Or.inr rfl, fun _ _ => rfl, fun _ => rfl⟩
  | jcc c t =>
    dsimp only
    simp only [dsts]
    apply okOr_shape
    cases s.flags with
    | none => exact ShapeE.throw _
    | some p =>
      obtain ⟨a, b⟩ := p
      exact ShapeE.pure ⟨err_branch _ _ _ _, Or.inl (halted_branch _ _ _ _), fun q _ => getG_branch _ _ _ _ q,
        fun _ => mem_branch _ _ _ _⟩
  | jccTail c name =>
    dsimp only
    simp only [dsts]
    apply okOr_shape
    cases s.flags with
    | none => exact ShapeE.throw _
    | some p =>
      obtain ⟨a, b⟩ := p
      dsimp only
      split
      · exact ShapeE.pure ⟨err_branch _ _ _ _, Or.inr rfl, fun q _ => getG_branch _ _ _ _ q,
          fun _ => mem_branch _ _ _ _⟩
      · exact ShapeE.pure ⟨err_branch _ _ _ _, Or.inl (halted_branch _ _ _ _), fun q _ => getG_branch _ _ _ _ q,
          fun _ => mem_branch _ _ _ _⟩
  | ret =>
    dsimp only
    simp only [dsts]
    apply okOr_shape
    cases s.getG rsp with
    | num _ _ => exact ShapeE.throw _
    | ptr sp =>
      dsimp only
      apply ShapeE.bind; intro v _
      split
      · refine ShapeE.pure ⟨rfl, Or.inr rfl, fun q hq => ?_, fun _ => rfl⟩
        simp only [List.mem_singleton, List.not_mem_nil, List.mem_cons, or_false] at hq
        exact getG_setG_of_ne _ _ _ _ hq
      · exact ShapeE.throw _
  | pop r =>
    dsimp only
    simp only [dsts]
    apply okOr_shape
    cases s.getG rsp with
    | num _ _ => exact ShapeE.throw _
    | ptr sp =>
      dsimp only
      apply ShapeE.bind; intro v _
      refine ShapeE.pure ⟨rfl, Or.inl rfl, fun q hq => ?_, fun _ => rfl⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, not_or, or_false] at hq
      rw [getG_next, getG_setG_of_ne _ _ _ _ hq.2, getG_setG_of_ne _ _ _ _ hq.1]
  | push r =>
    dsimp only
    simp only [dsts]
    apply okOr_shape
    cases s.getG rsp with
    | num _ _ => exact ShapeE.throw _
    | ptr sp =>
      dsimp only
      refine ShapeE.pure ⟨by simp only [State.next, State.setG, err_storeVal],
        Or.inl (by simp only [State.next, State.setG, halted_storeVal]), fun q hq => ?_,
        fun hw => by simp [writesMem] at hw⟩
      simp only [List.mem_singleton, List.not_mem_nil, List.mem_cons, or_false] at hq
      rw [getG_next, getG_setG_of_ne _ _ _ _ hq, getG_storeVal]
  | movst w m src =>
    dsimp only
    simp only [dsts]
    apply okOr_shape
    apply ShapeE.bind; intro a _
    split
    · exact ShapeE.pure ⟨by simp only [State.next, err_storeVal],
        Or.inl (by simp only [State.next, halted_storeVal]), fun q _ => by rw [getG_next, getG_storeVal],
        fun hw => by simp [writesMem] at hw⟩
    · cases s.getG src with
      | num lo hi => exact ShapeE.pure ⟨rfl, Or.inl rfl, fun q _ => rfl, fun hw => by simp [writesMem] at hw⟩
      | ptr _ => exact ShapeE.throw _
  | _ =>
    dsimp only
    simp only [dsts]
    apply okOr_shape
    shape_lift

/-! ### Runs -/

theorem run_halted_eq (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (n : Nat) (s : State α γ) (hh : s.halted = true) : run prog ro mem0 orc n s = s := by
  cases n with
  | zero => rfl
  | succ n => simp only [run, hh, ite_true]

theorem run_succ (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (n : Nat) (s : State α γ) (hh : s.halted = false) (i : Instr) (hi : prog[s.pc]? = some i) :
    run prog ro mem0 orc (n + 1) s = run prog ro mem0 orc n (exec ro mem0 orc i s) := by
  simp only [run, hh, Bool.false_eq_true, ite_false, hi]

theorem exec_err_none (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr)
    (s : State α γ) (h : (exec ro mem0 orc i s).err = none) : s.err = none := by
  by_cases hh : s.halted = true
  · unfold exec at h; rwa [ite_eq_left hh] at h
  · rcases exec_shape ro mem0 orc i s (by simpa using hh) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd h h1
    · rwa [h1] at h

/-- `err` is sticky: a run that ends without error never had one. -/
theorem run_err_none (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    ∀ (n : Nat) (s : State α γ), (run prog ro mem0 orc n s).err = none →
      ∀ k, k ≤ n → (run prog ro mem0 orc k s).err = none
  | 0, s, h, k, hk => by rw [Nat.le_zero.mp hk]; exact h
  | n + 1, s, h, k, hk => by
    by_cases hh : s.halted = true
    · rw [run_halted_eq _ _ _ _ _ _ hh] at h; rw [run_halted_eq _ _ _ _ _ _ hh]; exact h
    · have hh' : s.halted = false := by simpa using hh
      cases hi : prog[s.pc]? with
      | none =>
        exfalso
        simp only [run, hh', Bool.false_eq_true, ite_false, hi] at h
        exact fail_err s _ h
      | some i =>
        rw [run_succ _ _ _ _ _ _ hh' i hi] at h
        cases k with
        | zero => exact exec_err_none ro mem0 orc i s (run_err_none prog ro mem0 orc n _ h 0 (Nat.zero_le _))
        | succ k =>
          rw [run_succ _ _ _ _ _ _ hh' i hi]
          exact run_err_none prog ro mem0 orc n _ h k (Nat.le_of_succ_le_succ hk)

/-- A body region: static successors stay inside `[lo, hi)` or land on `hi`, and no instruction
halts. -/
def Body (prog : Array Instr) (lo hi : Nat) : Prop :=
  ∀ p i, lo ≤ p → p < hi → prog[p]? = some i →
    halts i = false ∧ ∀ q, q ∈ succs p i → (lo ≤ q ∧ q < hi) ∨ q = hi

/-- The exit fuel: a run from inside the body that halts without error after `N` steps reaches
`hi` unhalted after some `n ≤ N`, staying inside and unhalted before. -/
theorem run_exit (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    {lo hi : Nat} (hb : Body prog lo hi) :
    ∀ (N : Nat) (s : State α γ), lo ≤ s.pc → s.pc < hi → s.halted = false →
      (run prog ro mem0 orc N s).halted = true → (run prog ro mem0 orc N s).err = none →
      ∃ n, n ≤ N ∧
        (∀ k, k < n → lo ≤ (run prog ro mem0 orc k s).pc ∧ (run prog ro mem0 orc k s).pc < hi ∧
          (run prog ro mem0 orc k s).halted = false) ∧
        (run prog ro mem0 orc n s).pc = hi ∧ (run prog ro mem0 orc n s).halted = false
  | 0, s, _, _, hh, hN, _ => by simp only [run] at hN; rw [hh] at hN; cases hN
  | N + 1, s, hlo, hhi, hh, hN, herr => by
    cases hi' : prog[s.pc]? with
    | none =>
      exfalso
      simp only [run, hh, Bool.false_eq_true, ite_false, hi'] at herr
      exact fail_err s _ herr
    | some i =>
      have hstep := run_succ prog ro mem0 orc N s hh i hi'
      rw [hstep] at hN herr
      obtain ⟨hhalts, hsucc⟩ := hb s.pc i hlo hhi hi'
      have herr0 := run_err_none prog ro mem0 orc N _ herr 0 (Nat.zero_le _)
      rcases exec_shape ro mem0 orc i s hh with ⟨h1, _⟩ | ⟨_, h2, _, _⟩
      · exact absurd herr0 h1
      have hnh : (exec ro mem0 orc i s).halted = false := by
        rcases h2 with h2 | h2
        · rwa [hh] at h2
        · rw [hhalts] at h2; cases h2
      have hpc := (exec_agree ro mem0 orc i (R := srcs i) (s1 := s) (s2 := s)
        ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ h => h)).2
      have hin : (lo ≤ (exec ro mem0 orc i s).pc ∧ (exec ro mem0 orc i s).pc < hi) ∨
          (exec ro mem0 orc i s).pc = hi := by
        rcases hpc with hpc | ⟨hpc, _⟩
        · exact Or.inl (by rw [hpc]; exact ⟨hlo, hhi⟩)
        · exact hsucc _ hpc
      rcases hin with ⟨hlo', hhi'⟩ | hexit
      · obtain ⟨n, hn, hk, hpcn, hhn⟩ := run_exit prog ro mem0 orc hb N _ hlo' hhi' hnh hN herr
        refine ⟨n + 1, Nat.succ_le_succ hn, fun k hk' => ?_, ?_, ?_⟩
        · cases k with
          | zero => exact ⟨hlo, hhi, hh⟩
          | succ k => rw [run_succ prog ro mem0 orc k s hh i hi']; exact hk k (Nat.lt_of_succ_lt_succ hk')
        · rw [run_succ prog ro mem0 orc n s hh i hi']; exact hpcn
        · rw [run_succ prog ro mem0 orc n s hh i hi']; exact hhn
      · refine ⟨1, Nat.succ_le_succ (Nat.zero_le _), fun k hk => ?_, ?_, ?_⟩
        · have : k = 0 := by omega
          subst this; exact ⟨hlo, hhi, hh⟩
        · rw [run_succ prog ro mem0 orc 0 s hh i hi']; exact hexit
        · rw [run_succ prog ro mem0 orc 0 s hh i hi']; exact hnh

/-- A register no body instruction writes keeps its value while the run stays inside the body
without error. -/
theorem run_preserve (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    {lo hi : Nat} (r : Nat) (hw : ∀ p i, lo ≤ p → p < hi → prog[p]? = some i → r ∉ dsts i) :
    ∀ (n : Nat) (s : State α γ),
      (∀ k, k < n → lo ≤ (run prog ro mem0 orc k s).pc ∧ (run prog ro mem0 orc k s).pc < hi ∧
        (run prog ro mem0 orc k s).halted = false) →
      (run prog ro mem0 orc n s).err = none →
      (run prog ro mem0 orc n s).getG r = s.getG r
  | 0, s, _, _ => rfl
  | n + 1, s, hk, herr => by
    obtain ⟨hlo, hhi, hh⟩ := hk 0 (Nat.succ_pos _)
    simp only [run] at hlo hhi hh
    cases hi' : prog[s.pc]? with
    | none =>
      exfalso
      simp only [run, hh, Bool.false_eq_true, ite_false, hi'] at herr
      exact fail_err s _ herr
    | some i =>
      rw [run_succ prog ro mem0 orc n s hh i hi'] at herr ⊢
      have herr0 := run_err_none prog ro mem0 orc n _ herr 0 (Nat.zero_le _)
      rcases exec_shape ro mem0 orc i s hh with ⟨h1, _⟩ | ⟨_, _, h3, _⟩
      · exact absurd herr0 h1
      rw [run_preserve prog ro mem0 orc r hw n _ (fun k hk' => by
            rw [← run_succ prog ro mem0 orc k s hh i hi']; exact hk (k + 1) (Nat.succ_lt_succ hk')) herr]
      exact h3 r (hw s.pc i hlo hhi hi')

/-- A run whose executed instructions do not write memory leaves the log alone (failures keep it
too). -/
theorem run_nowrite (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    ∀ (n : Nat) (s : State α γ),
      (∀ k, k < n → (run prog ro mem0 orc k s).halted = false →
        ∀ i, prog[(run prog ro mem0 orc k s).pc]? = some i → writesMem i = false) →
      (run prog ro mem0 orc n s).mem = s.mem
  | 0, _, _ => rfl
  | n + 1, s, hk => by
    by_cases hh : s.halted = true
    · rw [run_halted_eq _ _ _ _ _ _ hh]
    · have hh' : s.halted = false := by simpa using hh
      cases hi : prog[s.pc]? with
      | none => simp only [run, hh', Bool.false_eq_true, ite_false, hi, fail_mem]
      | some i =>
        rw [run_succ prog ro mem0 orc n s hh' i hi]
        have hw : writesMem i = false := hk 0 (Nat.succ_pos _) hh' i hi
        have hm : (exec ro mem0 orc i s).mem = s.mem := by
          rcases exec_shape ro mem0 orc i s hh' with ⟨_, _, _, h4⟩ | ⟨_, _, _, h4⟩
          · exact h4
          · exact h4 hw
        rw [run_nowrite prog ro mem0 orc n _ (fun k hk' hhk j hj => by
          rw [← run_succ prog ro mem0 orc k s hh' i hi] at hhk hj
          exact hk (k + 1) (Nat.succ_lt_succ hk') hhk j hj), hm]

end Engine

end Hashtree.Asm.RunExit
