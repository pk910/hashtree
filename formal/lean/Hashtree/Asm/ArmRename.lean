import Hashtree.Asm.Arm
import Hashtree.Asm.ArmRun

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Tail-symbol rename (linux/arm64 -> darwin/arm64)

The Mach-O port of a kernel is the same instruction stream with the leading underscores of the
external symbols.  Inside the model the only place a symbol appears is the name of a tail call
(`Instr.bTail`); every other operand is pc- or register-relative.  This module proves that
renaming the tail names of the instruction stream and of the machine state commutes with
execution, so a run of the linux model transfers to the darwin model.  The observations
(`outBytes`, `abiObs`) read no `tail` field at all.
-/

namespace Hashtree.Asm.ArmRename
open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun

/-- Rename the symbol of a tail call; every other instruction is unchanged. -/
def renameInstr (f : String → String) : Instr → Instr
  | .bTail n => .bTail (f n)
  | i => i

/-- Rename the pending tail name of a state.  No instruction reads `tail` (only `bTail` writes
it; `run` and `runChain` read it), so this is the only state component a rename touches. -/
def renameState {α γ : Type} (f : String → String) (s : State α γ) : State α γ :=
  { s with tail := s.tail.map f }

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
  (f : String → String)

/-! ## The rename commutes with the state accessors and setters -/

@[simp] theorem renameState_gpr (s : State α γ) : (renameState f s).gpr = s.gpr := rfl
@[simp] theorem renameState_vr (s : State α γ) : (renameState f s).vr = s.vr := rfl
@[simp] theorem renameState_flags (s : State α γ) : (renameState f s).flags = s.flags := rfl
@[simp] theorem renameState_mem (s : State α γ) : (renameState f s).mem = s.mem := rfl
@[simp] theorem renameState_pc (s : State α γ) : (renameState f s).pc = s.pc := rfl
@[simp] theorem renameState_halted (s : State α γ) : (renameState f s).halted = s.halted := rfl
@[simp] theorem renameState_tail (s : State α γ) : (renameState f s).tail = s.tail.map f := rfl
@[simp] theorem renameState_err (s : State α γ) : (renameState f s).err = s.err := rfl
@[simp] theorem renameState_assume (s : State α γ) : (renameState f s).assume = s.assume := rfl

theorem renameState_mk (gpr : List (Val α γ)) (vr : List (List α)) (flags : Option (γ × γ))
    (mem : List (Addr γ × Cell α γ)) (pc : Nat) (halted : Bool) (tail : Option String)
    (err : Option String) (assume : List (Cond γ × Bool)) :
    renameState f ⟨gpr, vr, flags, mem, pc, halted, tail, err, assume⟩ =
      ⟨gpr, vr, flags, mem, pc, halted, tail.map f, err, assume⟩ := rfl

@[simp] theorem renameState_getG (s : State α γ) (i : Nat) :
    (renameState f s).getG i = s.getG i := rfl

@[simp] theorem renameState_getV (s : State α γ) (i : Nat) :
    (renameState f s).getV i = s.getV i := rfl

@[simp] theorem renameState_getQ (s : State α γ) (i : Nat) :
    getQ (renameState f s) i = getQ s i := rfl

@[simp] theorem renameState_getD (s : State α γ) (i : Nat) :
    getD (renameState f s) i = getD s i := rfl

@[simp] theorem renameState_setG (s : State α γ) (i : Nat) (v : Val α γ) :
    renameState f (s.setG i v) = (renameState f s).setG i v := rfl

@[simp] theorem renameState_setV (s : State α γ) (i : Nat) (v : List α) :
    renameState f (s.setV i v) = (renameState f s).setV i v := rfl

@[simp] theorem renameState_setW (s : State α γ) (i : Nat) (x : α) :
    renameState f (setW s i x) = setW (renameState f s) i x := rfl

@[simp] theorem renameState_setQ (s : State α γ) (i : Nat) (v : List α) :
    renameState f (setQ s i v) = setQ (renameState f s) i v := rfl

@[simp] theorem renameState_setD (s : State α γ) (i : Nat) (v : List α) :
    renameState f (setD s i v) = setD (renameState f s) i v := rfl

@[simp] theorem renameState_next (s : State α γ) :
    renameState f s.next = (renameState f s).next := rfl

@[simp] theorem renameState_halt (s : State α γ) :
    renameState f (halt s) = halt (renameState f s) := rfl

@[simp] theorem renameState_setFlags (s : State α γ) (a b : γ) :
    renameState f (setFlags s a b) = setFlags (renameState f s) a b := rfl

@[simp] theorem renameState_storeLane (s : State α γ) (a : Addr γ) (x : α) :
    renameState f (storeLane s a x) = storeLane (renameState f s) a x := rfl

@[simp] theorem renameState_ite (h : Prop) [Decidable h] (a b : State α γ) :
    renameState f (if h then a else b) = if h then renameState f a else renameState f b := by
  by_cases hh : h <;> simp [hh]

@[simp] theorem renameState_fail (s : State α γ) (msg : String) :
    renameState f (s.fail msg) = (renameState f s).fail msg := by
  unfold State.fail
  by_cases h : s.err.isSome <;> simp [h, renameState]

@[simp] theorem renameState_branch (orc : Nat → Bool) (s : State α γ) (c : Cond γ) (t : Nat) :
    renameState f (s.branch orc c t) = (renameState f s).branch orc c t := by
  unfold State.branch
  by_cases h : c.decideC.isNone <;> simp [h] <;> split <;> rfl

theorem renameState_storeLanes (s : State α γ) (a : Addr γ) (xs : List α) :
    renameState f (storeLanes s a xs) = storeLanes (renameState f s) a xs := by
  induction xs generalizing s a with
  | nil => rfl
  | cons x xs ih =>
    simp only [storeLanes]
    rw [ih]
    rfl

theorem renameState_storeVal (s : State α γ) (a : Addr γ) (v : Val α γ) :
    renameState f (storeVal s a v) = storeVal (renameState f s) a v := by
  cases v with
  | num lo hi => simp [storeVal]
  | ptr p => simp [storeVal, renameState]

theorem renameState_writeBack (s : State α γ) (n : Nat) (a : Option (Addr γ)) :
    renameState f (writeBack s n a) = writeBack (renameState f s) n a := by
  cases a <;> rfl

/-! ## Helper reads are blind to `tail` -/

@[simp] theorem readCell_rename (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) :
    readCell mem0 (renameState f s) a = readCell mem0 s a := rfl

@[simp] theorem loadLane_rename (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) :
    loadLane mem0 (renameState f s) a = loadLane mem0 s a := rfl

@[simp] theorem loadLanes_rename (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ)
    (n : Nat) : loadLanes mem0 (renameState f s) a n = loadLanes mem0 s a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [loadLanes, ih]

@[simp] theorem loadVal_rename (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) :
    loadVal mem0 (renameState f s) a = loadVal mem0 s a := rfl

@[simp] theorem getC_rename (s : State α γ) (i : Nat) :
    getC (renameState f s) i = getC s i := rfl

@[simp] theorem getW_rename (s : State α γ) (i : Nat) :
    getW (renameState f s) i = getW s i := rfl

@[simp] theorem getX_rename (s : State α γ) (i : Nat) :
    getX (renameState f s) i = getX s i := rfl

@[simp] theorem baseAddr_rename (s : State α γ) (n : Nat) :
    baseAddr (renameState f s) n = baseAddr s n := rfl

@[simp] theorem addrWB_rename (s : State α γ) (n : Nat) (i : Idx) :
    addrWB (renameState f s) n i = addrWB s n i := rfl

/-! ## Except algebra: mapping the rename through binds and composition -/

theorem except_bind_pure {β δ : Type} (h : β → δ) (x : Except String β) :
    (x >>= fun a => pure (h a)) = h <$> x := by
  cases x <;> rfl

theorem map_rename_comp {β : Type} (h : β → State α γ) (x : Except String β) :
    (h <$> x).map (renameState f) = ((renameState f) ∘ h) <$> x := by
  cases x <;> rfl

theorem except_bind_map {β : Type} (g : β → β) {δ : Type}
    (x : Except String β) (k : β → Except String δ) :
    (x.map g) >>= k = x >>= fun a => k (g a) := by
  cases x <;> rfl

theorem except_map_bind {β δ : Type} (g : δ → δ)
    (x : Except String β) (k : β → Except String δ) :
    (x >>= k).map g = x >>= fun a => (k a).map g := by
  cases x <;> rfl

theorem okOr_map_rename (s : State α γ) (r : Except String (State α γ)) :
    renameState f (okOr s r) = okOr (renameState f s) (r.map (renameState f)) := by
  cases r with
  | ok s' => rfl
  | error e =>
    show renameState f (s.fail e) = (renameState f s).fail e
    rw [renameState_fail]

@[simp] theorem okOr_ok (s s' : State α γ) : okOr s (.ok s') = s' := rfl
@[simp] theorem okOr_error (s : State α γ) (e : String) : okOr s (.error e) = s.fail e := rfl

theorem okOr_ite (c : Prop) [Decidable c] (a b : Except String (State α γ)) (s : State α γ) :
    okOr s (if c then a else b) = if c then okOr s a else okOr s b := by
  by_cases h : c <;> simp [h]

@[simp] theorem pure_ok {β : Type} (x : β) : (pure x : Except String β) = .ok x := rfl
@[simp] theorem throw_error {β : Type} (e : String) : (throw e : Except String β) = .error e := rfl
@[simp] theorem except_map_ok {β δ : Type} (g : β → δ) (x : β) :
    (Except.ok x : Except String β).map g = .ok (g x) := rfl
@[simp] theorem except_map_error {β δ : Type} (g : β → δ) (e : String) :
    (Except.error e : Except String β).map g = .error e := rfl

theorem except_map_ite {β δ : Type} (g : β → δ) (c : Prop) [Decidable c]
    (a b : Except String β) :
    (if c then a else b).map g = if c then a.map g else b.map g := by
  by_cases h : c <;> simp [h]

theorem writeBack_rename_out (s : State α γ) (n : Nat) (a : Option (Addr γ)) :
    writeBack (renameState f s) n a = renameState f (writeBack s n a) :=
  (renameState_writeBack f s n a).symm

/-! ## The state-building steps commute with the rename -/

theorem loadReg_rename (mem0 : Addr γ → Cell α γ) (s0 s : State α γ) (sz : Sz) (t : Nat)
    (a : Addr γ) :
    loadReg mem0 (renameState f s0) (renameState f s) sz t a
      = Except.map (renameState f) (loadReg mem0 s0 s sz t a) := by
  cases sz with
  | w =>
    simp only [loadReg]
    by_cases h : t = sp
    · simp only [h, ite_true]; rfl
    · simp only [h, ite_false, except_bind_pure]
      exact (map_rename_comp f (fun x => setW s t x) (loadLane mem0 s0 a)).symm
  | x =>
    simp only [loadReg]
    by_cases h : t = sp
    · simp only [h, ite_true]; rfl
    · simp only [h, ite_false, except_bind_pure]
      exact (map_rename_comp f (fun v => s.setG t v) (loadVal mem0 s0 a)).symm
  | d =>
    simp only [loadReg, except_bind_pure]
    exact (map_rename_comp f (fun v => setD s t v) (loadLanes mem0 s0 a 2)).symm
  | q =>
    simp only [loadReg, except_bind_pure]
    exact (map_rename_comp f (fun v => setQ s t v) (loadLanes mem0 s0 a 4)).symm

theorem storeReg_rename (s0 s : State α γ) (sz : Sz) (t : Nat) (a : Addr γ) :
    storeReg (renameState f s0) (renameState f s) sz t a
      = Except.map (renameState f) (storeReg s0 s sz t a) := by
  cases sz with
  | w =>
    simp only [storeReg, except_bind_pure]
    exact (map_rename_comp f (fun x => storeLane s a x) (getW s0 t)).symm
  | x =>
    simp only [storeReg]
    by_cases h : t = sp
    · simp only [h, ite_true]; rfl
    · simp only [h, ite_false]
      rw [← renameState_storeVal]
      rfl
  | d =>
    simp only [storeReg]
    rw [← renameState_storeLanes]
    rfl
  | q =>
    simp only [storeReg]
    rw [← renameState_storeLanes]
    rfl

theorem ld1Step_rename (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) (t : Nat)
    (st : State α γ) (j : Nat) :
    ld1Step mem0 (renameState f s) a t (renameState f st) j
      = Except.map (renameState f) (ld1Step mem0 s a t st j) := by
  simp only [ld1Step, except_bind_pure]
  exact (map_rename_comp f (fun v => setQ st ((t + j) % 32) v)
    (loadLanes mem0 s (a.plusI (16 * (j : Int))) 4)).symm

theorem ld4Step_rename (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) (t e : Nat)
    (st : State α γ) (r : Nat) :
    ld4Step mem0 (renameState f s) a t e (renameState f st) r
      = Except.map (renameState f) (ld4Step mem0 s a t e st r) := by
  simp only [ld4Step, except_bind_pure]
  exact (map_rename_comp f
    (fun x => setQ st ((t + r) % 32) ((getQ st ((t + r) % 32)).set e x))
    (loadLane mem0 s (a.plusI (4 * (r : Int))))).symm

@[simp] theorem st1Step_rename (s : State α γ) (a : Addr γ) (t : Nat) (st : State α γ) (j : Nat) :
    st1Step (renameState f s) a t (renameState f st) j
      = renameState f (st1Step s a t st j) := rfl

@[simp] theorem st4Step_rename (s : State α γ) (a : Addr γ) (t e : Nat) (st : State α γ) (r : Nat) :
    st4Step (renameState f s) a t e (renameState f st) r
      = renameState f (st4Step s a t e st r) := rfl

theorem foldlM_rename (step : State α γ → State α γ → Nat → Except String (State α γ))
    (hstep : ∀ s0 st j, step (renameState f s0) (renameState f st) j
      = Except.map (renameState f) (step s0 st j))
    (s0 init : State α γ) (l : List Nat) :
    l.foldlM (step (renameState f s0)) (renameState f init)
      = Except.map (renameState f) (l.foldlM (step s0) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldlM_cons]
    rw [hstep]
    rw [except_bind_map (renameState f) (step s0 init j)
      (fun b => l.foldlM (step (renameState f s0)) b)]
    simp only [ih]
    rw [← except_map_bind (renameState f) (step s0 init j)
      (fun a => l.foldlM (step s0) a)]

theorem foldl_rename (step : State α γ → State α γ → Nat → State α γ)
    (hstep : ∀ s0 st j, step (renameState f s0) (renameState f st) j
      = renameState f (step s0 st j))
    (s0 init : State α γ) (l : List Nat) :
    l.foldl (step (renameState f s0)) (renameState f init)
      = renameState f (l.foldl (step s0) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons j l ih => simp [List.foldl, hstep, ih]

theorem foldlM_ld1_rename (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) (t : Nat)
    (init : State α γ) (l : List Nat) :
    l.foldlM (ld1Step mem0 (renameState f s) a t) (renameState f init)
      = Except.map (renameState f) (l.foldlM (ld1Step mem0 s a t) init) :=
  foldlM_rename f (fun s0 st j => ld1Step mem0 s0 a t st j)
    (fun s0 st j => ld1Step_rename f mem0 s0 a t st j) s init l

theorem foldlM_ld4_rename (mem0 : Addr γ → Cell α γ) (s : State α γ) (a : Addr γ) (t e : Nat)
    (init : State α γ) (l : List Nat) :
    l.foldlM (ld4Step mem0 (renameState f s) a t e) (renameState f init)
      = Except.map (renameState f) (l.foldlM (ld4Step mem0 s a t e) init) :=
  foldlM_rename f (fun s0 st j => ld4Step mem0 s0 a t e st j)
    (fun s0 st j => ld4Step_rename f mem0 s0 a t e st j) s init l

theorem foldl_st1_rename (s : State α γ) (a : Addr γ) (t : Nat)
    (init : State α γ) (l : List Nat) :
    l.foldl (st1Step (renameState f s) a t) (renameState f init)
      = renameState f (l.foldl (st1Step s a t) init) :=
  foldl_rename f (fun s0 st j => st1Step s0 a t st j)
    (fun s0 st j => st1Step_rename f s0 a t st j) s init l

theorem foldl_st4_rename (s : State α γ) (a : Addr γ) (t e : Nat)
    (init : State α γ) (l : List Nat) :
    l.foldl (st4Step (renameState f s) a t e) (renameState f init)
      = renameState f (l.foldl (st4Step s a t e) init) :=
  foldl_rename f (fun s0 st j => st4Step s0 a t e st j)
    (fun s0 st j => st4Step_rename f s0 a t e st j) s init l

/-! ## One instruction -/

theorem exec_rename (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr)
    (s : State α γ) :
    exec ro mem0 orc (renameInstr f i) (renameState f s)
      = renameState f (exec ro mem0 orc i s) := by
  by_cases hs : s.halted = true
  · simp [exec, hs]
  cases i <;>
    simp [exec, hs, renameInstr, renameState_ite, renameState_mk,
      loadReg_rename, storeReg_rename,
      foldlM_ld1_rename, foldlM_ld4_rename, foldl_st1_rename, foldl_st4_rename,
      writeBack_rename_out,
      except_bind_map, except_map_bind, okOr_map_rename,
      except_map_ite, okOr_ite] <;>
    first
    | rfl
    | (split <;> simp_all)

/-! ## Whole-program execution -/

theorem run_rename (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ)
    (orc : Nat → Bool) :
    ∀ (n : Nat) (s : State α γ),
      run (prog.map (renameInstr f)) ro mem0 orc n (renameState f s)
        = renameState f (run prog ro mem0 orc n s) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    by_cases hs : s.halted = true
    · simp [run, hs]
    · simp only [run]
      cases hp : prog[s.pc]? with
      | none => simp_all
      | some i => simp_all [exec_rename]

/-- Rename a program (its symbol and its instruction stream). -/
def renameProg (f : String → String) (p : Prog) : Prog :=
  { p with name := f p.name, code := p.code.map (renameInstr f) }

/-- Rename a program list. -/
def renameProgs (f : String → String) (progs : List Prog) : List Prog :=
  progs.map (renameProg f)

theorem run_renameProg (p : Prog) (m0 : Addr Int → Cell W32 Int) (fuel : Nat) (s : CS) :
    run (renameProg f p).code (renameProg f p).ro m0 (fun _ => false) fuel (renameState f s)
      = renameState f (run p.code p.ro m0 (fun _ => false) fuel s) := by
  show run (p.code.map (renameInstr f)) p.ro m0 (fun _ => false) fuel (renameState f s)
    = renameState f (run p.code p.ro m0 (fun _ => false) fuel s)
  exact run_rename f p.code p.ro m0 (fun _ => false) fuel s

theorem fail_err (s : CS) (msg : String) : (s.fail msg).err ≠ none := by
  unfold State.fail
  cases s.err <;> simp

/-- Running a chain of renamed programs, from a renamed state, follows the renamed chain and
returns the renamed final state and the renamed path.  Requires that the linux chain never
looks up a name it does not have (its result has no error); the error strings of failed lookups
are not renamed. -/
theorem runChain_rename (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (fuel : Nat) :
    ∀ (hops : Nat) (name : String) (s : CS),
      (∀ (n : String) (p : Prog), progs.find? (·.name = n) = some p →
        (renameProgs f progs).find? (·.name = f n) = some (renameProg f p)) →
      (runChain progs m0 fuel hops name s).1.err = none →
      runChain (renameProgs f progs) m0 fuel hops (f name) (renameState f s)
        = (renameState f (runChain progs m0 fuel hops name s).1,
           (runChain progs m0 fuel hops name s).2.map f) := by
  intro hops
  induction hops with
  | zero =>
    intro name s hfind hok
    simp only [runChain] at hok
    exact absurd hok (fail_err s _)
  | succ hops ih =>
    intro name s hfind hok
    cases hf : progs.find? (·.name = name) with
    | none =>
      simp only [runChain, hf] at hok
      exact absurd hok (fail_err s _)
    | some p =>
      have hf2 := hfind name p hf
      simp only [runChain, hf, hf2, run_renameProg, renameState_tail, renameState_err] at hok ⊢
      generalize hs' : run p.code p.ro m0 (fun _ => false) fuel s = s' at hok ⊢
      cases ht : s'.tail with
      | none => cases he : s'.err <;> simp_all
      | some t =>
        cases he : s'.err with
        | some e => simp_all
        | none =>
          rw [ht, he] at hok
          simp only [Option.map_some, renameState_gpr, renameState_vr, renameState_flags,
            renameState_mem, renameState_assume]
          have hs : ({ s' with pc := 0, halted := false, tail := none, err := none } : CS)
              = renameState f { s' with pc := 0, halted := false, tail := none, err := none } := rfl
          rw [hs]
          have h := ih t { s' with pc := 0, halted := false, tail := none, err := none } hfind hok
          rw [h]
          rfl

end

/-! ## Observations -/

theorem outBytes_rename {f : String → String} (m0 : Addr Int → Cell W32 Int) (s : CS)
    (n : Nat) : outBytes m0 (renameState f s) n = outBytes m0 s n := rfl

theorem abiObs_rename {f : String → String} (count : Nat) (sp0 : Int) (s : CS) :
    abiObs count sp0 (renameState f s) = abiObs count sp0 s := rfl

section

variable {f : String → String}

/-- A clean finish of the linux chain transfers to the renamed (darwin) chain, with the same
observations. -/
theorem runChain_clean (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (fuel : Nat)
    (hops : Nat) (name : String) (s : CS)
    (hfind : ∀ (n : String) (p : Prog), progs.find? (·.name = n) = some p →
      (renameProgs f progs).find? (·.name = f n) = some (renameProg f p))
    (herr : (runChain progs m0 fuel hops name s).1.err = none)
    (hhalt : (runChain progs m0 fuel hops name s).1.halted = true)
    (htail : (runChain progs m0 fuel hops name s).1.tail = none)
    (n : Nat) :
    (runChain (renameProgs f progs) m0 fuel hops (f name) (renameState f s)).1.err = none ∧
    (runChain (renameProgs f progs) m0 fuel hops (f name) (renameState f s)).1.halted = true ∧
    (runChain (renameProgs f progs) m0 fuel hops (f name) (renameState f s)).1.tail = none ∧
    outBytes m0 (runChain (renameProgs f progs) m0 fuel hops (f name) (renameState f s)).1 n
      = outBytes m0 (runChain progs m0 fuel hops name s).1 n ∧
    abiObs (runChain progs m0 fuel hops name s).1.pc 0
        (runChain (renameProgs f progs) m0 fuel hops (f name) (renameState f s)).1
      = abiObs (runChain progs m0 fuel hops name s).1.pc 0
        (runChain progs m0 fuel hops name s).1 := by
  have h := runChain_rename f progs m0 fuel hops name s hfind herr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h]; simp [herr]
  · rw [h]; simp [hhalt]
  · rw [h]; simp [htail]
  · rw [h]; exact outBytes_rename m0 _ n
  · rw [h]; exact abiObs_rename _ 0 _

end
