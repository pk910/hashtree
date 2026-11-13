import Hashtree.Asm.BodyReads

/-!
# Run invariance over a register read set

Two states that agree on everything except some general registers (and the recorded branch
assumptions) run the same way, as long as they agree on every general register the program can
read before writing it.  `Agree R s1 s2` is the agreement relation (`R`: the registers that must
agree); `exec_agree` is the one-step lemma over the `srcs`/`dsts` scan of `Asm/BodyReads`
(`exec i` reads general registers only from `srcs i` and writes only `dsts i`); `run_agree` lifts
it through the fetch-execute loop with a per-pc read-set certificate `L` (`Cert prog L`: the
instruction's sources are in `L pc`, and for every static successor `q` of `pc` the registers of
`L q` not written at `pc` are in `L pc`).  The certificate is checked by `decide` on the concrete
program (`certB`); `live` computes one (the standard backward live-variable fixpoint).

For a straight-line stream `L pc = rbw (stream after pc)` is such a certificate (`rbw` is the
read-before-write scan); the kernel bodies loop, so their certificates are the fixpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Hashtree.Asm.RunAgree

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.BodyReads

section Engine
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

/-- Agreement on the general registers in `R` and on everything else except the recorded
branch assumptions.  `len` keeps register writes in step (`List.set` is a no-op past the end). -/
structure Agree (R : List Nat) (s1 s2 : State α γ) : Prop where
  gpr : ∀ r, r ∈ R → s1.getG r = s2.getG r
  len : s1.gpr.length = s2.gpr.length
  vr : s1.vr = s2.vr
  flags : s1.flags = s2.flags
  mem : s1.mem = s2.mem
  pc : s1.pc = s2.pc
  halted : s1.halted = s2.halted
  tail : s1.tail = s2.tail
  err : s1.err = s2.err

variable {R : List Nat} {s1 s2 : State α γ}

theorem Agree.mono (h : Agree R s1 s2) {R' : List Nat} (hR : ∀ r, r ∈ R' → r ∈ R) : Agree R' s1 s2 :=
  { h with gpr := fun r hr => h.gpr r (hR r hr) }

/-! ### Reads: equal on the agreeing state -/

theorem getV_ag (h : Agree R s1 s2) (i : Nat) : s2.getV i = s1.getV i := by
  simp only [State.getV, h.vr]

theorem flags_ag (h : Agree R s1 s2) : s2.flags = s1.flags := h.flags.symm

theorem getG_ag (h : Agree R s1 s2) {r : Nat} (hr : r ∈ R) : s2.getG r = s1.getG r :=
  (h.gpr r hr).symm

theorem regPtr_ag (h : Agree R s1 s2) {r : Nat} (hr : r ∈ R) : regPtr s2 r = regPtr s1 r := by
  simp only [regPtr, getG_ag h hr]

theorem baseAddr_ag (h : Agree R s1 s2) (ro : Region) {m : MemRef}
    (hm : ∀ r, r ∈ memRegs m → r ∈ R) : baseAddr ro s2 m = baseAddr ro s1 m := by
  unfold baseAddr
  cases m.ro with
  | some o => rfl
  | none =>
    try dsimp only
    cases hb : m.base with
    | none => rfl
    | some b =>
      apply regPtr_ag h
      apply hm
      simp [memRegs, baseOf, hb]

theorem effAddr_ag (h : Agree R s1 s2) (ro : Region) {m : MemRef}
    (hm : ∀ r, r ∈ memRegs m → r ∈ R) : effAddr ro s2 m = effAddr ro s1 m := by
  unfold effAddr
  rw [baseAddr_ag h ro hm]
  cases baseAddr ro s1 m with
  | error e => rfl
  | ok b =>
    try dsimp only
    cases hi : m.index with
    | none => rfl
    | some i =>
      have : i ∈ R := hm i (by simp [memRegs, indexOf, hi])
      simp only [getG_ag h this]

theorem readCell_ag (h : Agree R s1 s2) (mem0 : Addr γ → Cell α γ) (a : Addr γ) :
    readCell mem0 s2 a = readCell mem0 s1 a := by
  simp only [readCell, h.mem]

theorem loadLane_ag (h : Agree R s1 s2) (mem0 : Addr γ → Cell α γ) (a : Addr γ) :
    loadLane mem0 s2 a = loadLane mem0 s1 a := by
  simp only [loadLane, readCell_ag h]

theorem loadLanes_ag (h : Agree R s1 s2) (mem0 : Addr γ → Cell α γ) (a : Addr γ) (n : Nat) :
    loadLanes mem0 s2 a n = loadLanes mem0 s1 a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [loadLanes, loadLane_ag h, ih]

theorem pbRest_ag (h : Agree R s1 s2) (mem0 : Addr γ → Cell α γ) (p a : Addr γ) (n k : Nat) :
    pbRest mem0 s2 p a n k = pbRest mem0 s1 p a n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [pbRest, readCell_ag h, ih]

theorem loadVal_ag (h : Agree R s1 s2) (mem0 : Addr γ → Cell α γ) (a : Addr γ) :
    loadVal mem0 s2 a = loadVal mem0 s1 a := by
  simp only [loadVal, readCell_ag h, pbRest_ag h, loadLane_ag h]

theorem readVSrc_ag (h : Agree R s1 s2) (ro : Region) (mem0 : Addr γ → Cell α γ) (w : Nat)
    {v : VSrc} (hv : ∀ r, r ∈ vsrc v → r ∈ R) : readVSrc ro mem0 s2 w v = readVSrc ro mem0 s1 w v := by
  cases v with
  | reg i => simp only [readVSrc, getV_ag h]
  | mem m => simp only [readVSrc, effAddr_ag h ro hv, loadLanes_ag h]

theorem gData32_ag (h : Agree R s1 s2) (ro : Region) (mem0 : Addr γ → Cell α γ)
    {g : GSrc} (hg : ∀ r, r ∈ gsrc g → r ∈ R) : gData32 ro mem0 s2 g = gData32 ro mem0 s1 g := by
  cases g with
  | reg i => simp only [gData32, getG_ag h (hg i (by simp [gsrc]))]
  | imm v => rfl
  | mem m => simp only [gData32, effAddr_ag h ro hg, loadLane_ag h]

theorem gCtl_ag (h : Agree R s1 s2) {g : GSrc} (hg : ∀ r, r ∈ gsrc g → r ∈ R) :
    gCtl s2 g = gCtl s1 g := by
  cases g with
  | reg i => simp only [gCtl, getG_ag h (hg i (by simp [gsrc]))]
  | imm v => rfl
  | mem m => rfl

/-! ### Writes: the relation is preserved -/

theorem next_ag (h : Agree R s1 s2) : Agree R s1.next s2.next :=
  { h with pc := by simp only [State.next, h.pc] }

theorem setV_ag (h : Agree R s1 s2) (i : Nat) (v : List α) : Agree R (s1.setV i v) (s2.setV i v) :=
  { h with vr := by simp only [State.setV, h.vr] }

theorem setVec_ag (h : Agree R s1 s2) (vex : Bool) (w d : Nat) (v : List α) :
    Agree R (setVec s1 vex w d v) (setVec s2 vex w d v) := by
  unfold setVec
  rw [getV_ag h]
  exact setV_ag h _ _

theorem setG_ag (h : Agree R s1 s2) (d : Nat) (v : Val α γ) :
    Agree (d :: R) (s1.setG d v) (s2.setG d v) where
  gpr r hr := by
    simp only [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set, h.len]
    split
    · rfl
    · rename_i hne
      have hr' : r ∈ R := by
        rcases List.mem_cons.mp hr with h' | h'
        · exact absurd h'.symm hne
        · exact h'
      have := h.gpr r hr'
      simpa only [State.getG, List.getD_eq_getElem?_getD] using this
  len := by simp only [State.setG, List.length_set, h.len]
  vr := h.vr
  flags := h.flags
  mem := h.mem
  pc := h.pc
  halted := h.halted
  tail := h.tail
  err := h.err

theorem setData32_ag (h : Agree R s1 s2) (d : Nat) (x : α) :
    Agree (d :: R) (setData32 s1 d x) (setData32 s2 d x) := setG_ag h d _

theorem storeLane_ag (h : Agree R s1 s2) (a : Addr γ) (x : α) :
    Agree R (storeLane s1 a x) (storeLane s2 a x) :=
  { h with mem := by simp only [storeLane, h.mem] }

theorem storeLanes_ag (h : Agree R s1 s2) (a : Addr γ) (xs : List α) :
    Agree R (storeLanes s1 a xs) (storeLanes s2 a xs) := by
  induction xs generalizing s1 s2 a with
  | nil => exact h
  | cons x xs ih => exact ih (storeLane_ag h a x) _

theorem storeVal_ag (h : Agree R s1 s2) (a : Addr γ) (v : Val α γ) :
    Agree R (storeVal s1 a v) (storeVal s2 a v) := by
  cases v with
  | num lo hi => exact storeLane_ag (storeLane_ag h a lo) _ hi
  | ptr p => exact { h with mem := by simp only [storeVal, h.mem] }

theorem clearFlags_ag (h : Agree R s1 s2) : Agree R (clearFlags s1) (clearFlags s2) :=
  { h with flags := rfl }

theorem setFlags_ag (h : Agree R s1 s2) (a b : γ) : Agree R (setFlags s1 a b) (setFlags s2 a b) :=
  { h with flags := rfl }

theorem halt_ag (h : Agree R s1 s2) : Agree R (halt s1) (halt s2) :=
  { h with halted := rfl }

theorem fail_ag (h : Agree R s1 s2) (e : String) : Agree R (s1.fail e) (s2.fail e) := by
  unfold State.fail
  rw [← h.err]
  split
  · exact { h with halted := rfl, err := rfl }
  · exact { h with halted := rfl, err := rfl }

theorem fail_pc (s : State α γ) (e : String) : (s.fail e).pc = s.pc := by
  unfold State.fail; split <;> rfl

theorem assume_ag (h : Agree R s1 s2) (a1 a2 : List (Cond γ × Bool)) :
    Agree R { s1 with assume := a1 } { s2 with assume := a2 } :=
  ⟨h.gpr, h.len, h.vr, h.flags, h.mem, h.pc, h.halted, h.tail, h.err⟩

theorem setPc_ag (h : Agree R s1 s2) (t : Nat) : Agree R { s1 with pc := t } { s2 with pc := t } :=
  ⟨h.gpr, h.len, h.vr, h.flags, h.mem, rfl, h.halted, h.tail, h.err⟩

theorem branch_ag (h : Agree R s1 s2) (orc : Nat → Bool) (c : Cond γ) (t : Nat) :
    Agree R (s1.branch orc c t) (s2.branch orc c t) := by
  obtain ⟨hg, hl, hv, hf, hm, hpc, hh, ht, he⟩ := h
  obtain ⟨g1, v1, f1, m1, p1, hl1, t1, e1, a1⟩ := s1
  obtain ⟨g2, v2, f2, m2, p2, hl2, t2, e2, a2⟩ := s2
  simp only at hv hf hm hpc hh ht he
  subst hv hf hm hpc hh ht he
  simp only [State.branch]
  split <;> (try split) <;> (try split) <;> exact ⟨hg, hl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem branch_pc (s : State α γ) (orc : Nat → Bool) (c : Cond γ) (t : Nat) :
    (s.branch orc c t).pc = s.pc + 1 ∨ (s.branch orc c t).pc = t := by
  simp only [State.branch]
  split <;> (try split) <;> (try split) <;> simp [State.next]

/-! ### Lifting to `Except` -/

/-- Two step results agree: both fail with the same message, or both succeed with agreeing
states whose pc satisfies `P`. -/
def AgreeE (R : List Nat) (P : Nat → Prop) :
    Except String (State α γ) → Except String (State α γ) → Prop
  | .ok x, .ok y => Agree R x y ∧ P x.pc
  | .error e1, .error e2 => e1 = e2
  | _, _ => False

theorem AgreeE.bind {β : Type} {P : Nat → Prop} (m : Except String β)
    {f1 f2 : β → Except String (State α γ)}
    (h : ∀ x, m = .ok x → AgreeE R P (f1 x) (f2 x)) : AgreeE R P (m >>= f1) (m >>= f2) := by
  cases m with
  | error e => exact rfl
  | ok x => exact h x rfl

theorem AgreeE.pure {P : Nat → Prop} {x y : State α γ} (h : Agree R x y) (hp : P x.pc) :
    AgreeE R P (pure x) (pure y) := ⟨h, hp⟩

theorem AgreeE.throw {P : Nat → Prop} (e : String) :
    AgreeE R P (throw e : Except String (State α γ)) (throw e) := rfl

theorem okOr_ag (h : Agree R s1 s2) {R' : List Nat} (P : Nat → Prop) (hR : ∀ r, r ∈ R → r ∈ R')
    {r1 r2 : Except String (State α γ)} (he : AgreeE R' (fun q => q = s1.pc ∨ P q) r1 r2) :
    Agree R (okOr s1 r1) (okOr s2 r2) ∧
      ((okOr s1 r1).pc = s1.pc ∨ (P (okOr s1 r1).pc ∧ Agree R' (okOr s1 r1) (okOr s2 r2))) := by
  cases r1 with
  | error e1 =>
    try dsimp only
    cases r2 with
    | error e2 =>
      have he' : e1 = e2 := he
      subst he'
      exact ⟨fail_ag h e1, Or.inl (fail_pc s1 e1)⟩
    | ok y => exact absurd he id
  | ok x =>
    try dsimp only
    cases r2 with
    | error e2 => exact absurd he id
    | ok y =>
      obtain ⟨hxy, hp⟩ := he
      refine ⟨hxy.mono hR, ?_⟩
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr ⟨hp, hxy⟩

/-- Static successors of the instruction at `p`. -/
def succs (p : Nat) : Instr → List Nat
  | .jcc _ t => [p + 1, t]
  | .jmp t => [t]
  | .jccTail _ _ => [p + 1]
  | .jmpTail _ => []
  | .ret => []
  | _ => [p + 1]

/-! ### The one-step lemma -/

local macro "ag_writers" : tactic => `(tactic| (
  repeat first
    | exact ‹Agree _ _ _›
    | apply next_ag
    | apply setVec_ag
    | apply setG_ag
    | apply setData32_ag
    | apply storeLanes_ag
    | apply storeLane_ag
    | apply storeVal_ag
    | apply clearFlags_ag
    | apply setFlags_ag
    | apply halt_ag
    | apply branch_ag))

theorem storeLanes_pc (s : State α γ) (a : Addr γ) (xs : List α) : (storeLanes s a xs).pc = s.pc := by
  induction xs generalizing s a with
  | nil => rfl
  | cons x xs ih => simp only [storeLanes, ih, storeLane]

theorem storeVal_pc (s : State α γ) (a : Addr γ) (v : Val α γ) : (storeVal s a v).pc = s.pc := by
  cases v <;> simp [storeVal, storeLane]

local macro "ag_pc" : tactic => `(tactic| (
  simp only [State.next, setVec, State.setV, State.setG, setData32, clearFlags, setFlags, halt,
    storeLane, storeLanes_pc, storeVal_pc, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false, true_or, or_true, Nat.succ_ne_self]))

local macro "ag_lift" : tactic => `(tactic| (
  repeat first
    | (apply AgreeE.bind; intro _ _)
    | (apply AgreeE.pure <;> first | (ag_writers; done) | (ag_pc; done))
    | apply AgreeE.throw
    | split))

/-- One step: agreement on the instruction's sources gives agreement on everything but the
general registers, and, when the step moves the pc (it succeeded), agreement on the written
registers as well, at a static successor. -/
theorem exec_agree (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr)
    (h : Agree R s1 s2) (hs : ∀ r, r ∈ srcs i → r ∈ R) :
    Agree R (exec ro mem0 orc i s1) (exec ro mem0 orc i s2) ∧
      ((exec ro mem0 orc i s1).pc = s1.pc ∨
        ((exec ro mem0 orc i s1).pc ∈ succs s1.pc i ∧
          Agree (dsts i ++ R) (exec ro mem0 orc i s1) (exec ro mem0 orc i s2))) := by
  unfold exec
  rw [← h.halted]
  by_cases hh : s1.halted = true
  · simp only [hh, ite_true]; exact ⟨h, by simp⟩
  rw [if_neg hh, if_neg hh]
  have hV := getV_ag h
  have hF := flags_ag h
  have hLL := loadLanes_ag h mem0
  have hLV := loadVal_ag h mem0
  have hL := loadLane_ag h mem0
  cases i with
  | nop => dsimp only; exact ⟨next_ag h, Or.inr ⟨by simp [succs, State.next], next_ag h⟩⟩
  | jmp t =>
    dsimp only
    exact ⟨⟨h.gpr, h.len, h.vr, h.flags, h.mem, rfl, rfl, h.tail, h.err⟩,
      Or.inr ⟨by simp [succs], ⟨h.gpr, h.len, h.vr, h.flags, h.mem, rfl, rfl, h.tail, h.err⟩⟩⟩
  | jmpTail name => dsimp only; exact ⟨{ h with halted := rfl, tail := rfl }, Or.inl rfl⟩
  | vop op vex w d v1 v2 =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.nil_append, succs]
    simp only [hV, readVSrc_ag h ro mem0 w hs]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | vshift k vex w d src n =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | vshiftq vex w d src n =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | vror w d src n =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | vtern w d v1 v2 imm =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | vload vex w d src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.nil_append, succs]
    simp only [hV, readVSrc_ag h ro mem0 w hs]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | vstore w m src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.nil_append, succs]
    simp only [hV, effAddr_ag h ro hs]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | pshufd vex d src imm =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | pshufb vex w d src mask =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | palignr vex d v1 v2 imm =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | pblendw d src imm =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | shufps w d v1 v2 imm =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | perm2f128 d v1 v2 imm =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | inserti128 d v1 m imm =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.nil_append, succs]
    simp only [hV, effAddr_ag h ro hs, hLL]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | inserti64x4 d v1 m imm =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.nil_append, succs]
    simp only [hV, effAddr_ag h ro hs, hLL]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | permi2d d v1 v2 =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | permi2q d v1 v2 =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | sha256rnds2 d src =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | sha256msg1 d src =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | sha256msg2 d src =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | mov w d src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    have hG : ∀ r, r ∈ gsrc src → s2.getG r = s1.getG r := fun r hr => getG_ag h (hs r hr)
    simp only [gData32_ag h ro mem0 hs]
    refine okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) ?_
    cases src with
    | reg r =>
      simp only [hG r (by simp [gsrc])]
      ag_lift
    | imm v => ag_lift
    | mem m =>
      simp only [effAddr_ag h ro hs, hLV]
      ag_lift
  | movst w m src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.nil_append, succs]
    have hsrc : src ∈ R := hs src (List.mem_cons_self ..)
    have hm : ∀ r, r ∈ memRegs m → r ∈ R := fun r hr => hs r (List.mem_cons_of_mem _ hr)
    simp only [effAddr_ag h ro hm, getG_ag h hsrc]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | alu op w d src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    have hd : d ∈ R := hs d (List.mem_cons_self ..)
    have hsrc : ∀ r, r ∈ gsrc src → r ∈ R := fun r hr => hs r (List.mem_cons_of_mem _ hr)
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hd
    simp only [gData32_ag h ro mem0 hsrc, gData32_ag h ro mem0 hdd, gCtl_ag h hsrc, gCtl_ag h hdd]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (by ag_lift)
  | sub w d src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    have hd : d ∈ R := hs d (List.mem_cons_self ..)
    have hsrc : ∀ r, r ∈ gsrc src → r ∈ R := fun r hr => hs r (List.mem_cons_of_mem _ hr)
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hd
    simp only [gCtl_ag h hsrc, gCtl_ag h hdd]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (by ag_lift)
  | lea d m =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    simp only [effAddr_ag h ro hs]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (by ag_lift)
  | ror w d n =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gData32_ag h ro mem0 hdd]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (by ag_lift)
  | shld w d src n =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    have hss : ∀ r, r ∈ gsrc (.reg src) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gData32_ag h ro mem0 hdd, gData32_ag h ro mem0 hss]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (by ag_lift)
  | shl w d n =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gData32_ag h ro mem0 hdd, gCtl_ag h hdd]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (by ag_lift)
  | bswap w d =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gData32_ag h ro mem0 hdd]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (by ag_lift)
  | push r =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    simp only [getG_ag h (hs rsp (by simp)), getG_ag h (hs r (by simp))]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (by ag_lift)
  | pop r =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.cons_append, List.singleton_append, succs]
    simp only [getG_ag h (hs rsp (by simp)), hLV]
    refine okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)) ?_
    cases hg : s1.getG rsp with
    | num _ _ => exact AgreeE.throw _
    | ptr sp =>
      dsimp only
      apply AgreeE.bind; intro v _
      refine AgreeE.pure ?_ (by ag_pc)
      refine Agree.mono (next_ag (setG_ag (setG_ag h r v) rsp _)) ?_
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with hx | hx | hx <;> simp [hx]
  | cmp w a b =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.nil_append, succs]
    have hb : ∀ r, r ∈ gsrc b → r ∈ R := fun r hr => hs r (List.mem_cons_of_mem _ hr)
    have haa : ∀ r, r ∈ gsrc (.reg a) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gCtl_ag h hb, gCtl_ag h haa]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | test w a b =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.nil_append, succs]
    have haa : ∀ r, r ∈ gsrc (.reg a) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gCtl_ag h haa]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (by ag_lift)
  | jcc c t =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]
    simp only [hF]
    refine okOr_ag h (· ∈ [s1.pc + 1, t]) (fun _ hr => hr) ?_
    cases hf : s1.flags with
    | none => exact AgreeE.throw _
    | some p =>
      obtain ⟨a, b⟩ := p
      dsimp only
      refine AgreeE.pure (branch_ag h orc _ t) ?_
      rcases branch_pc s1 orc (ccCond c a b) t with hp | hp <;> simp [hp]
  | jccTail c name =>
    try dsimp only
    simp only [dsts, List.nil_append, succs]
    simp only [hF]
    refine okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) ?_
    cases hf : s1.flags with
    | none => exact AgreeE.throw _
    | some p =>
      obtain ⟨a, b⟩ := p
      have hb := branch_ag h orc (ccCond c a b) 1000000000
      dsimp only
      rw [← hb.pc]
      split
      · refine AgreeE.pure { hb with pc := h.pc, halted := rfl, tail := rfl } ?_
        exact Or.inl rfl
      · refine AgreeE.pure hb ?_
        rename_i hne
        rcases branch_pc s1 orc (ccCond c a b) 1000000000 with hp | hp
        · simp [hp]
        · exact absurd hp hne
  | ret =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, List.singleton_append, succs]
    simp only [getG_ag h (hs rsp (by simp)), hLV]
    refine okOr_ag h (· ∈ []) (fun _ hr => List.mem_cons_of_mem _ hr) ?_
    ag_lift

/-! ### The run -/

/-- A per-pc read-set certificate: the sources of the instruction at `p` are in `L p`, and the
registers of a static successor's set that `p` does not write are in `L p`. -/
def Cert (prog : Array Instr) (L : Nat → List Nat) : Prop :=
  ∀ p i, prog[p]? = some i →
    (∀ r, r ∈ srcs i → r ∈ L p) ∧ ∀ q, q ∈ succs p i → ∀ r, r ∈ L q → r ∈ dsts i ++ L p

/-- Runs from states agreeing on the certificate's set at their pc agree on everything but the
general registers (and on the general registers of the final pc's set). -/
theorem run_agree (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    {L : Nat → List Nat} (hc : Cert prog L) (n : Nat) {s1 s2 : State α γ}
    (h : Agree (L s1.pc) s1 s2) :
    Agree (L (run prog ro mem0 orc n s1).pc) (run prog ro mem0 orc n s1) (run prog ro mem0 orc n s2) := by
  induction n generalizing s1 s2 with
  | zero => exact h
  | succ n ih =>
    try dsimp only
    unfold run
    rw [← h.halted, ← h.pc]
    by_cases hh : s1.halted = true
    · simp only [hh, ite_true]; exact h
    simp only [hh, Bool.false_eq_true, ite_false]
    cases hp : prog[s1.pc]? with
    | none =>
      rw [fail_pc]
      exact fail_ag h _
    | some i =>
      apply ih
      obtain ⟨hsrc, hsucc⟩ := hc s1.pc i hp
      obtain ⟨h1, h2⟩ := exec_agree ro mem0 orc i h hsrc
      rcases h2 with h2 | ⟨hq, h3⟩
      · rw [h2]; exact h1
      · exact h3.mono (hsucc _ hq)

end Engine

/-! ### Deciding a certificate and computing one -/

/-- The certificate check on a program, with `L` as a list of per-pc sets. -/
def certB (prog : Array Instr) (L : List (List Nat)) : Bool :=
  (List.range prog.size).all fun p => match prog[p]? with
    | none => true
    | some i =>
      (srcs i).all (fun r => (L.getD p []).contains r) &&
        (succs p i).all fun q => (L.getD q []).all fun r => (dsts i).contains r || (L.getD p []).contains r

theorem Cert_of_certB {prog : Array Instr} {L : List (List Nat)} (h : certB prog L = true) :
    Cert prog (fun p => L.getD p []) := by
  intro p i hp
  have hlt : p < prog.size := (Array.getElem?_eq_some_iff.mp hp).1
  have := (List.all_eq_true.mp h) p (List.mem_range.mpr hlt)
  simp only [hp, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem] at this
  refine ⟨this.1, fun q hq r hr => ?_⟩
  rw [List.mem_append]
  exact this.2 q hq r hr

/-- One backward liveness sweep, from the last pc down: forward successors use the sets
already computed in this sweep (`acc`, headed by pc `p + 1`), backward ones the previous
sweep's (`old`). -/
def sweepAux (prog : Array Instr) (old : List (List Nat)) : Nat → List (List Nat) → List (List Nat)
  | 0, acc => acc
  | p + 1, acc =>
    let cur := match prog[p]? with
      | none => []
      | some i =>
        (srcs i ++ (succs p i).flatMap fun q =>
          (if p < q then acc.getD (q - p - 1) [] else old.getD q []).filter
            fun r => !(dsts i).contains r).eraseDups
    sweepAux prog old p (cur :: acc)

def liveSweep (prog : Array Instr) (old : List (List Nat)) : List (List Nat) :=
  sweepAux prog old prog.size []

def liveFix (prog : Array Instr) : Nat → List (List Nat) → List (List Nat)
  | 0, L => L
  | n + 1, L =>
    let L' := liveSweep prog L
    if L' = L then L else liveFix prog n L'

/-- The live-in sets of a program (a fixpoint reached within `fuel` sweeps; otherwise the
partial iterate, which `certB` then rejects). -/
def live (prog : Array Instr) (fuel : Nat := 16) : List (List Nat) :=
  liveFix prog fuel (List.replicate prog.size [])

end Hashtree.Asm.RunAgree
