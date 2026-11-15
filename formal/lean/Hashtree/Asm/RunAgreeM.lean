import Hashtree.Asm.BodyReads

/-!
# Run invariance over a register read set and a memory address set

`Asm/RunAgree` generalised to a memory relation: `AgreeM R fl M s1 s2` asks agreement on the
general registers in `R`, on the flags when `fl`, and on the *lookups of the addresses in `M`*
(the log entries at other addresses may differ).  `exec_agreeM` is the one-step lemma: with the
instruction's register sources in `R` and its memory reads inside `M` (`ReadsM`, stated on the
effective addresses the first run computes), the two steps agree on `M` again (both append the
same cells), on `R`, and on the written registers.  This is the engine of the frame-slot
certificate (`Asm/FrameTags`): `M` is the complement of the tagged frame slots, and the copies
(`push`/`pop`/save/restore of tagged items) are handled outside this lemma.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Hashtree.Asm.RunAgreeM

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.BodyReads

section Engine
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

/-- Agreement on the general registers in `R` and on everything else except the recorded
branch assumptions.  `len` keeps register writes in step (`List.set` is a no-op past the end). -/
structure AgreeM (R : List Nat) (fl : Bool) (M : Addr γ → Prop) (s1 s2 : State α γ) : Prop where
  gpr : ∀ r, r ∈ R → s1.getG r = s2.getG r
  len : s1.gpr.length = s2.gpr.length
  vr : s1.vr = s2.vr
  /-- the flags agree when the certificate says they are live (`fl`) -/
  flags : fl = true → s1.flags = s2.flags
  /-- the logs agree at the addresses in `M` -/
  mem : ∀ a, M a → lookup a s1.mem = lookup a s2.mem
  pc : s1.pc = s2.pc
  halted : s1.halted = s2.halted
  tail : s1.tail = s2.tail
  err : s1.err = s2.err

variable {R : List Nat} {fl : Bool} {M : Addr γ → Prop} {s1 s2 : State α γ}

theorem AgreeM.mono (h : AgreeM R fl M s1 s2) {R' : List Nat} {fl' : Bool} (hR : ∀ r, r ∈ R' → r ∈ R)
    (hF : fl' = true → fl = true) : AgreeM R' fl' M s1 s2 :=
  { h with gpr := fun r hr => h.gpr r (hR r hr), flags := fun h' => h.flags (hF h') }

/-! ### Reads: equal on the agreeing state -/

theorem getV_ag (h : AgreeM R fl M s1 s2) (i : Nat) : s2.getV i = s1.getV i := by
  simp only [State.getV, h.vr]

theorem flags_ag (h : AgreeM R true M s1 s2) : s2.flags = s1.flags := (h.flags rfl).symm

theorem getG_ag (h : AgreeM R fl M s1 s2) {r : Nat} (hr : r ∈ R) : s2.getG r = s1.getG r :=
  (h.gpr r hr).symm

theorem regPtr_ag (h : AgreeM R fl M s1 s2) {r : Nat} (hr : r ∈ R) : regPtr s2 r = regPtr s1 r := by
  simp only [regPtr, getG_ag h hr]

theorem baseAddr_ag (h : AgreeM R fl M s1 s2) (ro : Region) {m : MemRef}
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

theorem effAddr_ag (h : AgreeM R fl M s1 s2) (ro : Region) {m : MemRef}
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

/-- Four consecutive cells from `a` (one lane) are in `M`. -/
def M4 (M : Addr γ → Prop) (a : Addr γ) : Prop := M a ∧ M (a.plusI 1) ∧ M (a.plusI 2) ∧ M (a.plusI 3)

/-- `n` consecutive lanes from `a` are in `M`. -/
def MLanes (M : Addr γ → Prop) : Addr γ → Nat → Prop
  | _, 0 => True
  | a, n + 1 => M4 M a ∧ MLanes M (a.plusI 4) n

/-- The eight cells of a 64-bit value at `a` are in `M` (in every form `loadVal` reads them). -/
def M8 (M : Addr γ → Prop) (a : Addr γ) : Prop :=
  M a ∧ (∀ j : Nat, 1 ≤ j → j < 8 → M (a.plusI j)) ∧ M4 M a ∧ M4 M (a.plusI 4)

/-- Memory-only agreement on `M`. -/
def MemAg (M : Addr γ → Prop) (m1 m2 : List (Addr γ × Cell α γ)) : Prop :=
  ∀ a, M a → lookup a m1 = lookup a m2

theorem readCell_memAg {m1 m2 : List (Addr γ × Cell α γ)} (hm : MemAg M m1 m2) (mem0 : Addr γ → Cell α γ)
    {s1 s2 : State α γ} (h1 : s1.mem = m1) (h2 : s2.mem = m2) (a : Addr γ) (ha : M a) :
    readCell mem0 s2 a = readCell mem0 s1 a := by
  simp only [readCell, h1, h2, hm a ha]

theorem loadLane_memAg {m1 m2 : List (Addr γ × Cell α γ)} (hm : MemAg M m1 m2) (mem0 : Addr γ → Cell α γ)
    {s1 s2 : State α γ} (h1 : s1.mem = m1) (h2 : s2.mem = m2) (a : Addr γ) (h4 : M4 M a) :
    loadLane mem0 s2 a = loadLane mem0 s1 a := by
  obtain ⟨c0, c1, c2, c3⟩ := h4
  simp only [loadLane, readCell_memAg hm mem0 h1 h2 _ c0, readCell_memAg hm mem0 h1 h2 _ c1,
    readCell_memAg hm mem0 h1 h2 _ c2, readCell_memAg hm mem0 h1 h2 _ c3]

theorem loadLanes_memAg {m1 m2 : List (Addr γ × Cell α γ)} (hm : MemAg M m1 m2) (mem0 : Addr γ → Cell α γ)
    {s1 s2 : State α γ} (h1 : s1.mem = m1) (h2 : s2.mem = m2) (a : Addr γ) (n : Nat)
    (hl : MLanes M a n) : loadLanes mem0 s2 a n = loadLanes mem0 s1 a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    obtain ⟨h4, hl'⟩ := hl
    simp only [loadLanes, loadLane_memAg hm mem0 h1 h2 a h4, ih _ hl']

theorem pbRest_memAg {m1 m2 : List (Addr γ × Cell α γ)} (hm : MemAg M m1 m2) (mem0 : Addr γ → Cell α γ)
    {s1 s2 : State α γ} (h1 : s1.mem = m1) (h2 : s2.mem = m2) (p a : Addr γ) (n : Nat) :
    ∀ k : Nat, (∀ j : Nat, k ≤ j → j < k + n → M (a.plusI j)) →
      pbRest mem0 s2 p a n k = pbRest mem0 s1 p a n k := by
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro k hk
    simp only [pbRest, readCell_memAg hm mem0 h1 h2 _ (hk k (Nat.le_refl _) (by omega)),
      ih (k + 1) (fun j h1 h2 => hk j (by omega) (by omega))]

theorem loadVal_memAg {m1 m2 : List (Addr γ × Cell α γ)} (hm : MemAg M m1 m2) (mem0 : Addr γ → Cell α γ)
    {s1 s2 : State α γ} (h1 : s1.mem = m1) (h2 : s2.mem = m2) (a : Addr γ) (h8 : M8 M a) :
    loadVal mem0 s2 a = loadVal mem0 s1 a := by
  obtain ⟨c0, hj, h4a, h4b⟩ := h8
  simp only [loadVal, readCell_memAg hm mem0 h1 h2 a c0, loadLane_memAg hm mem0 h1 h2 a h4a,
    loadLane_memAg hm mem0 h1 h2 _ h4b,
    fun p => pbRest_memAg hm mem0 h1 h2 p a 7 1 (fun j hj1 hj2 => hj j hj1 (by omega))]

theorem readCell_ag (h : AgreeM R fl M s1 s2) (mem0 : Addr γ → Cell α γ) (a : Addr γ) (ha : M a) :
    readCell mem0 s2 a = readCell mem0 s1 a := readCell_memAg h.mem mem0 rfl rfl a ha

theorem loadLane_ag (h : AgreeM R fl M s1 s2) (mem0 : Addr γ → Cell α γ) (a : Addr γ) (h4 : M4 M a) :
    loadLane mem0 s2 a = loadLane mem0 s1 a := loadLane_memAg h.mem mem0 rfl rfl a h4

theorem loadLanes_ag (h : AgreeM R fl M s1 s2) (mem0 : Addr γ → Cell α γ) (a : Addr γ) (n : Nat)
    (hl : MLanes M a n) : loadLanes mem0 s2 a n = loadLanes mem0 s1 a n :=
  loadLanes_memAg h.mem mem0 rfl rfl a n hl

theorem loadVal_ag (h : AgreeM R fl M s1 s2) (mem0 : Addr γ → Cell α γ) (a : Addr γ) (h8 : M8 M a) :
    loadVal mem0 s2 a = loadVal mem0 s1 a := loadVal_memAg h.mem mem0 rfl rfl a h8

/-- The memory reads of a vector source lie in `M` (on the effective address the first run computes). -/
def VReadsM (ro : Region) (M : Addr γ → Prop) (s : State α γ) (w : Nat) : VSrc → Prop
  | .reg _ => True
  | .mem m => ∀ a, effAddr ro s m = .ok a → MLanes M a w

/-- The memory read of a general source lies in `M`. -/
def GReadsM (ro : Region) (M : Addr γ → Prop) (s : State α γ) : GSrc → Prop
  | .mem m => ∀ a, effAddr ro s m = .ok a → M4 M a
  | _ => True

theorem readVSrc_ag (h : AgreeM R fl M s1 s2) (ro : Region) (mem0 : Addr γ → Cell α γ) (w : Nat)
    {v : VSrc} (hv : ∀ r, r ∈ vsrc v → r ∈ R) (hr : VReadsM ro M s1 w v) :
    readVSrc ro mem0 s2 w v = readVSrc ro mem0 s1 w v := by
  cases v with
  | reg i => simp only [readVSrc, getV_ag h]
  | mem m =>
    simp only [readVSrc, effAddr_ag h ro hv]
    cases he : effAddr ro s1 m with
    | error e => rfl
    | ok a => exact loadLanes_ag h mem0 a w (hr a he)

theorem gData32_ag (h : AgreeM R fl M s1 s2) (ro : Region) (mem0 : Addr γ → Cell α γ)
    {g : GSrc} (hg : ∀ r, r ∈ gsrc g → r ∈ R) (hr : GReadsM ro M s1 g) :
    gData32 ro mem0 s2 g = gData32 ro mem0 s1 g := by
  cases g with
  | reg i => simp only [gData32, getG_ag h (hg i (by simp [gsrc]))]
  | imm v => rfl
  | mem m =>
    simp only [gData32, effAddr_ag h ro hg]
    cases he : effAddr ro s1 m with
    | error e => rfl
    | ok a => exact loadLane_ag h mem0 a (hr a he)

theorem gCtl_ag (h : AgreeM R fl M s1 s2) {g : GSrc} (hg : ∀ r, r ∈ gsrc g → r ∈ R) :
    gCtl s2 g = gCtl s1 g := by
  cases g with
  | reg i => simp only [gCtl, getG_ag h (hg i (by simp [gsrc]))]
  | imm v => rfl
  | mem m => rfl

/-! ### Writes: the relation is preserved -/

theorem next_ag (h : AgreeM R fl M s1 s2) : AgreeM R fl M s1.next s2.next :=
  { h with pc := by simp only [State.next, h.pc] }

theorem setV_ag (h : AgreeM R fl M s1 s2) (i : Nat) (v : List α) : AgreeM R fl M (s1.setV i v) (s2.setV i v) :=
  { h with vr := by simp only [State.setV, h.vr] }

theorem setVec_ag (h : AgreeM R fl M s1 s2) (vex : Bool) (w d : Nat) (v : List α) :
    AgreeM R fl M (setVec s1 vex w d v) (setVec s2 vex w d v) := by
  unfold setVec
  rw [getV_ag h]
  exact setV_ag h _ _

theorem setG_ag (h : AgreeM R fl M s1 s2) (d : Nat) (v : Val α γ) :
    AgreeM (d :: R) fl M (s1.setG d v) (s2.setG d v) where
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

theorem setData32_ag (h : AgreeM R fl M s1 s2) (d : Nat) (x : α) :
    AgreeM (d :: R) fl M (setData32 s1 d x) (setData32 s2 d x) := setG_ag h d _

theorem lookup_cons_congr (a b : Addr γ) (c : Cell α γ) {m1 m2 : List (Addr γ × Cell α γ)}
    (hm : lookup a m1 = lookup a m2) : lookup a ((b, c) :: m1) = lookup a ((b, c) :: m2) := by
  simp only [lookup]
  cases AddrEq.same a b with
  | none => rfl
  | some t => cases t <;> simp only [hm]

theorem lookup_append_congr (a : Addr γ) (l : List (Addr γ × Cell α γ)) {m1 m2 : List (Addr γ × Cell α γ)}
    (hm : lookup a m1 = lookup a m2) : lookup a (l ++ m1) = lookup a (l ++ m2) := by
  induction l with
  | nil => simpa using hm
  | cons p l ih => exact lookup_cons_congr a p.1 p.2 ih

theorem storeLane_ag (h : AgreeM R fl M s1 s2) (a : Addr γ) (x : α) :
    AgreeM R fl M (storeLane s1 a x) (storeLane s2 a x) :=
  by
  refine { h with mem := ?_ }
  intro b hb
  simp only [storeLane]
  exact lookup_cons_congr _ _ _ (lookup_cons_congr _ _ _ (lookup_cons_congr _ _ _ (lookup_cons_congr _ _ _ (h.mem b hb))))

theorem storeLanes_ag (h : AgreeM R fl M s1 s2) (a : Addr γ) (xs : List α) :
    AgreeM R fl M (storeLanes s1 a xs) (storeLanes s2 a xs) := by
  induction xs generalizing s1 s2 a with
  | nil => exact h
  | cons x xs ih => exact ih (storeLane_ag h a x) _

theorem storeVal_ag (h : AgreeM R fl M s1 s2) (a : Addr γ) (v : Val α γ) :
    AgreeM R fl M (storeVal s1 a v) (storeVal s2 a v) := by
  cases v with
  | num lo hi => exact storeLane_ag (storeLane_ag h a lo) _ hi
  | ptr p =>
    refine { h with mem := ?_ }
    intro b hb
    simp only [storeVal]
    exact lookup_append_congr _ _ (h.mem b hb)

theorem clearFlags_ag (h : AgreeM R fl M s1 s2) : AgreeM R true M (clearFlags s1) (clearFlags s2) :=
  { h with flags := fun _ => rfl }

theorem setFlags_ag (h : AgreeM R fl M s1 s2) (a b : γ) : AgreeM R true M (setFlags s1 a b) (setFlags s2 a b) :=
  { h with flags := fun _ => rfl }

theorem halt_ag (h : AgreeM R fl M s1 s2) : AgreeM R fl M (halt s1) (halt s2) :=
  { h with halted := rfl }

theorem fail_ag (h : AgreeM R fl M s1 s2) (e : String) : AgreeM R fl M (s1.fail e) (s2.fail e) := by
  unfold State.fail
  rw [← h.err]
  split
  · exact { h with halted := rfl, err := rfl }
  · exact { h with halted := rfl, err := rfl }

theorem fail_pc (s : State α γ) (e : String) : (s.fail e).pc = s.pc := by
  unfold State.fail; split <;> rfl

theorem assume_ag (h : AgreeM R fl M s1 s2) (a1 a2 : List (Cond γ × Bool)) :
    AgreeM R fl M { s1 with assume := a1 } { s2 with assume := a2 } :=
  ⟨h.gpr, h.len, h.vr, h.flags, h.mem, h.pc, h.halted, h.tail, h.err⟩

theorem setPc_ag (h : AgreeM R fl M s1 s2) (t : Nat) : AgreeM R fl M { s1 with pc := t } { s2 with pc := t } :=
  ⟨h.gpr, h.len, h.vr, h.flags, h.mem, rfl, h.halted, h.tail, h.err⟩

theorem branch_ag (h : AgreeM R fl M s1 s2) (orc : Nat → Bool) (c : Cond γ) (t : Nat) :
    AgreeM R fl M (s1.branch orc c t) (s2.branch orc c t) := by
  obtain ⟨hg, hl, hv, hf, hm, hpc, hh, ht, he⟩ := h
  obtain ⟨g1, v1, f1, m1, p1, hl1, t1, e1, a1⟩ := s1
  obtain ⟨g2, v2, f2, m2, p2, hl2, t2, e2, a2⟩ := s2
  simp only at hv hm hpc hh ht he
  subst hv hpc hh ht he
  simp only [State.branch]
  split <;> (try split) <;> (try split) <;> exact ⟨hg, hl, rfl, hf, hm, rfl, rfl, rfl, rfl⟩

theorem branch_pc (s : State α γ) (orc : Nat → Bool) (c : Cond γ) (t : Nat) :
    (s.branch orc c t).pc = s.pc + 1 ∨ (s.branch orc c t).pc = t := by
  simp only [State.branch]
  split <;> (try split) <;> (try split) <;> simp [State.next]

/-! ### Lifting to `Except` -/

/-- Two step results agree: both fail with the same message, or both succeed with agreeing
states whose pc satisfies `P`. -/
def AgreeME (R : List Nat) (fl : Bool) (M : Addr γ → Prop) (P : Nat → Prop) :
    Except String (State α γ) → Except String (State α γ) → Prop
  | .ok x, .ok y => AgreeM R fl M x y ∧ P x.pc
  | .error e1, .error e2 => e1 = e2
  | _, _ => False

theorem AgreeME.bind {β : Type} {P : Nat → Prop} (m : Except String β)
    {f1 f2 : β → Except String (State α γ)}
    (h : ∀ x, m = .ok x → AgreeME R fl M P (f1 x) (f2 x)) : AgreeME R fl M P (m >>= f1) (m >>= f2) := by
  cases m with
  | error e => exact rfl
  | ok x => exact h x rfl

theorem AgreeME.pure {P : Nat → Prop} {x y : State α γ} (h : AgreeM R fl M x y) (hp : P x.pc) :
    AgreeME R fl M P (pure x) (pure y) := ⟨h, hp⟩

theorem AgreeME.throw {P : Nat → Prop} (e : String) :
    AgreeME R fl M P (throw e : Except String (State α γ)) (throw e) := rfl

theorem okOr_ag (h : AgreeM R fl M s1 s2) {R' : List Nat} {fl' : Bool} (P : Nat → Prop)
    (hR : ∀ r, r ∈ R → r ∈ R') (hF : fl = true → fl' = true)
    {r1 r2 : Except String (State α γ)} (he : AgreeME R' fl' M (fun q => q = s1.pc ∨ P q) r1 r2) :
    AgreeM R fl M (okOr s1 r1) (okOr s2 r2) ∧
      ((okOr s1 r1).pc = s1.pc ∨ (P (okOr s1 r1).pc ∧ AgreeM R' fl' M (okOr s1 r1) (okOr s2 r2))) := by
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
      refine ⟨hxy.mono hR hF, ?_⟩
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
    | exact ‹AgreeM _ _ _ _ _›
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
    | (apply AgreeME.bind; intro _ _)
    | (apply AgreeME.pure <;> first | (ag_writers; done) | (ag_pc; done))
    | apply AgreeME.throw
    | split))

/-- The memory reads of an instruction lie in `M` (on the addresses the first run computes). -/
def ReadsM (ro : Region) (M : Addr γ → Prop) (s : State α γ) : Instr → Prop
  | .vop _ _ w _ _ v => VReadsM ro M s w v
  | .vload _ w _ v => VReadsM ro M s w v
  | .inserti128 _ _ m _ => ∀ a, effAddr ro s m = .ok a → MLanes M a 4
  | .inserti64x4 _ _ m _ => ∀ a, effAddr ro s m = .ok a → MLanes M a 8
  | .mov _ _ (.mem m) => ∀ a, effAddr ro s m = .ok a → M8 M a ∧ M4 M a
  | .alu _ _ _ g => GReadsM ro M s g
  | .pop _ => ∀ sp, s.getG rsp = .ptr sp → M8 M sp
  | .ret => ∀ sp, s.getG rsp = .ptr sp → M8 M sp
  | _ => True

/-- One step: agreement on the instruction's register sources and on its memory reads gives
agreement on everything but the general registers (the logs agree on `M` again: both steps
append the same cells), and, when the step moves the pc, on the written registers as well, at a
static successor. -/
theorem exec_agreeM (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr)
    (h : AgreeM R fl M s1 s2) (hs : ∀ r, r ∈ srcs i → r ∈ R) (hsf : readsF i = true → fl = true)
    (hr : ReadsM ro M s1 i) :
    AgreeM R fl M (exec ro mem0 orc i s1) (exec ro mem0 orc i s2) ∧
      ((exec ro mem0 orc i s1).pc = s1.pc ∨
        ((exec ro mem0 orc i s1).pc ∈ succs s1.pc i ∧
          AgreeM (dsts i ++ R) (writesF i || fl) M (exec ro mem0 orc i s1) (exec ro mem0 orc i s2))) := by
  unfold exec
  rw [← h.halted]
  by_cases hh : s1.halted = true
  · simp only [hh, ite_true]; exact ⟨h, by simp⟩
  rw [ite_eq_right hh, ite_eq_right hh]
  have hV := getV_ag h
  cases i with
  | nop => dsimp only; exact ⟨next_ag h, Or.inr ⟨by simp [succs, State.next], next_ag h⟩⟩
  | jmp t =>
    dsimp only
    exact ⟨⟨h.gpr, h.len, h.vr, h.flags, h.mem, rfl, rfl, h.tail, h.err⟩,
      Or.inr ⟨by simp [succs], ⟨h.gpr, h.len, h.vr, h.flags, h.mem, rfl, rfl, h.tail, h.err⟩⟩⟩
  | jmpTail name => dsimp only; exact ⟨{ h with halted := rfl, tail := rfl }, Or.inl rfl⟩
  | vop op vex w d v1 v2 =>
    try dsimp only
    simp only [srcs] at hs; simp only [ReadsM] at hr; simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    simp only [hV, readVSrc_ag h ro mem0 w hs hr]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | vshift k vex w d src n =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | vshiftq vex w d src n =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | vror w d src n =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | vtern w d v1 v2 imm =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | vload vex w d src =>
    try dsimp only
    simp only [srcs] at hs; simp only [ReadsM] at hr; simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    simp only [hV, readVSrc_ag h ro mem0 w hs hr]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | vstore w m src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    simp only [hV, effAddr_ag h ro hs]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | pshufd vex d src imm =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | pshufb vex w d src mask =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | palignr vex d v1 v2 imm =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | pblendw d src imm =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | shufps w d v1 v2 imm =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | perm2f128 d v1 v2 imm =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | inserti128 d v1 m imm =>
    try dsimp only
    simp only [srcs] at hs; simp only [ReadsM] at hr; simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    simp only [hV, effAddr_ag h ro hs]
    refine okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) ?_
    apply AgreeME.bind; intro a ha
    rw [loadLanes_ag h mem0 a 4 (hr a ha)]
    ag_lift
  | inserti64x4 d v1 m imm =>
    try dsimp only
    simp only [srcs] at hs; simp only [ReadsM] at hr; simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    simp only [hV, effAddr_ag h ro hs]
    refine okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) ?_
    apply AgreeME.bind; intro a ha
    rw [loadLanes_ag h mem0 a 8 (hr a ha)]
    ag_lift
  | permi2d d v1 v2 =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | permi2q d v1 v2 =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | sha256rnds2 d src =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | sha256msg1 d src =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | sha256msg2 d src =>
    try dsimp only
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]; simp only [hV]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | mov w d src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    have hG : ∀ r, r ∈ gsrc src → s2.getG r = s1.getG r := fun r hr => getG_ag h (hs r hr)
    refine okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun h => h) ?_
    cases src with
    | reg r =>
      simp only [gData32_ag h ro mem0 hs trivial, hG r (by simp [gsrc])]
      ag_lift
    | imm v => simp only [gData32_ag h ro mem0 hs trivial]; ag_lift
    | mem m =>
      simp only [ReadsM] at hr
      simp only [effAddr_ag h ro hs, gData32_ag h ro mem0 hs (fun a ha => (hr a ha).2)]
      split
      · apply AgreeME.bind; intro a ha
        rw [loadVal_ag h mem0 a (hr a ha).1]
        ag_lift
      · ag_lift
  | movst w m src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    have hsrc : src ∈ R := hs src (List.mem_cons_self ..)
    have hm : ∀ r, r ∈ memRegs m → r ∈ R := fun r hr => hs r (List.mem_cons_of_mem _ hr)
    simp only [effAddr_ag h ro hm, getG_ag h hsrc]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) (by ag_lift)
  | alu op w d src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.cons_append, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    by_cases hz : op = .xor ∧ src = .reg d
    · obtain ⟨rfl, rfl⟩ := hz
      simp only [and_self, ite_true]
      exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun _ => rfl) (by ag_lift)
    · rw [if_neg hz] at hs
      have hd : d ∈ R := hs d (List.mem_cons_self ..)
      have hsrc : ∀ r, r ∈ gsrc src → r ∈ R := fun r hr => hs r (List.mem_cons_of_mem _ hr)
      have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hd
      simp only [ReadsM] at hr
      simp only [gData32_ag h ro mem0 hsrc hr, gData32_ag h ro mem0 hdd trivial, gCtl_ag h hsrc, gCtl_ag h hdd]
      exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun _ => rfl) (by ag_lift)
  | sub w d src =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    have hd : d ∈ R := hs d (List.mem_cons_self ..)
    have hsrc : ∀ r, r ∈ gsrc src → r ∈ R := fun r hr => hs r (List.mem_cons_of_mem _ hr)
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hd
    simp only [gCtl_ag h hsrc, gCtl_ag h hdd]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun _ => rfl) (by ag_lift)
  | lea d m =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    simp only [effAddr_ag h ro hs]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun h => h) (by ag_lift)
  | ror w d n =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gData32_ag h ro mem0 hdd trivial]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun _ => rfl) (by ag_lift)
  | shld w d src n =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    have hss : ∀ r, r ∈ gsrc (.reg src) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gData32_ag h ro mem0 hdd trivial, gData32_ag h ro mem0 hss trivial]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun _ => rfl) (by ag_lift)
  | shl w d n =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gData32_ag h ro mem0 hdd trivial, gCtl_ag h hdd]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun _ => rfl) (by ag_lift)
  | bswap w d =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    have hdd : ∀ r, r ∈ gsrc (.reg d) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gData32_ag h ro mem0 hdd trivial]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun h => h) (by ag_lift)
  | push r =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    simp only [getG_ag h (hs rsp (by simp)), getG_ag h (hs r (by simp))]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ hr) (fun h => h) (by ag_lift)
  | pop r =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.cons_append, List.singleton_append, Bool.false_or, succs]
    simp only [ReadsM] at hr
    simp only [getG_ag h (hs rsp (by simp))]
    refine okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)) (fun h => h) ?_
    cases hg : s1.getG rsp with
    | num _ _ => exact AgreeME.throw _
    | ptr sp =>
      dsimp only
      rw [loadVal_ag h mem0 sp (hr sp hg)]
      apply AgreeME.bind; intro v _
      refine AgreeME.pure ?_ (by ag_pc)
      refine AgreeM.mono (next_ag (setG_ag (setG_ag h r v) rsp _)) ?_ (fun h => h)
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with hx | hx | hx <;> simp [hx]
  | cmp w a b =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    have hb : ∀ r, r ∈ gsrc b → r ∈ R := fun r hr => hs r (List.mem_cons_of_mem _ hr)
    have haa : ∀ r, r ∈ gsrc (.reg a) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gCtl_ag h hb, gCtl_ag h haa]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun _ => rfl) (by ag_lift)
  | test w a b =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    have haa : ∀ r, r ∈ gsrc (.reg a) → r ∈ R := fun r hr => by simp only [gsrc, List.mem_singleton] at hr; rw [hr]; exact hs _ (by simp)
    simp only [gCtl_ag h haa]
    exact okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun _ => rfl) (by ag_lift)
  | jcc c t =>
    try dsimp only
    simp only [readsF] at hsf
    have hF := flags_ag (h.mono (fun _ hr => hr) (fun _ => hsf trivial))
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    simp only [hF]
    refine okOr_ag h (· ∈ [s1.pc + 1, t]) (fun _ hr => hr) (fun h => h) ?_
    cases hf : s1.flags with
    | none => exact AgreeME.throw _
    | some p =>
      obtain ⟨a, b⟩ := p
      dsimp only
      refine AgreeME.pure (branch_ag h orc _ t) ?_
      rcases branch_pc s1 orc (ccCond c a b) t with hp | hp <;> simp [hp]
  | jccTail c name =>
    try dsimp only
    simp only [readsF] at hsf
    have hF := flags_ag (h.mono (fun _ hr => hr) (fun _ => hsf trivial))
    simp only [dsts, writesF, List.nil_append, Bool.false_or, succs]
    simp only [hF]
    refine okOr_ag h (· ∈ [s1.pc + 1]) (fun _ hr => hr) (fun h => h) ?_
    cases hf : s1.flags with
    | none => exact AgreeME.throw _
    | some p =>
      obtain ⟨a, b⟩ := p
      have hb := branch_ag h orc (ccCond c a b) 1000000000
      dsimp only
      rw [← hb.pc]
      split
      · refine AgreeME.pure { hb with pc := h.pc, halted := rfl, tail := rfl } ?_
        exact Or.inl rfl
      · refine AgreeME.pure hb ?_
        rename_i hne
        rcases branch_pc s1 orc (ccCond c a b) 1000000000 with hp | hp
        · simp [hp]
        · exact absurd hp hne
  | ret =>
    try dsimp only
    simp only [srcs] at hs; simp only [dsts, writesF, List.singleton_append, Bool.false_or, Bool.true_or, succs]
    simp only [ReadsM] at hr
    simp only [getG_ag h (hs rsp (by simp))]
    refine okOr_ag h (· ∈ []) (fun _ hr => List.mem_cons_of_mem _ hr) (fun h => h) ?_
    cases hg : s1.getG rsp with
    | num _ _ => exact AgreeME.throw _
    | ptr sp =>
      dsimp only
      rw [loadVal_ag h mem0 sp (hr sp hg)]
      ag_lift

end Engine

end Hashtree.Asm.RunAgreeM
