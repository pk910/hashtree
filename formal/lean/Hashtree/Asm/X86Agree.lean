import Hashtree.Asm.X86

/-!
# x86-64: dead-register congruence

`AgreeOn S s1 s2` says that two machine states agree everywhere except on the general registers
whose index is in the set `S` (and on the flags when `flg ∈ S`).  `execE_agree` shows that one
instruction that reads no register of `S` takes two agreeing states to results that agree on
`S` minus the registers it writes (or fail with the same message); `execE_eq` relates the
instruction body `execE` to `exec`.  `run_agree` lifts this to whole runs: if the reference run
does not fail and a per-pc analysis of read and write sets justifies every instruction it
executes (with `successors` and `execE_ok_pc` locating the pc of the next one), the peer run
ends in a state that agrees on the analysis set of the final pc.  The intended use is an entry
contract for a kernel that tolerates arbitrary values in scratch registers the kernel overwrites
before reading (the x4/x8/x16 tail-call hand-offs).
-/

namespace Hashtree.Asm.X86
open Hashtree.Asm

/-- Pseudo-index standing for the flags in the read/write sets; the shipped kernels use only
general registers `0 … 15`. -/
def flg : Nat := 16

/-- States that agree everywhere except on the general registers whose index is in `S`, and on
the flags when `flg ∈ S`. -/
structure AgreeOn {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    (S : List Nat) (s1 s2 : State α γ) : Prop where
  pc : s1.pc = s2.pc
  halted : s1.halted = s2.halted
  tail : s1.tail = s2.tail
  err : s1.err = s2.err
  mem : s1.mem = s2.mem
  vr : s1.vr = s2.vr
  assume : s1.assume = s2.assume
  flags : flg ∉ S → s1.flags = s2.flags
  glen : s1.gpr.length = s2.gpr.length
  gpr : ∀ i, i ∉ S → s1.getG i = s2.getG i
  /-- `flg` is not a general register: its `getG` value is always the default, and the
  instructions never write index `flg`, so it can be kept outside the analysis. -/
  gpr16 : s1.getG flg = s2.getG flg

/-- Remove one register from the "may still differ" set. -/
def eraseReg (S : List Nat) (d : Nat) : List Nat := S.filter (fun x => !decide (x = d))

theorem mem_eraseReg {S : List Nat} {d x : Nat} : x ∈ eraseReg S d ↔ x ∈ S ∧ x ≠ d := by
  simp [eraseReg, List.mem_filter]

theorem not_mem_eraseReg {S : List Nat} {d i : Nat} (hid : i ≠ d) (h : i ∉ eraseReg S d) :
    i ∉ S := by
  intro hs
  exact h (by rw [mem_eraseReg]; exact ⟨hs, hid⟩)

theorem mem_eraseReg_of_mem {S : List Nat} {d x : Nat} (hs : x ∈ S) (hx : x ≠ d) :
    x ∈ eraseReg S d := by
  rw [mem_eraseReg]
  exact ⟨hs, hx⟩

/-- A larger "may differ" set is weaker. -/
theorem AgreeOn.mono {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S T : List Nat} {s1 s2 : State α γ}
    (h : AgreeOn S s1 s2) (hST : ∀ i, i ∈ S → i ∈ T) : AgreeOn T s1 s2 where
  pc := h.pc
  halted := h.halted
  tail := h.tail
  err := h.err
  mem := h.mem
  vr := h.vr
  assume := h.assume
  flags := fun hT => h.flags (fun hS => hT (hST flg hS))
  glen := h.glen
  gpr := fun i hi => h.gpr i (fun hS => hi (hST i hS))
  gpr16 := h.gpr16

/-! ## `getD`/`set` on plain lists -/

theorem getD_set_self {β : Type} {l : List β} {i : Nat} {a d : β} :
    (l.set i a).getD i d = if i < l.length then a else d := by
  induction l generalizing i with
  | nil =>
    induction i with
    | zero => rfl
    | succ i => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.set_cons_succ, List.getD_cons_succ, List.length_cons]
      rw [ih]
      by_cases hlt : i < xs.length
      · simp only [hlt, ite_true]
        have hlt' : i + 1 < xs.length + 1 := by omega
        simp only [hlt', ite_true]
      · simp only [hlt, ite_false]
        have hlt' : ¬ i + 1 < xs.length + 1 := by omega
        simp only [hlt', ite_false]

theorem getD_set_ne {β : Type} {l : List β} {i j : Nat} (h : j ≠ i) {a d : β} :
    (l.set i a).getD j d = l.getD j d := by
  induction l generalizing i j with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl h
      | succ j => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.set_cons_succ, List.getD_cons_succ]
        exact ih (fun hh => h (congrArg Nat.succ hh))

theorem getG_setG_self {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    (s : State α γ) (d : Nat) (v : Val α γ) :
    (s.setG d v).getG d =
      if d < s.gpr.length then v else .num (Lane.const 0) (Lane.const 0) := by
  simp only [State.getG, State.setG]
  exact getD_set_self

theorem getG_setG_ne {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    (s : State α γ) {d i : Nat} (h : i ≠ d) (v : Val α γ) :
    (s.setG d v).getG i = s.getG i := by
  simp only [State.getG, State.setG]
  exact getD_set_ne h

theorem getV_eq {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {s1 s2 : State α γ} (h : s1.vr = s2.vr) (i : Nat) : s1.getV i = s2.getV i := by
  simp only [State.getV, h]

/-! ## Record updates keep `AgreeOn` -/

theorem AgreeOn.of_pc {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) {p1 p2 : Nat} (hp : p1 = p2) :
    AgreeOn S { s1 with pc := p1 } { s2 with pc := p2 } where
  pc := hp
  halted := by simpa using h.halted
  tail := by simpa using h.tail
  err := by simpa using h.err
  mem := by simpa using h.mem
  vr := by simpa using h.vr
  assume := by simpa using h.assume
  flags := by intro hS; simpa using h.flags hS
  glen := by simpa using h.glen
  gpr := by intro i hi; simpa only [State.getG] using h.gpr i hi
  gpr16 := by simpa only [State.getG] using h.gpr16

theorem AgreeOn.of_halted {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) {b1 b2 : Bool} (hb : b1 = b2) :
    AgreeOn S { s1 with halted := b1 } { s2 with halted := b2 } where
  pc := by simpa using h.pc
  halted := hb
  tail := by simpa using h.tail
  err := by simpa using h.err
  mem := by simpa using h.mem
  vr := by simpa using h.vr
  assume := by simpa using h.assume
  flags := by intro hS; simpa using h.flags hS
  glen := by simpa using h.glen
  gpr := by intro i hi; simpa only [State.getG] using h.gpr i hi
  gpr16 := by simpa only [State.getG] using h.gpr16

theorem AgreeOn.of_tail {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) {t1 t2 : Option String} (ht : t1 = t2) :
    AgreeOn S { s1 with tail := t1 } { s2 with tail := t2 } where
  pc := by simpa using h.pc
  halted := by simpa using h.halted
  tail := ht
  err := by simpa using h.err
  mem := by simpa using h.mem
  vr := by simpa using h.vr
  assume := by simpa using h.assume
  flags := by intro hS; simpa using h.flags hS
  glen := by simpa using h.glen
  gpr := by intro i hi; simpa only [State.getG] using h.gpr i hi
  gpr16 := by simpa only [State.getG] using h.gpr16

theorem AgreeOn.of_err {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) {e1 e2 : Option String} (he : e1 = e2) :
    AgreeOn S { s1 with err := e1 } { s2 with err := e2 } where
  pc := by simpa using h.pc
  halted := by simpa using h.halted
  tail := by simpa using h.tail
  err := he
  mem := by simpa using h.mem
  vr := by simpa using h.vr
  assume := by simpa using h.assume
  flags := by intro hS; simpa using h.flags hS
  glen := by simpa using h.glen
  gpr := by intro i hi; simpa only [State.getG] using h.gpr i hi
  gpr16 := by simpa only [State.getG] using h.gpr16

theorem AgreeOn.of_mem {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    {m1 m2 : List (Addr γ × Cell α γ)} (hm : m1 = m2) :
    AgreeOn S { s1 with mem := m1 } { s2 with mem := m2 } where
  pc := by simpa using h.pc
  halted := by simpa using h.halted
  tail := by simpa using h.tail
  err := by simpa using h.err
  mem := hm
  vr := by simpa using h.vr
  assume := by simpa using h.assume
  flags := by intro hS; simpa using h.flags hS
  glen := by simpa using h.glen
  gpr := by intro i hi; simpa only [State.getG] using h.gpr i hi
  gpr16 := by simpa only [State.getG] using h.gpr16

theorem AgreeOn.of_vr {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) {v1 v2 : List (List α)} (hv : v1 = v2) :
    AgreeOn S { s1 with vr := v1 } { s2 with vr := v2 } where
  pc := by simpa using h.pc
  halted := by simpa using h.halted
  tail := by simpa using h.tail
  err := by simpa using h.err
  mem := by simpa using h.mem
  vr := hv
  assume := by simpa using h.assume
  flags := by intro hS; simpa using h.flags hS
  glen := by simpa using h.glen
  gpr := by intro i hi; simpa only [State.getG] using h.gpr i hi
  gpr16 := by simpa only [State.getG] using h.gpr16

theorem AgreeOn.of_assume {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    {a1 a2 : List (Cond γ × Bool)} (ha : a1 = a2) :
    AgreeOn S { s1 with assume := a1 } { s2 with assume := a2 } where
  pc := by simpa using h.pc
  halted := by simpa using h.halted
  tail := by simpa using h.tail
  err := by simpa using h.err
  mem := by simpa using h.mem
  vr := by simpa using h.vr
  assume := ha
  flags := by intro hS; simpa using h.flags hS
  glen := by simpa using h.glen
  gpr := by intro i hi; simpa only [State.getG] using h.gpr i hi
  gpr16 := by simpa only [State.getG] using h.gpr16

theorem AgreeOn.of_flags {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    {f1 f2 : Option (γ × γ)} (hf : flg ∉ S → f1 = f2) :
    AgreeOn S { s1 with flags := f1 } { s2 with flags := f2 } where
  pc := by simpa using h.pc
  halted := by simpa using h.halted
  tail := by simpa using h.tail
  err := by simpa using h.err
  mem := by simpa using h.mem
  vr := by simpa using h.vr
  assume := by simpa using h.assume
  flags := hf
  glen := by simpa using h.glen
  gpr := by intro i hi; simpa only [State.getG] using h.gpr i hi
  gpr16 := by simpa only [State.getG] using h.gpr16

theorem AgreeOn.next {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) :
    AgreeOn S s1.next s2.next := by
  unfold State.next
  exact h.of_pc (by rw [h.pc])

theorem AgreeOn.halt {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) :
    AgreeOn S (halt s1) (halt s2) := by
  unfold Hashtree.Asm.X86.halt
  exact h.of_halted rfl

/-- Writing the same value to a register outside `S`, which stays outside. -/
theorem AgreeOn.setG {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) (d : Nat) (v : Val α γ)
    (hd : d ∉ S) (hf : d ≠ flg) : AgreeOn S (s1.setG d v) (s2.setG d v) where
  pc := h.pc
  halted := by simpa only [State.setG] using h.halted
  tail := by simpa only [State.setG] using h.tail
  err := by simpa only [State.setG] using h.err
  mem := by simpa only [State.setG] using h.mem
  vr := by simpa only [State.setG] using h.vr
  assume := by simpa only [State.setG] using h.assume
  flags := by intro hS; simpa only [State.setG] using h.flags hS
  glen := by simp only [State.setG, List.length_set, h.glen]
  gpr := by
    intro i hi
    by_cases hid : i = d
    · subst hid
      rw [getG_setG_self, getG_setG_self]
      by_cases hlt : i < s1.gpr.length
      · simp only [hlt, ite_true, h.glen ▸ hlt]
      · simp only [hlt, ite_false, h.glen ▸ hlt]
    · rw [getG_setG_ne _ hid v, getG_setG_ne _ hid v]
      exact h.gpr i hi
  gpr16 := by
    rw [getG_setG_ne _ (Ne.symm hf) v, getG_setG_ne _ (Ne.symm hf) v]
    exact h.gpr16

/-- Writing a register that leaves `S` (the written values are equal). -/
theorem AgreeOn.setG_diff {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) {d : Nat} {v1 v2 : Val α γ}
    (hv : v1 = v2) (hd : d ≠ flg) :
    AgreeOn (eraseReg S d) (s1.setG d v1) (s2.setG d v2) where
  pc := h.pc
  halted := by simpa only [State.setG] using h.halted
  tail := by simpa only [State.setG] using h.tail
  err := by simpa only [State.setG] using h.err
  mem := by simpa only [State.setG] using h.mem
  vr := by simpa only [State.setG] using h.vr
  assume := by simpa only [State.setG] using h.assume
  flags := by
    intro hS
    have hS' : flg ∉ S := fun hmem =>
      hS (by rw [mem_eraseReg]; exact ⟨hmem, Ne.symm hd⟩)
    simpa only [State.setG] using h.flags hS'
  glen := by simp only [State.setG, List.length_set, h.glen]
  gpr := by
    intro i hi
    by_cases hid : i = d
    · subst hid
      rw [getG_setG_self, getG_setG_self]
      by_cases hlt : i < s1.gpr.length
      · simp only [hlt, ite_true, h.glen ▸ hlt, hv]
      · simp only [hlt, ite_false, h.glen ▸ hlt]
    · have hne : i ∉ S := not_mem_eraseReg hid hi
      rw [getG_setG_ne _ hid v1, getG_setG_ne _ hid v2]
      exact h.gpr i hne
  gpr16 := by
    rw [getG_setG_ne s1 (d := d) (i := flg) (Ne.symm hd) v1, getG_setG_ne s2 (d := d) (i := flg) (Ne.symm hd) v2]
    exact h.gpr16

/-- A 32-bit data write: the register leaves `S`. -/
theorem AgreeOn.setData32 {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) {d : Nat} (hd : d ≠ flg)
    {x1 x2 : α} (hx : x1 = x2) :
    AgreeOn (eraseReg S d) (setData32 s1 d x1) (setData32 s2 d x2) := by
  unfold Hashtree.Asm.X86.setData32
  exact h.setG_diff (by rw [hx]) hd

theorem AgreeOn.clearFlags {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) :
    AgreeOn (eraseReg S flg) (clearFlags s1) (clearFlags s2) := by
  unfold Hashtree.Asm.X86.clearFlags
  exact {
    pc := h.pc
    halted := h.halted
    tail := h.tail
    err := h.err
    mem := h.mem
    vr := h.vr
    assume := h.assume
    flags := by intro _; rfl
    glen := h.glen
    gpr := by
      intro i hi
      by_cases hif : i = flg
      · subst hif; simpa only [State.getG] using h.gpr16
      · simpa only [State.getG] using h.gpr i (not_mem_eraseReg hif hi)
    gpr16 := h.gpr16 }

theorem AgreeOn.setFlags {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]
    {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    {a1 a2 b1 b2 : γ} (ha : a1 = a2) (hb : b1 = b2) :
    AgreeOn (eraseReg S flg) (setFlags s1 a1 b1) (setFlags s2 a2 b2) := by
  unfold Hashtree.Asm.X86.setFlags
  exact {
    pc := h.pc
    halted := h.halted
    tail := h.tail
    err := h.err
    mem := h.mem
    vr := h.vr
    assume := h.assume
    flags := by intro _; rw [ha, hb]
    glen := h.glen
    gpr := by
      intro i hi
      by_cases hif : i = flg
      · subst hif; simpa only [State.getG] using h.gpr16
      · simpa only [State.getG] using h.gpr i (not_mem_eraseReg hif hi)
    gpr16 := h.gpr16 }


section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

/-! ## Register read/write sets -/

/-- Registers read by a memory operand (base and index). -/
def regsOfMemRef (m : MemRef) : List Nat := m.base.toList ++ m.index.toList

/-- Registers read by a general-register operand. -/
def regsOfGSrc : GSrc → List Nat
  | .reg i => [i]
  | .imm _ => []
  | .mem m => regsOfMemRef m

/-- Registers read by a vector operand (`.reg` reads the vector file only). -/
def regsOfVSrc : VSrc → List Nat
  | .reg _ => []
  | .mem m => regsOfMemRef m

/-- General registers read by an instruction. -/
def readsOf : Instr → List Nat
  | .nop => []
  | .vop _ _ _ _ _ s => regsOfVSrc s
  | .vshift _ _ _ _ _ _ => []
  | .vshiftq _ _ _ _ _ => []
  | .vror _ _ _ _ => []
  | .vtern _ _ _ _ _ => []
  | .vload _ _ _ src => regsOfVSrc src
  | .vstore _ m _ => regsOfMemRef m
  | .pshufd _ _ _ _ => []
  | .pshufb _ _ _ _ _ => []
  | .palignr _ _ _ _ _ => []
  | .pblendw _ _ _ => []
  | .shufps _ _ _ _ _ => []
  | .perm2f128 _ _ _ _ => []
  | .inserti128 _ _ m _ => regsOfMemRef m
  | .inserti64x4 _ _ m _ => regsOfMemRef m
  | .permi2d _ _ _ => []
  | .permi2q _ _ _ => []
  | .sha256rnds2 _ _ => []
  | .sha256msg1 _ _ => []
  | .sha256msg2 _ _ => []
  | .mov _ _ src => regsOfGSrc src
  | .movst _ m src => regsOfMemRef m ++ [src]
  | .alu _ _ d src => d :: regsOfGSrc src
  | .sub _ d src => d :: regsOfGSrc src
  | .lea _ m => regsOfMemRef m
  | .ror _ d _ => [d]
  | .shld _ d s _ => [d, s]
  | .shl _ d _ => [d]
  | .bswap _ d => [d]
  | .push r => [rsp, r]
  | .pop r => [rsp]
  | .cmp _ a b => a :: regsOfGSrc b ++ [flg]
  | .test _ a _ => [a, flg]
  | .jcc _ _ => [flg]
  | .jmp _ => []
  | .jccTail _ _ => [flg]
  | .jmpTail _ => []
  | .ret => [rsp]

/-- General registers written by an instruction (in write order).  The flag pseudo-index `flg`
is written by the flag-setting instructions but never written as a general register. -/
def writesOf : Instr → List Nat
  | .nop => []
  | .vop _ _ _ _ _ _ => []
  | .vshift _ _ _ _ _ _ => []
  | .vshiftq _ _ _ _ _ => []
  | .vror _ _ _ _ => []
  | .vtern _ _ _ _ _ => []
  | .vload _ _ _ _ => []
  | .vstore _ _ _ => []
  | .pshufd _ _ _ _ => []
  | .pshufb _ _ _ _ _ => []
  | .palignr _ _ _ _ _ => []
  | .pblendw _ _ _ => []
  | .shufps _ _ _ _ _ => []
  | .perm2f128 _ _ _ _ => []
  | .inserti128 _ _ _ _ => []
  | .inserti64x4 _ _ _ _ => []
  | .permi2d _ _ _ => []
  | .permi2q _ _ _ => []
  | .sha256rnds2 _ _ => []
  | .sha256msg1 _ _ => []
  | .sha256msg2 _ _ => []
  | .mov _ d _ => [d]
  | .movst _ _ _ => []
  | .alu _ _ d _ => [d, flg]
  | .sub _ d _ => [d, flg]
  | .lea d _ => [d]
  | .ror _ d _ => [d, flg]
  | .shld _ d _ _ => [d, flg]
  | .shl _ d _ => [d, flg]
  | .bswap _ d => [d]
  | .push _ => [rsp]
  | .pop r => [r, rsp]
  | .cmp _ _ _ => [flg]
  | .test _ _ _ => [flg]
  | .jcc _ _ => []
  | .jmp _ => []
  | .jccTail _ _ => []
  | .jmpTail _ => []
  | .ret => [rsp]

/-- General registers stored by `setG`/`setData32` (never the flag pseudo-index). -/
def gprWritesOf : Instr → List Nat
  | .mov _ d _ => [d]
  | .alu _ _ d _ => [d]
  | .sub _ d _ => [d]
  | .lea d _ => [d]
  | .ror _ d _ => [d]
  | .shld _ d _ _ => [d]
  | .shl _ d _ => [d]
  | .bswap _ d => [d]
  | .push _ => [rsp]
  | .pop r => [r, rsp]
  | _ => []

/-! ## Membership helpers -/

theorem mem_regsOfMemRef_base {m : MemRef} {b : Nat} (hb : m.base = some b) :
    b ∈ regsOfMemRef m := by
  simp only [regsOfMemRef]
  rw [hb]
  simp

theorem mem_regsOfMemRef_index {m : MemRef} {i : Nat} (hi : m.index = some i) :
    i ∈ regsOfMemRef m := by
  simp only [regsOfMemRef]
  rw [hi]
  simp

/-! ## Reads agree -/

theorem readCell_agree {mem0 : Addr γ → Cell α γ} {S : List Nat} {s1 s2 : State α γ}
    (h : AgreeOn S s1 s2) (a : Addr γ) : readCell mem0 s1 a = readCell mem0 s2 a := by
  simp only [readCell, h.mem]

theorem loadLane_agree {mem0 : Addr γ → Cell α γ} {S : List Nat} {s1 s2 : State α γ}
    (h : AgreeOn S s1 s2) (a : Addr γ) : loadLane mem0 s1 a = loadLane mem0 s2 a := by
  simp only [loadLane, readCell_agree h]

theorem loadLanes_agree {mem0 : Addr γ → Cell α γ} {S : List Nat} {s1 s2 : State α γ}
    (h : AgreeOn S s1 s2) :
    ∀ (a : Addr γ) (n : Nat), loadLanes mem0 s1 a n = loadLanes mem0 s2 a n
  | _, 0 => rfl
  | a, n + 1 => by
    simp only [loadLanes, loadLane_agree h, loadLanes_agree h (a.plusI 4) n]

theorem pbRest_agree {mem0 : Addr γ → Cell α γ} {S : List Nat} {s1 s2 : State α γ}
    (h : AgreeOn S s1 s2) (p a : Addr γ) :
    ∀ (n k : Nat), pbRest mem0 s1 p a n k = pbRest mem0 s2 p a n k
  | 0, _ => rfl
  | n + 1, k => by
    simp only [pbRest, readCell_agree h, pbRest_agree h p a n (k + 1)]

theorem loadVal_agree {mem0 : Addr γ → Cell α γ} {S : List Nat} {s1 s2 : State α γ}
    (h : AgreeOn S s1 s2) (a : Addr γ) : loadVal mem0 s1 a = loadVal mem0 s2 a := by
  simp only [loadVal, readCell_agree h, pbRest_agree h, loadLane_agree h]

theorem regPtr_agree {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    {r : Nat} (hr : r ∉ S) : regPtr s1 r = regPtr s2 r := by
  unfold regPtr
  rw [h.gpr r hr]

theorem baseAddr_agree {ro : Region} {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    (m : MemRef) (hb : ∀ b, m.base = some b → b ∉ S) :
    baseAddr ro s1 m = baseAddr ro s2 m := by
  unfold baseAddr
  cases hro : m.ro with
  | some o => rfl
  | none =>
    cases hmb : m.base with
    | none => rfl
    | some b => exact regPtr_agree h (hb b hmb)

theorem effAddr_agree {ro : Region} {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    (m : MemRef) (hb : ∀ b, m.base = some b → b ∉ S)
    (hi : ∀ i, m.index = some i → i ∉ S) : effAddr ro s1 m = effAddr ro s2 m := by
  unfold effAddr
  rw [baseAddr_agree h m hb]
  split
  · rfl
  · split
    · rfl
    · next i heq => simp only [h.gpr i (hi i heq)]

theorem readVSrc_agree {ro : Region} {mem0 : Addr γ → Cell α γ} {S : List Nat} {s1 s2 : State α γ}
    (h : AgreeOn S s1 s2) (w : Nat) (v : VSrc)
    (hreg : ∀ r, r ∈ regsOfVSrc v → r ∉ S) :
    readVSrc ro mem0 s1 w v = readVSrc ro mem0 s2 w v := by
  cases v with
  | reg i => simp only [readVSrc, getV_eq h.vr]
  | mem m =>
    have hb : ∀ b, m.base = some b → b ∉ S := fun b hmb =>
      hreg b (by simpa only [regsOfVSrc] using mem_regsOfMemRef_base hmb)
    have hi : ∀ i, m.index = some i → i ∉ S := fun i hmi =>
      hreg i (by simpa only [regsOfVSrc] using mem_regsOfMemRef_index hmi)
    simp only [readVSrc, effAddr_agree h m hb hi, loadLanes_agree h]

theorem gData32_agree {ro : Region} {mem0 : Addr γ → Cell α γ} {S : List Nat} {s1 s2 : State α γ}
    (h : AgreeOn S s1 s2) (g : GSrc) (hreg : ∀ r, r ∈ regsOfGSrc g → r ∉ S) :
    gData32 ro mem0 s1 g = gData32 ro mem0 s2 g := by
  cases g with
  | reg i =>
    simp only [gData32]
    rw [h.gpr i (hreg i (by simp only [regsOfGSrc, List.mem_singleton]))]
  | imm v => rfl
  | mem m =>
    have hb : ∀ b, m.base = some b → b ∉ S := fun b hmb =>
      hreg b (by simpa only [regsOfGSrc] using mem_regsOfMemRef_base hmb)
    have hi : ∀ i, m.index = some i → i ∉ S := fun i hmi =>
      hreg i (by simpa only [regsOfGSrc] using mem_regsOfMemRef_index hmi)
    simp only [gData32, effAddr_agree h m hb hi, loadLane_agree h]

theorem gCtl_agree {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    (g : GSrc) (hreg : ∀ r, r ∈ regsOfGSrc g → r ∉ S) : gCtl s1 g = gCtl s2 g := by
  cases g with
  | reg i =>
    simp only [gCtl]
    rw [h.gpr i (hreg i (by simp only [regsOfGSrc, List.mem_singleton]))]
  | imm v => rfl
  | mem m => rfl

/-- Reduction of the `ret` target pattern on a concrete pointer value. -/
theorem retMatch (r : Nat) (o : γ) (X Y : Except String (State α γ)) :
    (match (Val.ptr (⟨r, o⟩ : Addr γ) : Val α γ) with
     | Val.ptr ⟨5, _⟩ => X
     | _ => Y) = (if r = 5 then X else Y) := by
  by_cases h5 : r = 5
  · rw [h5]
    simp
  · rw [if_neg h5]
    split
    · rename_i heq
      exact absurd (by cases heq; rfl) h5
    · rfl

/-! ## Writes keep `AgreeOn` -/

theorem AgreeOn.setV {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    (i : Nat) {v1 v2 : List α} (hv : v1 = v2) :
    AgreeOn S (s1.setV i v1) (s2.setV i v2) := by
  unfold State.setV
  exact h.of_vr (by rw [h.vr, hv])

theorem AgreeOn.setVec {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    (vex : Bool) (w d : Nat) {v1 v2 : List α} (hv : v1 = v2) :
    AgreeOn S (setVec s1 vex w d v1) (setVec s2 vex w d v2) := by
  simp only [Hashtree.Asm.X86.setVec, State.setV]
  refine h.of_vr ?_
  simp only [State.getV, h.vr, hv]

theorem AgreeOn.storeLane {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    (a : Addr γ) {x1 x2 : α} (hx : x1 = x2) :
    AgreeOn S (storeLane s1 a x1) (storeLane s2 a x2) := by
  unfold Hashtree.Asm.storeLane
  exact h.of_mem (by rw [h.mem, hx])

theorem AgreeOn.storeLanes {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2) :
    ∀ (a : Addr γ) (xs : List α), AgreeOn S (storeLanes s1 a xs) (storeLanes s2 a xs)
  | a, [] => h
  | a, x :: xs => (h.storeLane a rfl).storeLanes (a.plusI 4) xs

theorem AgreeOn.storeVal {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    (a : Addr γ) {v1 v2 : Val α γ} (hv : v1 = v2) :
    AgreeOn S (storeVal s1 a v1) (storeVal s2 a v2) := by
  rw [hv]
  cases v2 with
  | num lo hi =>
    simp only [Hashtree.Asm.storeVal]
    exact (h.storeLane a rfl).storeLane (a.plusI 4) rfl
  | ptr p =>
    simp only [Hashtree.Asm.storeVal]
    exact h.of_mem (by rw [h.mem])

theorem AgreeOn.fail {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    {e1 e2 : String} (he : e1 = e2) : AgreeOn S (s1.fail e1) (s2.fail e2) := by
  unfold State.fail
  by_cases herr : s1.err.isSome = true
  · have herr2 : s2.err.isSome = true := by rw [← h.err]; exact herr
    rw [if_pos herr, if_pos herr2]
    exact h.of_halted rfl
  · have herr2 : s2.err.isSome = true → False := by rw [← h.err]; exact herr
    rw [if_neg herr, if_neg herr2]
    have he' : (some e1 : Option String) = some e2 := by rw [he]
    exact (h.of_err he').of_halted rfl

theorem AgreeOn.branch {S : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    (orc : Nat → Bool) (c : Cond γ) (t : Nat) :
    AgreeOn S (s1.branch orc c t) (s2.branch orc c t) := by
  simp only [State.branch]
  cases hd : c.decideC with
  | some b =>
    simp only [Option.isNone_some, Bool.false_eq_true, ite_false]
    cases hb : b with
    | false => exact h.next
    | true => exact h.of_pc rfl
  | none =>
    simp only [Option.isNone_none, ite_true]
    have hpc : orc s1.pc = orc s2.pc := by rw [h.pc]
    rw [hpc]
    cases ho : orc s2.pc with
    | false => exact (h.of_assume (by rw [h.assume])).next
    | true =>
      rw [if_pos rfl]
      refine (h.of_assume (a1 := (c, true) :: s1.assume) (a2 := (c, true) :: s2.assume)
        (by rw [h.assume])).of_pc rfl

/-! ## Agreement of `Except` computations -/

/-- Agreement of two instruction-body results: both succeed in agreeing states, or both fail
with the same message. -/
def AgreeR (T : List Nat) : Except String (State α γ) → Except String (State α γ) → Prop
  | .ok s1, .ok s2 => AgreeOn T s1 s2
  | .error e1, .error e2 => e1 = e2
  | _, _ => False

theorem AgreeR.pure {T : List Nat} {s1 s2 : State α γ} (h : AgreeOn T s1 s2) :
    AgreeR T (.ok s1) (.ok s2) := h

theorem AgreeR.throw {T : List Nat} {e : String} :
    AgreeR T (Except.error e : Except String (State α γ)) (Except.error e) := rfl

theorem AgreeR.ite {T : List Nat} {c : Prop} [Decidable c]
    {a1 a2 b1 b2 : Except String (State α γ)}
    (ha : c → AgreeR T a1 a2) (hb : ¬c → AgreeR T b1 b2) :
    AgreeR T (if c then a1 else b1) (if c then a2 else b2) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact ha hc
  · rw [if_neg hc, if_neg hc]; exact hb hc

theorem bind_ok_agree {β : Type} (b : β) (f : β → Except String (State α γ)) :
    (Except.ok b >>= f) = f b := rfl

theorem bind_error {β : Type} (e : String) (f : β → Except String (State α γ)) :
    ((Except.error e : Except String β) >>= f) = .error e := rfl

theorem AgreeR.bind {T : List Nat} {β : Type} {R1 R2 : Except String β} (hR : R1 = R2)
    {F1 F2 : β → Except String (State α γ)} (hF : ∀ b, AgreeR T (F1 b) (F2 b)) :
    AgreeR T (R1 >>= F1) (R2 >>= F2) := by
  subst hR
  cases R1 with
  | error e => simp only [bind_error]; exact AgreeR.throw
  | ok b => simp only [bind_ok_agree]; exact hF b

/-- `okOr` of agreeing computations that succeed agrees; a shared failure agrees on the old
set (a failed step performs no writes). -/
theorem okOr_agree {S T : List Nat} {s1 s2 : State α γ} (h : AgreeOn S s1 s2)
    (hTS : ∀ r, r ∈ S → r ∈ T) {r1 r2 : Except String (State α γ)} (hr : AgreeR T r1 r2) :
    AgreeOn T (okOr s1 r1) (okOr s2 r2) := by
  cases r1 with
  | error e1 =>
    cases r2 with
    | error e2 => simp only [okOr]; exact (h.fail hr).mono hTS
    | ok s2' => exact hr.elim
  | ok s1' =>
    cases r2 with
    | error e2 => exact hr.elim
    | ok s2' =>
      simp only [okOr]
      exact hr

end

/-! ## Instruction bodies without the halt check

`execE` is `exec`'s body: the same do-blocks, with the three non-`Except` instructions
(`nop`, `jmp`, `jmpTail`) wrapped in `pure`.  `execE_eq` checks the transcription. -/

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

def execE (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr)
    (s : State α γ) : Except String (State α γ) :=
  match i with
  | .nop => .ok s.next
  | .vop op vex w d vs1 vs2 => do
    let b ← readVSrc ro mem0 s w vs2
    let a := (s.getV vs1).take w
    let r := lanes2 (lop op) a b
    pure (setVec s vex w d r).next
  | .vshift k vex w d src n => do
    pure (setVec s vex w d (((s.getV src).take w).map (fun x => shiftL k x n))).next
  | .vshiftq vex w d src n => do
    let r := unpairs ((pairs ((s.getV src).take w)).map (fun (lo, hi) => shrQ lo hi n))
    pure (setVec s vex w d r).next
  | .vror w d src n => do
    pure (setVec s true w d (((s.getV src).take w).map (fun x => Lane.ror x (n % 32)))).next
  | .vtern w d vs1 vs2 imm => do
    let a := (s.getV d).take w
    let b := (s.getV vs1).take w
    let c := (s.getV vs2).take w
    pure (setVec s true w d (lanes3 (Lane.tern imm) a b c)).next
  | .vload vex w d src => do
    let v ← readVSrc ro mem0 s w src
    pure (setVec s vex w d v).next
  | .vstore w m src => do
    let a ← effAddr ro s m
    pure (storeLanes s a ((s.getV src).take w)).next
  | .pshufd vex d src imm => do
    let v := s.getV src
    let r := (List.range 4).map (fun i => v.getD ((imm >>> (2 * i)) % 4) (Lane.const 0))
    pure (setVec s vex 4 d r).next
  | .pshufb vex w d src mask => do
    let r ← pshufbL ((s.getV src).take w) (s.getV mask) w
    pure (setVec s vex w d r).next
  | .palignr vex d vs1 vs2 imm => do
    pure (setVec s vex 4 d (palignrL (s.getV vs1) (s.getV vs2) imm)).next
  | .pblendw d src imm => do
    pure (setVec s false 4 d (pblendwL (s.getV d) (s.getV src) imm)).next
  | .shufps w d vs1 vs2 imm => do
    let a := s.getV vs1; let b := s.getV vs2
    let r := (List.range w).map (fun i =>
      let g := i / 4; let j := i % 4
      let sel := (imm >>> (2 * j)) % 4
      (if j < 2 then a else b).getD (4 * g + sel) (Lane.const 0))
    pure (setVec s true w d r).next
  | .perm2f128 d vs1 vs2 imm => do
    let a := s.getV vs1; let b := s.getV vs2
    let half (ctl : Nat) : List α :=
      if ctl.testBit 3 then zeroLanes 4
      else match ctl % 4 with
        | 0 => a.take 4 | 1 => (a.drop 4).take 4 | 2 => b.take 4 | _ => (b.drop 4).take 4
    pure (setVec s true 8 d (half imm ++ half (imm >>> 4))).next
  | .inserti128 d vs1 m imm => do
    let x ← loadLanes mem0 s (← effAddr ro s m) 4
    let a := (s.getV vs1).take 8
    let r := if imm % 2 = 0 then x ++ a.drop 4 else a.take 4 ++ x
    pure (setVec s true 8 d r).next
  | .inserti64x4 d vs1 m imm => do
    let x ← loadLanes mem0 s (← effAddr ro s m) 8
    let a := s.getV vs1
    let r := if imm % 2 = 0 then x ++ a.drop 8 else a.take 8 ++ x
    pure (setVec s true 16 d r).next
  | .permi2d d vs1 vs2 => do
    let idx ← ctlLanes (s.getV d) 16
    pure (setVec s true 16 d (permi2dP (s.getV vs1) (s.getV vs2) idx)).next
  | .permi2q d vs1 vs2 => do
    let idx ← ctlLanes (s.getV d) 16
    pure (setVec s true 16 d (permi2qP (s.getV vs1) (s.getV vs2) idx)).next
  | .sha256rnds2 d src => do
    pure (setVec s false 4 d (rnds2 (s.getV d) (s.getV src) (s.getV 0))).next
  | .sha256msg1 d src => do
    pure (setVec s false 4 d (msg1 (s.getV d) (s.getV src))).next
  | .sha256msg2 d src => do
    pure (setVec s false 4 d (msg2 (s.getV d) (s.getV src))).next
  | .mov w d src => do
    if w = 64 then
      match src with
      | .reg r => pure (s.setG d (s.getG r)).next
      | .imm v => pure (s.setG d (.ptr ⟨rNum, Ctl.ofInt v⟩)).next
      | .mem m => pure (s.setG d (← loadVal mem0 s (← effAddr ro s m))).next
    else pure (setData32 s d (← gData32 ro mem0 s src)).next
  | .movst w m src => do
    let a ← effAddr ro s m
    if w = 64 then pure (storeVal s a (s.getG src)).next
    else match s.getG src with
      | .num lo _ => pure (storeLane s a lo).next
      | _ => throw "32-bit store of a pointer"
  | .alu op w d src => do
    if w = 64 then
      if op = .xor ∧ src = .reg d then
        pure (clearFlags (s.setG d (.ptr ⟨rNum, Ctl.ofInt 0⟩))).next
      else
      let a ← gCtl s (.reg d)
      let b ← gCtl s src
      match op with
      | .add =>
        if b.region = rNum ∨ a.region = rNum then
          let r : Addr γ := ⟨if b.region = rNum then a.region else b.region, Ctl.add a.off b.off⟩
          pure (setFlags (s.setG d (.ptr r)) r.off (Ctl.ofInt 0)).next
        else throw "pointer + pointer"
      | .and => match Ctl.asInt a.off, Ctl.asInt b.off with
        | some x, some y =>
          match andInt x y with
          | some r =>
            if b.region = rNum ∧ (a.region = rNum ∨ (-64 ≤ y ∧ y < 0)) then
              pure (clearFlags (s.setG d (.ptr ⟨a.region, Ctl.ofInt r⟩))).next
            else throw "and on pointer"
          | none => throw "and form"
        | _, _ => throw "and on symbolic pointer"
      | _ => throw "64-bit data operation"
    else
      if op = .xor ∧ src = .reg d then pure (clearFlags (setData32 s d (Lane.const 0))).next
      else
        let a ← gData32 ro mem0 s (.reg d)
        let b ← gData32 ro mem0 s src
        pure (clearFlags (setData32 s d (lop op a b))).next
  | .sub w d src => do
    if w = 64 then
      let a ← gCtl s (.reg d)
      let b ← gCtl s src
      if b.region = rNum then
        let r : Addr γ := a.plus (Ctl.smul (-1) b.off)
        pure (setFlags (s.setG d (.ptr r)) a.off b.off).next
      else throw "pointer - pointer"
    else throw "32-bit sub"
  | .lea d m => do
    pure (s.setG d (.ptr (← effAddr ro s m))).next
  | .ror w d n => do
    if w = 32 then
      let a ← gData32 ro mem0 s (.reg d)
      pure (clearFlags (setData32 s d (Lane.ror a (n % 32)))).next
    else throw "64-bit ror"
  | .shld w d src n => do
    if w = 32 then
      let a ← gData32 ro mem0 s (.reg d)
      let b ← gData32 ro mem0 s (.reg src)
      let n := n % 32
      let r := if n = 0 then a else Lane.or (Lane.shl a n) (Lane.shr b (32 - n))
      pure (clearFlags (setData32 s d r)).next
    else throw "64-bit shld"
  | .shl w d n => do
    if w = 64 then
      let a ← gCtl s (.reg d)
      if a.region = rNum then
        pure (clearFlags (s.setG d (.ptr ⟨rNum, Ctl.smul (2 ^ (n % 64)) a.off⟩))).next
      else throw "shl of a pointer"
    else
      let a ← gData32 ro mem0 s (.reg d)
      pure (clearFlags (setData32 s d (shiftL .shl a (n % 32)))).next
  | .bswap w d => do
    if w = 32 then
      let a ← gData32 ro mem0 s (.reg d)
      pure (setData32 s d (ofBytes (byteOf a 3) (byteOf a 2) (byteOf a 1) (byteOf a 0))).next
    else throw "64-bit bswap"
  | .push r => do
    match s.getG rsp with
    | .ptr sp =>
      let sp' := sp.plusI (-8)
      pure ((storeVal s sp' (s.getG r)).setG rsp (.ptr sp')).next
    | _ => throw "rsp not a pointer"
  | .pop r => do
    match s.getG rsp with
    | .ptr sp =>
      let v ← loadVal mem0 s sp
      pure ((s.setG r v).setG rsp (.ptr (sp.plusI 8))).next
    | _ => throw "rsp not a pointer"
  | .cmp w a b => do
    if w = 64 then
      let x ← gCtl s (.reg a)
      let y ← gCtl s b
      if y.region = rNum ∨ y.region = x.region then pure (setFlags s x.off y.off).next
      else throw "cmp of unrelated pointers"
    else throw "32-bit cmp"
  | .test w a b => do
    if w = 64 ∧ a = b then
      let x ← gCtl s (.reg a)
      if x.region = rNum then pure (setFlags s x.off (Ctl.ofInt 0)).next
      else throw "test of a pointer"
    else throw "test form"
  | .jcc c t => do
    match s.flags with
    | some (a, b) => pure (s.branch orc (ccCond c a b) t)
    | none => throw "branch on clobbered flags"
  | .jmp t => .ok { s with pc := t }
  | .jccTail c name => do
    match s.flags with
    | some (a, b) =>
      let s' := s.branch orc (ccCond c a b) 1000000000
      if s'.pc = 1000000000 then pure { s' with pc := s.pc, halted := true, tail := some name }
      else pure s'
    | none => throw "branch on clobbered flags"
  | .jmpTail name => .ok { s with halted := true, tail := some name }
  | .ret => do
    match s.getG rsp with
    | .ptr sp =>
      match ← loadVal mem0 s sp with
      | .ptr ⟨5, _⟩ => pure (halt (s.setG rsp (.ptr (sp.plusI 8))))
      | _ => throw "ret to unknown address"
    | _ => throw "rsp not a pointer"

theorem execE_eq (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr)
    (s : State α γ) :
    exec ro mem0 orc i s =
      if s.halted then s else okOr s (execE ro mem0 orc i s) := by
  cases i <;> rfl

end

/-! ## One step preserves agreement

`execE_agree`: an instruction that reads no register of `S` takes two agreeing states to two
states that agree on `S` minus the registers the instruction writes (or to the same error). -/

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

/-- Remove each listed register in turn from the "may differ" set. -/
def eraseAll (S : List Nat) : List Nat → List Nat
  | [] => S
  | w :: ws => eraseAll (eraseReg S w) ws

theorem mem_eraseAll : ∀ (S ws : List Nat) {i : Nat}, i ∈ eraseAll S ws → i ∈ S
  | _, [], i, hi => hi
  | S, w :: ws, i, hi => by
    have h1 : i ∈ eraseReg S w := mem_eraseAll (eraseReg S w) ws hi
    exact (mem_eraseReg.mp h1).1

theorem execE_agree {ro : Region} {mem0 : Addr γ → Cell α γ} {orc : Nat → Bool} {S : List Nat}
    {s1 s2 : State α γ} (h : AgreeOn S s1 s2) (i : Instr)
    (hread : ∀ r, r ∈ readsOf i → r ∉ S)
    (hgpr : ∀ d, d ∈ gprWritesOf i → d ≠ flg) :
    AgreeR (eraseAll S (writesOf i)) (execE ro mem0 orc i s1) (execE ro mem0 orc i s2) := by
  cases i with
  | nop => exact AgreeR.pure h.next
  | vop op vex w d vs1 vs2 =>
    refine AgreeR.bind (readVSrc_agree h w vs2 (fun r hr => hread r (by simpa only [readsOf] using hr))) (fun b => ?_)
    refine AgreeR.pure ?_
    have hv : lanes2 (lop op) ((s1.getV vs1).take w) b = lanes2 (lop op) ((s2.getV vs1).take w) b := by
      rw [getV_eq h.vr vs1]
    exact (h.setVec vex w d hv).next
  | vshift k vex w d src n =>
    refine AgreeR.pure ?_
    have hv : ((s1.getV src).take w).map (fun x => shiftL k x n) = ((s2.getV src).take w).map (fun x => shiftL k x n) := by
      rw [getV_eq h.vr src]
    exact (h.setVec vex w d hv).next
  | vshiftq vex w d src n =>
    refine AgreeR.pure ?_
    have hv : unpairs ((pairs ((s1.getV src).take w)).map (fun (lo, hi) => shrQ lo hi n)) =
        unpairs ((pairs ((s2.getV src).take w)).map (fun (lo, hi) => shrQ lo hi n)) := by
      rw [getV_eq h.vr src]
    exact (h.setVec vex w d hv).next
  | vror w d src n =>
    refine AgreeR.pure ?_
    have hv : ((s1.getV src).take w).map (fun x => Lane.ror x (n % 32)) = ((s2.getV src).take w).map (fun x => Lane.ror x (n % 32)) := by
      rw [getV_eq h.vr src]
    exact (h.setVec true w d hv).next
  | vtern w d vs1 vs2 imm =>
    refine AgreeR.pure ?_
    have hv : lanes3 (Lane.tern imm) ((s1.getV d).take w) ((s1.getV vs1).take w) ((s1.getV vs2).take w) =
        lanes3 (Lane.tern imm) ((s2.getV d).take w) ((s2.getV vs1).take w) ((s2.getV vs2).take w) := by
      rw [getV_eq h.vr d, getV_eq h.vr vs1, getV_eq h.vr vs2]
    exact (h.setVec true w d hv).next
  | vload vex w d src =>
    refine AgreeR.bind (readVSrc_agree h w src (fun r hr => hread r (by simpa only [readsOf] using hr))) (fun v => ?_)
    exact AgreeR.pure ((h.setVec vex w d rfl).next)
  | vstore w m src =>
    refine AgreeR.bind (effAddr_agree h m
      (fun b hb => hread b (by simpa only [readsOf] using mem_regsOfMemRef_base hb))
      (fun j hj => hread j (by simpa only [readsOf] using mem_regsOfMemRef_index hj))) (fun a => ?_)
    refine AgreeR.pure ?_
    have hv : (s1.getV src).take w = (s2.getV src).take w := by rw [getV_eq h.vr src]
    rw [hv]
    exact (h.storeLanes a _).next
  | pshufd vex d src imm =>
    refine AgreeR.pure ?_
    have hv : (List.range 4).map (fun i => (s1.getV src).getD ((imm >>> (2 * i)) % 4) (Lane.const 0)) =
        (List.range 4).map (fun i => (s2.getV src).getD ((imm >>> (2 * i)) % 4) (Lane.const 0)) := by
      rw [getV_eq h.vr src]
    exact (h.setVec vex 4 d hv).next
  | pshufb vex w d src mask =>
    refine AgreeR.bind ?_ (fun r => ?_)
    · rw [getV_eq h.vr src, getV_eq h.vr mask]
    · exact AgreeR.pure ((h.setVec vex w d rfl).next)
  | palignr vex d vs1 vs2 imm =>
    refine AgreeR.pure ?_
    have hv : palignrL (s1.getV vs1) (s1.getV vs2) imm = palignrL (s2.getV vs1) (s2.getV vs2) imm := by
      rw [getV_eq h.vr vs1, getV_eq h.vr vs2]
    exact (h.setVec vex 4 d hv).next
  | pblendw d src imm =>
    refine AgreeR.pure ?_
    have hv : pblendwL (s1.getV d) (s1.getV src) imm = pblendwL (s2.getV d) (s2.getV src) imm := by
      rw [getV_eq h.vr d, getV_eq h.vr src]
    exact (h.setVec false 4 d hv).next
  | shufps w d vs1 vs2 imm =>
    refine AgreeR.pure ?_
    have hv : (List.range w).map (fun i =>
        let g := i / 4; let j := i % 4
        let sel := (imm >>> (2 * j)) % 4
        (if j < 2 then s1.getV vs1 else s1.getV vs2).getD (4 * g + sel) (Lane.const 0)) =
      (List.range w).map (fun i =>
        let g := i / 4; let j := i % 4
        let sel := (imm >>> (2 * j)) % 4
        (if j < 2 then s2.getV vs1 else s2.getV vs2).getD (4 * g + sel) (Lane.const 0)) := by
      rw [getV_eq h.vr vs1, getV_eq h.vr vs2]
    exact (h.setVec true w d hv).next
  | perm2f128 d vs1 vs2 imm =>
    refine AgreeR.pure ?_
    have hv : (let a := s1.getV vs1; let b := s1.getV vs2
        let half (ctl : Nat) : List α :=
          if ctl.testBit 3 then zeroLanes 4
          else match ctl % 4 with
            | 0 => a.take 4 | 1 => (a.drop 4).take 4 | 2 => b.take 4 | _ => (b.drop 4).take 4
        half imm ++ half (imm >>> 4)) =
      (let a := s2.getV vs1; let b := s2.getV vs2
        let half (ctl : Nat) : List α :=
          if ctl.testBit 3 then zeroLanes 4
          else match ctl % 4 with
            | 0 => a.take 4 | 1 => (a.drop 4).take 4 | 2 => b.take 4 | _ => (b.drop 4).take 4
        half imm ++ half (imm >>> 4)) := by
      rw [getV_eq h.vr vs1, getV_eq h.vr vs2]
    exact (h.setVec true 8 d hv).next
  | inserti128 d vs1 m imm =>
    refine AgreeR.bind (effAddr_agree h m
      (fun b hb => hread b (by simpa only [readsOf] using mem_regsOfMemRef_base hb))
      (fun j hj => hread j (by simpa only [readsOf] using mem_regsOfMemRef_index hj))) (fun a => ?_)
    refine AgreeR.bind (loadLanes_agree h a 4) (fun x => ?_)
    refine AgreeR.pure ?_
    have hv : (if imm % 2 = 0 then x ++ ((s1.getV vs1).take 8).drop 4 else ((s1.getV vs1).take 8).take 4 ++ x) =
        (if imm % 2 = 0 then x ++ ((s2.getV vs1).take 8).drop 4 else ((s2.getV vs1).take 8).take 4 ++ x) := by
      rw [getV_eq h.vr vs1]
    exact (h.setVec true 8 d hv).next
  | inserti64x4 d vs1 m imm =>
    refine AgreeR.bind (effAddr_agree h m
      (fun b hb => hread b (by simpa only [readsOf] using mem_regsOfMemRef_base hb))
      (fun j hj => hread j (by simpa only [readsOf] using mem_regsOfMemRef_index hj))) (fun a => ?_)
    refine AgreeR.bind (loadLanes_agree h a 8) (fun x => ?_)
    refine AgreeR.pure ?_
    have hv : (if imm % 2 = 0 then x ++ (s1.getV vs1).drop 8 else (s1.getV vs1).take 8 ++ x) =
        (if imm % 2 = 0 then x ++ (s2.getV vs1).drop 8 else (s2.getV vs1).take 8 ++ x) := by
      rw [getV_eq h.vr vs1]
    exact (h.setVec true 16 d hv).next
  | permi2d d vs1 vs2 =>
    refine AgreeR.bind ?_ (fun idx => ?_)
    · rw [getV_eq h.vr d]
    · refine AgreeR.pure ?_
      have hv : permi2dP (s1.getV vs1) (s1.getV vs2) idx = permi2dP (s2.getV vs1) (s2.getV vs2) idx := by
        rw [getV_eq h.vr vs1, getV_eq h.vr vs2]
      exact (h.setVec true 16 d hv).next
  | permi2q d vs1 vs2 =>
    refine AgreeR.bind ?_ (fun idx => ?_)
    · rw [getV_eq h.vr d]
    · refine AgreeR.pure ?_
      have hv : permi2qP (s1.getV vs1) (s1.getV vs2) idx = permi2qP (s2.getV vs1) (s2.getV vs2) idx := by
        rw [getV_eq h.vr vs1, getV_eq h.vr vs2]
      exact (h.setVec true 16 d hv).next
  | sha256rnds2 d src =>
    refine AgreeR.pure ?_
    have hv : rnds2 (s1.getV d) (s1.getV src) (s1.getV 0) = rnds2 (s2.getV d) (s2.getV src) (s2.getV 0) := by
      rw [getV_eq h.vr d, getV_eq h.vr src, getV_eq h.vr 0]
    exact (h.setVec false 4 d hv).next
  | sha256msg1 d src =>
    refine AgreeR.pure ?_
    have hv : msg1 (s1.getV d) (s1.getV src) = msg1 (s2.getV d) (s2.getV src) := by
      rw [getV_eq h.vr d, getV_eq h.vr src]
    exact (h.setVec false 4 d hv).next
  | sha256msg2 d src =>
    refine AgreeR.pure ?_
    have hv : msg2 (s1.getV d) (s1.getV src) = msg2 (s2.getV d) (s2.getV src) := by
      rw [getV_eq h.vr d, getV_eq h.vr src]
    exact (h.setVec false 4 d hv).next
  | mov w d src =>
    simp only [execE]
    by_cases hw : w = 64
    · rw [if_pos hw, if_pos hw]
      cases src with
      | reg r =>
        have hg : s1.getG r = s2.getG r := h.gpr r (hread r (by simp [readsOf, regsOfGSrc]))
        exact AgreeR.pure ((h.setG_diff hg (hgpr d (by simp [gprWritesOf]))).next)
      | imm v =>
        exact AgreeR.pure ((h.setG_diff rfl (hgpr d (by simp [gprWritesOf]))).next)
      | mem m =>
        refine AgreeR.bind (effAddr_agree h m
          (fun b hb => hread b (by simp only [readsOf, regsOfGSrc]; exact mem_regsOfMemRef_base hb))
          (fun j hj => hread j (by simp only [readsOf, regsOfGSrc]; exact mem_regsOfMemRef_index hj))) (fun a => ?_)
        refine AgreeR.bind (loadVal_agree h a) (fun v => ?_)
        exact AgreeR.pure ((h.setG_diff rfl (hgpr d (by simp [gprWritesOf]))).next)
    · rw [if_neg hw, if_neg hw]
      refine AgreeR.bind (gData32_agree h src (fun r hr => hread r (by simpa only [readsOf] using hr))) (fun x => ?_)
      exact AgreeR.pure ((h.setData32 (hgpr d (by simp [gprWritesOf])) rfl).next)
  | movst w m src =>
    refine AgreeR.bind (effAddr_agree h m
      (fun b hb => hread b (by simp [readsOf, List.mem_append]; exact Or.inl (mem_regsOfMemRef_base hb)))
      (fun j hj => hread j (by simp [readsOf, List.mem_append]; exact Or.inl (mem_regsOfMemRef_index hj)))) (fun a => ?_)
    by_cases hw : w = 64
    · rw [if_pos hw, if_pos hw]
      have hg : s1.getG src = s2.getG src := h.gpr src (hread src (by simp [readsOf]))
      exact AgreeR.pure ((h.storeVal a hg).next)
    · rw [if_neg hw, if_neg hw]
      have hg : s1.getG src = s2.getG src := h.gpr src (hread src (by simp [readsOf]))
      rw [hg]
      cases hv : s2.getG src with
      | num lo hi => exact AgreeR.pure ((h.storeLane a rfl).next)
      | ptr p => exact AgreeR.throw
  | alu op w d src =>
    simp only [execE]
    by_cases hw : w = 64
    · rw [if_pos hw, if_pos hw]
      by_cases hx : op = .xor ∧ src = .reg d
      · rw [if_pos hx, if_pos hx]
        exact AgreeR.pure (((h.setG_diff rfl (hgpr d (by simp [gprWritesOf]))).clearFlags).next)
      · rw [if_neg hx, if_neg hx]
        refine AgreeR.bind (gCtl_agree h (.reg d) (fun r hr => hread r (by
          have h1 : r = d := List.mem_singleton.mp hr
          rw [h1]
          simp [readsOf]))) (fun a => ?_)
        refine AgreeR.bind (gCtl_agree h src (fun r hr => hread r (List.mem_cons_of_mem d hr))) (fun bb => ?_)
        cases op with
        | add =>
          by_cases hz : bb.region = rNum ∨ a.region = rNum
          · rw [if_pos hz, if_pos hz]
            exact AgreeR.pure (((h.setG_diff rfl (hgpr d (by simp [gprWritesOf]))).setFlags rfl rfl).next)
          · rw [if_neg hz, if_neg hz]
            exact AgreeR.throw
        | and =>
          cases hxa : Ctl.asInt a.off with
          | none => dsimp only; exact AgreeR.throw
          | some x =>
            dsimp only
            cases hyb : Ctl.asInt bb.off with
            | none => dsimp only; exact AgreeR.throw
            | some y =>
              dsimp only
              cases hnd : andInt x y with
              | none => dsimp only; exact AgreeR.throw
              | some r =>
                dsimp only
                by_cases hz : bb.region = rNum ∧ (a.region = rNum ∨ (-64 ≤ y ∧ y < 0))
                · rw [if_pos hz, if_pos hz]
                  exact AgreeR.pure (((h.setG_diff rfl (hgpr d (by simp [gprWritesOf]))).clearFlags).next)
                · rw [if_neg hz, if_neg hz]
                  exact AgreeR.throw
        | xor => exact AgreeR.throw
        | or => exact AgreeR.throw
    · rw [if_neg hw, if_neg hw]
      by_cases hx : op = .xor ∧ src = .reg d
      · rw [if_pos hx, if_pos hx]
        exact AgreeR.pure (((h.setData32 (hgpr d (by simp [gprWritesOf])) rfl).clearFlags).next)
      · rw [if_neg hx, if_neg hx]
        refine AgreeR.bind (gData32_agree h (.reg d) (fun r hr => hread r (by
          have h1 : r = d := List.mem_singleton.mp hr
          rw [h1]
          simp [readsOf]))) (fun a => ?_)
        refine AgreeR.bind (gData32_agree h src (fun r hr => hread r (List.mem_cons_of_mem d hr))) (fun bb => ?_)
        exact AgreeR.pure (((h.setData32 (hgpr d (by simp [gprWritesOf])) rfl).clearFlags).next)
  | sub w d src =>
    simp only [execE]
    by_cases hw : w = 64
    · rw [if_pos hw, if_pos hw]
      refine AgreeR.bind (gCtl_agree h (.reg d) (fun r hr => hread r (by
        have h1 : r = d := List.mem_singleton.mp hr
        rw [h1]
        simp [readsOf]))) (fun a => ?_)
      refine AgreeR.bind (gCtl_agree h src (fun r hr => hread r (List.mem_cons_of_mem d hr))) (fun bb => ?_)
      by_cases hz : bb.region = rNum
      · rw [if_pos hz, if_pos hz]
        exact AgreeR.pure (((h.setG_diff rfl (hgpr d (by simp [gprWritesOf]))).setFlags rfl rfl).next)
      · rw [if_neg hz, if_neg hz]
        exact AgreeR.throw
    · rw [if_neg hw, if_neg hw]
      exact AgreeR.throw
  | lea d m =>
    refine AgreeR.bind (effAddr_agree h m
      (fun b hb => hread b (by simpa only [readsOf] using mem_regsOfMemRef_base hb))
      (fun j hj => hread j (by simpa only [readsOf] using mem_regsOfMemRef_index hj))) (fun a => ?_)
    exact AgreeR.pure ((h.setG_diff rfl (hgpr d (by simp [gprWritesOf]))).next)
  | ror w d n =>
    simp only [execE]
    by_cases hw : w = 32
    · rw [if_pos hw, if_pos hw]
      refine AgreeR.bind (gData32_agree h (.reg d) (fun r hr => hread r (by
        have h1 : r = d := List.mem_singleton.mp hr
        rw [h1]
        simp [readsOf]))) (fun a => ?_)
      exact AgreeR.pure (((h.setData32 (hgpr d (by simp [gprWritesOf])) rfl).clearFlags).next)
    · rw [if_neg hw, if_neg hw]
      exact AgreeR.throw
  | shld w d src n =>
    simp only [execE]
    by_cases hw : w = 32
    · rw [if_pos hw, if_pos hw]
      refine AgreeR.bind (gData32_agree h (.reg d) (fun r hr => hread r (by
        have h1 : r = d := List.mem_singleton.mp hr
        rw [h1]
        simp [readsOf]))) (fun a => ?_)
      refine AgreeR.bind (gData32_agree h (.reg src) (fun r hr => hread r (by
        have h1 : r = src := List.mem_singleton.mp hr
        rw [h1]
        simp [readsOf]))) (fun bb => ?_)
      exact AgreeR.pure (((h.setData32 (hgpr d (by simp [gprWritesOf])) rfl).clearFlags).next)
    · rw [if_neg hw, if_neg hw]
      exact AgreeR.throw
  | shl w d n =>
    simp only [execE]
    by_cases hw : w = 64
    · rw [if_pos hw, if_pos hw]
      refine AgreeR.bind (gCtl_agree h (.reg d) (fun r hr => hread r (by
        have h1 : r = d := List.mem_singleton.mp hr
        rw [h1]
        simp [readsOf]))) (fun a => ?_)
      by_cases hz : a.region = rNum
      · rw [if_pos hz, if_pos hz]
        exact AgreeR.pure (((h.setG_diff rfl (hgpr d (by simp [gprWritesOf]))).clearFlags).next)
      · rw [if_neg hz, if_neg hz]
        exact AgreeR.throw
    · rw [if_neg hw, if_neg hw]
      refine AgreeR.bind (gData32_agree h (.reg d) (fun r hr => hread r (by
        have h1 : r = d := List.mem_singleton.mp hr
        rw [h1]
        simp [readsOf]))) (fun a => ?_)
      exact AgreeR.pure (((h.setData32 (hgpr d (by simp [gprWritesOf])) rfl).clearFlags).next)
  | bswap w d =>
    simp only [execE]
    by_cases hw : w = 32
    · rw [if_pos hw, if_pos hw]
      refine AgreeR.bind (gData32_agree h (.reg d) (fun r hr => hread r (by
        have h1 : r = d := List.mem_singleton.mp hr
        rw [h1]
        simp [readsOf]))) (fun a => ?_)
      exact AgreeR.pure ((h.setData32 (hgpr d (by simp [gprWritesOf])) rfl).next)
    · rw [if_neg hw, if_neg hw]
      exact AgreeR.throw
  | push r =>
    simp only [execE]
    have hg : s1.getG rsp = s2.getG rsp := h.gpr rsp (hread rsp (by simp [readsOf]))
    have hr : s1.getG r = s2.getG r := h.gpr r (hread r (by simp [readsOf]))
    rw [hg]
    cases hsp : s2.getG rsp with
    | num lo hi => exact AgreeR.throw
    | ptr sp =>
      exact AgreeR.pure (((h.storeVal (sp.plusI (-8)) hr).setG_diff (d := rsp) rfl
        (hgpr rsp (by simp [gprWritesOf]))).next)
  | pop r =>
    simp only [execE]
    have hg : s1.getG rsp = s2.getG rsp := h.gpr rsp (hread rsp (by simp [readsOf]))
    rw [hg]
    cases hsp : s2.getG rsp with
    | num lo hi => exact AgreeR.throw
    | ptr sp =>
      refine AgreeR.bind (loadVal_agree h sp) (fun v => ?_)
      exact AgreeR.pure (((h.setG_diff (d := r) rfl (hgpr r (by simp [gprWritesOf]))).setG_diff
        (d := rsp) rfl (hgpr rsp (by simp [gprWritesOf]))).next)
  | cmp w a b =>
    simp only [execE]
    by_cases hw : w = 64
    · rw [if_pos hw, if_pos hw]
      refine AgreeR.bind (gCtl_agree h (.reg a) (fun r hr => hread r (by
        have h1 : r = a := List.mem_singleton.mp hr
        rw [h1]
        simp [readsOf]))) (fun x => ?_)
      refine AgreeR.bind (gCtl_agree h b (fun r hr => hread r (by
        simp [readsOf, regsOfGSrc]
        exact Or.inr (Or.inl hr)))) (fun y => ?_)
      by_cases hz : y.region = rNum ∨ y.region = x.region
      · rw [if_pos hz, if_pos hz]
        exact AgreeR.pure ((h.setFlags rfl rfl).next)
      · rw [if_neg hz, if_neg hz]
        exact AgreeR.throw
    · rw [if_neg hw, if_neg hw]
      exact AgreeR.throw
  | test w a b =>
    simp only [execE]
    by_cases hc : w = 64 ∧ a = b
    · rw [if_pos hc, if_pos hc]
      refine AgreeR.bind (gCtl_agree h (.reg a) (fun r hr => hread r (by
        have h1 : r = a := List.mem_singleton.mp hr
        rw [h1]
        simp [readsOf]))) (fun x => ?_)
      by_cases hz : x.region = rNum
      · rw [if_pos hz, if_pos hz]
        exact AgreeR.pure ((h.setFlags rfl rfl).next)
      · rw [if_neg hz, if_neg hz]
        exact AgreeR.throw
    · rw [if_neg hc, if_neg hc]
      exact AgreeR.throw
  | jcc c t =>
    simp only [execE]
    have hf : s1.flags = s2.flags := h.flags (hread flg (by simp [readsOf]))
    rw [hf]
    cases hfl : s2.flags with
    | none => exact AgreeR.throw
    | some p =>
      cases p with
      | mk a b => exact AgreeR.pure (h.branch orc (ccCond c a b) t)
  | jmp t => exact AgreeR.pure (h.of_pc rfl)
  | jccTail c name =>
    simp only [execE]
    have hf : s1.flags = s2.flags := h.flags (hread flg (by simp [readsOf]))
    rw [hf]
    cases hfl : s2.flags with
    | none => exact AgreeR.throw
    | some p =>
      cases p with
      | mk a b =>
        dsimp only
        have hb : AgreeOn S (s1.branch orc (ccCond c a b) 1000000000)
            (s2.branch orc (ccCond c a b) 1000000000) := h.branch orc (ccCond c a b) 1000000000
        rw [hb.pc]
        by_cases htake : (s2.branch orc (ccCond c a b) 1000000000).pc = 1000000000
        · rw [if_pos htake, if_pos htake]
          refine AgreeR.pure ?_
          exact { pc := h.pc, halted := rfl, tail := rfl, err := hb.err, mem := hb.mem, vr := hb.vr, assume := hb.assume, flags := hb.flags, glen := hb.glen, gpr := hb.gpr, gpr16 := hb.gpr16 }
        · rw [if_neg htake, if_neg htake]
          exact AgreeR.pure hb
  | jmpTail name =>
    refine AgreeR.pure ?_
    exact { pc := h.pc, halted := rfl, tail := rfl, err := h.err, mem := h.mem, vr := h.vr, assume := h.assume, flags := h.flags, glen := h.glen, gpr := h.gpr, gpr16 := h.gpr16 }
  | ret =>
    simp only [execE]
    have hg : s1.getG rsp = s2.getG rsp := h.gpr rsp (hread rsp (by simp [readsOf]))
    rw [hg]
    cases hsp : s2.getG rsp with
    | num lo hi => exact AgreeR.throw
    | ptr sp =>
      refine AgreeR.bind (loadVal_agree h sp) (fun v => ?_)
      cases v with
      | num lo hi => exact AgreeR.throw
      | ptr p =>
        cases p with
        | mk r o =>
          rw [retMatch r o (pure (halt (s1.setG rsp (.ptr (sp.plusI 8)))))
                (throw "ret to unknown address"),
              retMatch r o (pure (halt (s2.setG rsp (.ptr (sp.plusI 8)))))
                (throw "ret to unknown address")]
          by_cases h5 : r = 5
          · rw [if_pos h5, if_pos h5]
            exact AgreeR.pure ((h.setG_diff (d := rsp) rfl (by decide)).halt)
          · rw [if_neg h5, if_neg h5]
            exact AgreeR.throw

end

/-! ## Successor positions of one instruction

`successors pc i` lists the program counters a successful execution of `i` can continue at:
the jump target (`jmp`), both arms of a branch, `pc + 1`, or nothing for `ret` and the two
tail-call forms (whose result is the same state, stopped).  `execE_ok_pc` shows that every
successful body leaves the state either at `pc` or at one of those successors; `run_agree` uses
it to carry its register invariant across a step of the run. -/

section
variable {α γ : Type}

/-- A property that holds of every successful result of a computation. -/
def OkProp (P : State α γ → Prop) (r : Except String (State α γ)) : Prop := ∀ s', r = .ok s' → P s'

theorem OkProp_pure (P : State α γ → Prop) (x : State α γ) (h : P x) : OkProp P (pure x) := by
  intro s' hs; cases hs; exact h

theorem OkProp_throw (P : State α γ → Prop) (e : String) : OkProp P (throw e) := by
  intro s' hs; cases hs

theorem OkProp_bind {β : Type} (P : State α γ → Prop) (m : Except String β)
    (f : β → Except String (State α γ)) (h : ∀ a, OkProp P (f a)) : OkProp P (m >>= f) := by
  intro s' hs
  cases hm : m with
  | error e => rw [hm] at hs; cases hs
  | ok a => rw [hm] at hs; exact h a s' hs

theorem OkProp_ite (P : State α γ → Prop) (c : Prop) [Decidable c] (a b : Except String (State α γ))
    (ha : c → OkProp P a) (hb : ¬ c → OkProp P b) : OkProp P (if c then a else b) := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

end

section
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

-- the pc lemmas are about the record updates alone, which take no instance argument
set_option linter.unusedSectionVars false

/-! ### State updates keep the pc -/

@[simp] theorem setG_pc (s : State α γ) (i : Nat) (v : Val α γ) : (s.setG i v).pc = s.pc := rfl
@[simp] theorem setV_pc (s : State α γ) (i : Nat) (v : List α) : (s.setV i v).pc = s.pc := rfl
@[simp] theorem next_pc (s : State α γ) : s.next.pc = s.pc + 1 := rfl
@[simp] theorem setVec_pc (s : State α γ) (vex : Bool) (w d : Nat) (v : List α) :
    (setVec s vex w d v).pc = s.pc := rfl
@[simp] theorem setData32_pc (s : State α γ) (d : Nat) (x : α) : (setData32 s d x).pc = s.pc := rfl
@[simp] theorem clearFlags_pc (s : State α γ) : (clearFlags s).pc = s.pc := rfl
@[simp] theorem setFlags_pc (s : State α γ) (a b : γ) : (setFlags s a b).pc = s.pc := rfl
@[simp] theorem halt_pc (s : State α γ) : (halt s).pc = s.pc := rfl
@[simp] theorem storeLane_pc (s : State α γ) (a : Addr γ) (x : α) : (storeLane s a x).pc = s.pc := rfl
@[simp] theorem storeLanes_pc : ∀ (l : List α) (s : State α γ) (a : Addr γ),
    (storeLanes s a l).pc = s.pc
  | [], _, _ => rfl
  | x :: xs, s, a => by simp only [storeLanes, storeLanes_pc xs, storeLane_pc]
@[simp] theorem storeVal_pc (s : State α γ) (a : Addr γ) (v : Val α γ) : (storeVal s a v).pc = s.pc := by
  cases v with
  | num lo hi => simp only [storeVal, storeLane_pc]
  | ptr p => rfl

/-- A branch lands at its target or after it (`State.branch` records the condition it took). -/
theorem branch_pc_cases (orc : Nat → Bool) (s : State α γ) (c : Cond γ) (t : Nat) :
    (s.branch orc c t).pc = t ∨ (s.branch orc c t).pc = s.pc + 1 := by
  unfold State.branch
  dsimp only
  cases hd : c.decideC with
  | some b =>
    cases b <;> simp [State.next]
  | none =>
    by_cases ho : orc s.pc <;> simp [State.next, ho]

/-- The pc of the next instruction: `pc + 1`, a jump target, or unchanged (`ret`, tail calls). -/
def successors (pc : Nat) : Instr → List Nat
  | .jmp t => [t]
  | .jcc _ t => [t, pc + 1]
  | .jmpTail _ => []
  | .jccTail _ _ => [pc + 1]
  | .ret => []
  | _ => [pc + 1]

/-- Every successful instruction body lands at `pc` again or at one of its successors. -/
theorem execE_pc_ok (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr)
    (s : State α γ) :
    OkProp (fun s' => s'.pc = s.pc ∨ s'.pc ∈ successors s.pc i) (execE ro mem0 orc i s) := by
  cases i <;> dsimp only [execE]
  case jmp t =>
    apply OkProp_pure
    exact Or.inr (by simp [successors])
  case jmpTail name =>
    apply OkProp_pure
    exact Or.inl rfl
  case jcc c t =>
    split
    · apply OkProp_pure
      rcases branch_pc_cases orc s _ t with h | h
      · exact Or.inr (by rw [h]; simp [successors])
      · exact Or.inr (by rw [h]; simp [successors])
    · apply OkProp_throw
  case jccTail c name =>
    split
    · apply OkProp_ite
      · intro _
        apply OkProp_pure
        exact Or.inl rfl
      · intro hne
        apply OkProp_pure
        rcases branch_pc_cases orc s _ 1000000000 with h | h
        · exact absurd h hne
        · exact Or.inr (by rw [h]; simp [successors])
    · apply OkProp_throw
  case ret =>
    split
    · apply OkProp_bind
      intro v
      split
      · apply OkProp_pure
        exact Or.inl rfl
      · apply OkProp_throw
    · apply OkProp_throw
  all_goals
    (repeat (first
      | apply OkProp_bind; intro _
      | apply OkProp_throw
      | apply OkProp_ite <;> intro _
      | (apply OkProp_pure; simp [successors])
      | split))

/-- A successful instruction leaves the pc at `pc` or at a successor of `i`. -/
theorem execE_ok_pc (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) (i : Instr)
    (s s' : State α γ) (h : execE ro mem0 orc i s = .ok s') :
    s'.pc = s.pc ∨ s'.pc ∈ successors s.pc i :=
  execE_pc_ok ro mem0 orc i s s' h

/-! ## Runs preserve agreement

`run_agree` is the congruence for `run`: if the reference run finishes without an error and the
analysis `Ds` justifies every instruction it executes (it reads no register of `Ds pc`, it
writes no flag, and the registers it writes leave the successor's `Ds`), then the peer run
executes the same instructions and ends in a state that agrees on `Ds` of the final pc.  The
induction is driven by the reference run's success: a step that failed would make the final
error non-`none`, and a step that succeeded keeps agreement by `execE_agree`; the successor
containment is `execE_ok_pc`.  No disjunctive step relation is needed, because the only user of
the congruence already knows that the reference run succeeds. -/

theorem run_of_halted (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool) :
    ∀ (n : Nat) (s : State α γ), s.halted = true → run prog ro mem0 orc n s = s
  | 0, _, _ => rfl
  | n + 1, s, h => by simp [run, h]

theorem fail_err_ne_none (s : State α γ) (msg : String) : (s.fail msg).err ≠ none := by
  cases hs : s.err with
  | none => simp [State.fail, hs]
  | some e => simp [State.fail, hs]

/-- Two runs from agreeing states agree, as long as the analysis `Ds` covers every executed
instruction (reads outside `Ds`, no flag writes, writes stay within the successors' `Ds`). -/
theorem run_agree (prog : Array Instr) (ro : Region) (mem0 : Addr γ → Cell α γ) (orc : Nat → Bool)
    (Ds : Nat → List Nat)
    (hsound : ∀ (pc : Nat) (i : Instr), prog[pc]? = some i →
      (∀ r, r ∈ readsOf i → r ∉ Ds pc) ∧
      (∀ d, d ∈ gprWritesOf i → d ≠ flg) ∧
      (∀ p' : Nat, p' ∈ successors pc i →
        ∀ r, r ∈ eraseAll (Ds pc) (writesOf i) → r ∈ Ds p')) :
    ∀ (n : Nat) (s1 s2 : State α γ), AgreeOn (Ds s1.pc) s1 s2 →
      (run prog ro mem0 orc n s1).err = none →
      AgreeOn (Ds (run prog ro mem0 orc n s1).pc) (run prog ro mem0 orc n s1)
        (run prog ro mem0 orc n s2)
  | 0, s1, s2, h, _ => h
  | n + 1, s1, s2, h, herrf => by
    simp only [run] at herrf ⊢
    by_cases hh : s1.halted = true
    · simp only [hh, ite_true] at herrf ⊢
      rw [if_pos (show s2.halted = true from by rw [← h.halted]; exact hh)]
      exact h
    · simp only [hh, Bool.false_eq_true, ite_false] at herrf ⊢
      rw [if_neg (show ¬ (s2.halted = true) from by rw [← h.halted]; exact hh)]
      cases hfetch : prog[s1.pc]? with
      | none =>
        simp only [hfetch] at herrf
        exact absurd herrf (fail_err_ne_none _ _)
      | some i =>
        rw [← h.pc]
        simp only [hfetch] at herrf ⊢
        obtain ⟨hread, hgpr, hsucc⟩ := hsound s1.pc i hfetch
        cases hstep : execE ro mem0 orc i s1 with
        | error e =>
          -- a failed step leaves a halted state whose error the run can never clear
          have hex : exec ro mem0 orc i s1 = s1.fail e := by
            rw [execE_eq]
            simp only [hh, Bool.false_eq_true, ite_false, hstep, okOr]
          rw [hex] at herrf
          rw [run_of_halted prog ro mem0 orc n (s1.fail e) (by unfold State.fail; split <;> rfl)] at herrf
          exact absurd herrf (fail_err_ne_none _ _)
        | ok s1' =>
          have hex : exec ro mem0 orc i s1 = s1' := by
            rw [execE_eq]
            simp only [hh, Bool.false_eq_true, ite_false, hstep, okOr]
          cases h2 : execE ro mem0 orc i s2 with
          | error e =>
            have hR := execE_agree (ro := ro) (mem0 := mem0) (orc := orc) h i hread hgpr
            rw [hstep, h2] at hR
            exact hR.elim
          | ok s2' =>
            have hR : AgreeOn (eraseAll (Ds s1.pc) (writesOf i)) s1' s2' := by
              have := execE_agree (ro := ro) (mem0 := mem0) (orc := orc) h i hread hgpr
              rw [hstep, h2] at this
              exact this
            have hex2 : exec ro mem0 orc i s2 = s2' := by
              rw [execE_eq]
              simp only [show ¬ (s2.halted = true) from by rw [← h.halted]; exact hh,
                Bool.false_eq_true, ite_false, h2, okOr]
            -- the written registers stay inside the analysis at the landed pc
            have hT : ∀ r, r ∈ eraseAll (Ds s1.pc) (writesOf i) → r ∈ Ds s1'.pc := by
              intro r hr
              rcases execE_ok_pc ro mem0 orc i s1 s1' hstep with hpc' | hpc'
              · rw [hpc']; exact mem_eraseAll _ _ hr
              · exact hsucc s1'.pc hpc' r hr
            rw [hex] at herrf ⊢
            rw [hex2] at ⊢
            exact run_agree prog ro mem0 orc Ds hsound n s1' s2' (hR.mono hT) herrf

end

end Hashtree.Asm.X86
