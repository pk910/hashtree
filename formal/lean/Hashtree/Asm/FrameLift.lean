import Hashtree.Asm.FrameTags
import Hashtree.Asm.MemCells
import Hashtree.Asm.RunExit

/-!
# R5: the frame-slot lift — the semantics of the tag certificate (`Asm/FrameTags`)

`TagRel` (the relation between two runs that differ only in the callee-saved registers and the
frame cells holding them) is preserved by one instruction of a certified stream.  The general
instructions go through the memory-conditioned agreement engine (`RunAgreeM.exec_agreeM` with
`M` = the cells outside the listed slots) plus `RunExit.exec_shape` (registers outside `dsts`
unchanged) and the cell lemmas of `Asm/MemCells` (listed slots survive disjoint writes); the four
copies (`push`, `pop`, `mov [rsp+k], r`, `mov r, [rsp+k]`) are done directly.

The two hypotheses of the lift beyond the certificate: `BaseRel B` (the aligned base of avx2_x8
sits 16..47 bytes below the entry rsp, as `and rsp, -32` at rsp - 16 gives) and, per step, that
every memory operand whose base is not rsp evaluates outside the `rStack` region (the kernels'
other pointers are rIn/rOut/rodata pointers: region disjointness, one `simp` at the instance).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Hashtree.Asm.FrameLift

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.BodyReads Hashtree.Asm.RspMap Hashtree.Asm.FrameTags
open Hashtree.Asm.RunAgreeM Hashtree.Asm.MemCells Hashtree.Asm.RunExit

abbrev CS := State W32 Int
abbrev M0 := Addr Int → Cell W32 Int

/-- The agreeing (unlisted) general registers. -/
def agreeing (T : Tags) : List Nat := (List.range 16).filter fun r => statusOf T (.reg r) = none

/-- The cells outside the listed slots. -/
def Outside (B : Nat → Int) (T : Tags) (a : Addr Int) : Prop := ¬ InTagged B T a

/-- The aligned base (base 1) sits 16..47 bytes below the entry rsp (base 0). -/
def BaseRel (B : Nat → Int) : Prop := B 0 - 47 ≤ B 1 ∧ B 1 ≤ B 0 - 16

section Rel
variable {mem0 : M0} {B : Nat → Int} {T : Tags} {s0 s0' s s' : CS}

theorem tagRel_agreeM (h : TagRel mem0 B T s0 s0' s s') :
    AgreeM (agreeing T) true (Outside B T) s s' where
  gpr r hr := h.reg r (by simp only [agreeing, List.mem_filter, decide_eq_true_eq] at hr; exact hr.2)
  len := h.len
  vr := h.vr
  flags := fun _ => h.flags
  mem := h.mem
  pc := h.pc
  halted := h.halted
  tail := h.tail
  err := h.err

end Rel

/-! ## The statuses after a general step -/

section Status

theorem statusOf_nil (i : Item) : statusOf [] i = none := rfl

theorem statusOf_cons (p : Item × Option Nat) (T : Tags) (i : Item) :
    statusOf (p :: T) i = if p.1 = i then some p.2 else statusOf T i := by
  by_cases h : p.1 = i
  · simp [statusOf, h]
  · simp [statusOf, h]

theorem statusOf_filter (T : Tags) (q : Item × Option Nat → Bool) (i : Item) (hq : ∀ st, q (i, st) = true) :
    statusOf (T.filter q) i = statusOf T i := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    obtain ⟨j, st⟩ := p
    by_cases hj : j = i
    · subst hj
      simp only [List.filter_cons, hq st, ite_true, statusOf_cons]
    · simp only [List.filter_cons]
      split
      · rw [statusOf_cons, statusOf_cons]; simp [hj, ih]
      · rw [statusOf_cons]; simp [hj, ih]

theorem statusOf_filter_none (T : Tags) (q : Item × Option Nat → Bool) (i : Item) (hq : ∀ st, q (i, st) = false) :
    statusOf (T.filter q) i = none := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    obtain ⟨j, st⟩ := p
    by_cases hj : j = i
    · subst hj
      simp only [List.filter_cons, hq st, Bool.false_eq_true, ite_false, ih]
    · simp only [List.filter_cons]
      split
      · rw [statusOf_cons]; simp [hj, ih]
      · exact ih

theorem statusOf_map (T : Tags) (g : Item × Option Nat → Item × Option Nat) (hg : ∀ p, (g p).1 = p.1) (i : Item) :
    statusOf (T.map g) i = (statusOf T i).map fun st => (g (i, st)).2 := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    obtain ⟨j, st⟩ := p
    simp only [List.map_cons, statusOf_cons, hg]
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, ih]

theorem statusOf_clearRegs_reg (T : Tags) (D : List Nat) (r : Nat) :
    statusOf (clearRegs T D) (.reg r) = if r ∈ D then none else statusOf T (.reg r) := by
  by_cases hr : r ∈ D
  · simp only [hr, ite_true]
    exact statusOf_filter_none T _ _ (fun st => by simp [hr])
  · simp only [hr, ite_false]
    exact statusOf_filter T _ _ (fun st => by simp [hr])

theorem statusOf_clearRegs_slot (T : Tags) (D : List Nat) (t : Slot) :
    statusOf (clearRegs T D) (.slot t) = statusOf T (.slot t) :=
  statusOf_filter T _ _ (fun st => rfl)

/-- After `clearOverlap?`: registers keep their status; a slot keeps its status unless the write
overlaps it, in which case it is free; listed-ness is unchanged. -/
theorem clearOverlap?_some {T T' : Tags} {s : Slot} (h : clearOverlap? T s = some T') :
    (∀ r, statusOf T' (.reg r) = statusOf T (.reg r)) ∧
    (∀ t, statusOf T' (.slot t) = if overlaps s t then (statusOf T (.slot t)).map (fun _ => none)
      else statusOf T (.slot t)) ∧
    (∀ p ∈ T, ∀ t, p.1 = .slot t → overlaps s t = true → covers s t = true) := by
  simp only [clearOverlap?] at h
  split at h
  · cases h
  · rename_i hany
    simp only [Option.some.injEq] at h
    subst h
    have hg : ∀ p : Item × Option Nat, (freeOv s p).1 = p.1 := by
      intro p
      obtain ⟨j, st⟩ := p
      cases j with
      | reg q => rfl
      | slot u => simp only [freeOv]; split <;> rfl
    refine ⟨?_, ?_, ?_⟩
    · intro r
      rw [statusOf_map T (freeOv s) hg]
      cases statusOf T (.reg r) <;> rfl
    · intro t
      rw [statusOf_map T (freeOv s) hg]
      cases statusOf T (.slot t) with
      | none => simp
      | some st => simp only [Option.map_some, freeOv]; split <;> rfl
    · intro p hp t hpt ho
      have hf : ¬ ((fun p : Item × Option Nat => match p.1 with | .slot t => overlaps s t && !covers s t | _ => false) p = true) := by
        intro hp'
        exact hany (List.any_eq_true.mpr ⟨p, hp, hp'⟩)
      obtain ⟨j, st⟩ := p
      simp only at hpt
      subst hpt
      cases hc : covers s t with
      | true => rfl
      | false => simp [ho, hc] at hf

end Status

/-! ## Slots and cells -/

theorem inSlot_region {B : Nat → Int} {sl : Slot} {a : Addr Int} (h : inSlot B sl a) : a.region = rStack := h.1

/-- A cell of a slot lies in its physical interval (relative to the entry rsp). -/
theorem inSlot_phys {B : Nat → Int} (hB : BaseRel B) {sl : Slot} {a : Addr Int} (h : inSlot B sl a)
    (hb : sl.1 = 0 ∨ sl.1 = 1) :
    (phys sl).1 ≤ a.off - B 0 ∧ a.off - B 0 < (phys sl).2 := by
  obtain ⟨_, h1, h2⟩ := h
  obtain ⟨hB1, hB2⟩ := hB
  rcases hb with hb | hb
  · rw [hb] at h1 h2; simp only [phys, hb, ite_true]; omega
  · rw [hb] at h1 h2; simp only [phys, hb, Nat.one_ne_zero, ite_false, ite_true]; omega

/-- Cells of non-overlapping slots are disjoint. -/
theorem not_overlaps_disjoint {B : Nat → Int} (hB : BaseRel B) {s t : Slot} (ho : overlaps s t = false)
    (hs : s.1 = 0 ∨ s.1 = 1) (ht : t.1 = 0 ∨ t.1 = 1) {a : Addr Int} (h1 : inSlot B s a) (h2 : inSlot B t a) : False := by
  simp only [overlaps] at ho
  split at ho
  · rename_i hst
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_lt] at ho
    obtain ⟨_, a1, a2⟩ := h1
    obtain ⟨_, b1, b2⟩ := h2
    rw [hst] at a1 a2
    omega
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_lt] at ho
    have p1 := inSlot_phys hB h1 hs
    have p2 := inSlot_phys hB h2 ht
    omega

/-- The physical cells of a slot `(base, off, size)` at the base values `B`. -/
theorem inSlot_iff (B : Nat → Int) (sl : Slot) (a : Addr Int) :
    inSlot B sl a ↔ Cells ⟨rStack, B sl.1 + sl.2.1⟩ sl.2.2 a := by
  simp only [inSlot, Cells]

/-- An rsp-based, unindexed operand evaluates to its slot's address. -/
theorem effAddr_rsp {B : Nat → Int} {f : Fact} {s : CS} (hr : RspOk B f s) (m : MemRef)
    (hb : m.base = some 4) (hi : m.index = none) (hro : m.ro = none) :
    effAddr 4 s m = .ok ⟨rStack, B f.sp.1 + f.sp.2 + m.disp⟩ := by
  unfold RspOk at hr
  simp only [effAddr, baseAddr, hro, hb, hi, regPtr, hr, Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id]

/-- `MLanes` from a cell condition. -/
theorem MLanes_of_cells (M : Addr Int → Prop) (a : Addr Int) (w : Nat) (h : ∀ x, Cells a (4 * w) x → M x) :
    MLanes M a w := by
  induction w generalizing a with
  | zero => trivial
  | succ w ih =>
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ih (a.plusI 4) ?_⟩
    · exact h a ⟨rfl, Int.le_refl _, by omega⟩
    · exact h _ ⟨rfl, by rw [plusI_int]; dsimp only; omega, by rw [plusI_int]; dsimp only; omega⟩
    · exact h _ ⟨rfl, by rw [plusI_int]; dsimp only; omega, by rw [plusI_int]; dsimp only; omega⟩
    · exact h _ ⟨rfl, by rw [plusI_int]; dsimp only; omega, by rw [plusI_int]; dsimp only; omega⟩
    · intro x hx
      obtain ⟨h1, h2, h3⟩ := hx
      rw [plusI_int] at h1 h2 h3
      dsimp only at h1 h2 h3
      exact h x ⟨h1, by omega, by omega⟩

theorem M4_of_cells (M : Addr Int → Prop) (a : Addr Int) (h : ∀ x, Cells a 4 x → M x) : M4 M a :=
  (MLanes_of_cells M a 1 (by simpa using h)).1

theorem M8_of_cells (M : Addr Int → Prop) (a : Addr Int) (h : ∀ x, Cells a 8 x → M x) : M8 M a := by
  refine ⟨h a ⟨rfl, Int.le_refl _, by omega⟩, ?_, ?_, ?_⟩
  · intro j hj1 hj2
    exact h _ ⟨rfl, by rw [plusI_int]; dsimp only; omega, by rw [plusI_int]; dsimp only; omega⟩
  · exact M4_of_cells M a (fun x hx => h x ⟨hx.1, hx.2.1, by have := hx.2.2; omega⟩)
  · refine M4_of_cells M _ (fun x hx => ?_)
    obtain ⟨h1, h2, h3⟩ := hx
    rw [plusI_int] at h1 h2 h3
    dsimp only at h1 h2 h3
    exact h x ⟨h1, by omega, by omega⟩

/-- Cells of a region other than `rStack` are outside every slot. -/
theorem outside_of_region {B : Nat → Int} {T : Tags} {a : Addr Int} (h : a.region ≠ rStack) : Outside B T a := by
  rintro ⟨sl, _, hin⟩
  exact h (inSlot_region hin)

theorem cells_region {a x : Addr Int} {n : Nat} (h : Cells a n x) : x.region = a.region := h.1

/-- The slots of a listed item are on base 0 or 1 when `slotsOk01` holds; we carry it as a
hypothesis on the table (`Bases01 T`). -/
def Bases01 (T : Tags) : Prop := ∀ sl, statusOf T (.slot sl) ≠ none → sl.1 = 0 ∨ sl.1 = 1

/-- A listed item is an entry of the table. -/
theorem listed_mem {T : Tags} {i : Item} (h : statusOf T i ≠ none) : ∃ p ∈ T, p.1 = i := by
  induction T with
  | nil => exact absurd rfl h
  | cons p T ih =>
    rw [statusOf_cons] at h
    split at h
    · exact ⟨p, List.mem_cons_self .., by assumption⟩
    · obtain ⟨q, hq, hqi⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hqi⟩

/-- A read slot that hits no listed slot has all its cells outside. -/
theorem outside_of_not_hits {B : Nat → Int} (hB : BaseRel B) {T : Tags} (h01 : Bases01 T) {sl : Slot}
    (hs : sl.1 = 0 ∨ sl.1 = 1) (hh : hitsTagged T sl = false) {x : Addr Int}
    (hx : Cells ⟨rStack, B sl.1 + sl.2.1⟩ sl.2.2 x) : Outside B T x := by
  rintro ⟨t, ht, hin⟩
  have ho : overlaps sl t = false := by
    obtain ⟨p, hp, hpt⟩ := listed_mem ht
    cases hc : overlaps sl t with
    | false => rfl
    | true =>
      exfalso
      have : hitsTagged T sl = true := by
        unfold hitsTagged
        exact List.any_eq_true.mpr ⟨p, hp, by rw [hpt]; exact hc⟩
      rw [this] at hh; cases hh
  exact not_overlaps_disjoint hB ho hs (h01 t ht) ((inSlot_iff B sl x).mpr hx) hin




/-! ## The general step -/

section General
variable {mem0 : M0} {B : Nat → Int} {s0 s0' s s' : CS} {f : Fact} {T T' : Tags} {i : Instr} {orc : Nat → Bool}

theorem succs_eq (p : Nat) (i : Instr) : RunAgreeM.succs p i = RunAgree.succs p i := by cases i <;> rfl

theorem tagStep_general (h : isCopy i = false) (f : Fact) (T : Tags) : tagStep f i T = generalStep f i T := by
  cases i with
  | push _ => simp [isCopy] at h
  | pop _ => simp [isCopy] at h
  | movst w m s => simp only [isCopy, beq_eq_false_iff_ne, ne_eq] at h; simp [tagStep, h]
  | mov w d src =>
    cases src with
    | mem m => simp only [isCopy, beq_eq_false_iff_ne, ne_eq] at h; simp [tagStep, h]
    | reg _ => rfl
    | imm _ => rfl
  | _ => rfl

theorem generalStep_some (h : generalStep f i T = some T') :
    regsUntagged T (srcs i) = true ∧ (readSlots f i).any (hitsTagged T) = false ∧
    (match writeSlot f i with
      | some sl => clearOverlap? (clearRegs T (dsts i)) sl = some T'
      | none => T' = clearRegs T (dsts i)) := by
  simp only [generalStep] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    refine ⟨hc.1, hc.2, ?_⟩
    split at h
    · rename_i sl hsl; simp only [hsl]; exact h
    · rename_i hsl; simp only [hsl, Option.some.injEq] at h ⊢; exact h.symm
  · cases h

/-- The register statuses after a general step. -/
theorem general_reg_status (hg : generalStep f i T = some T') (r : Nat) :
    statusOf T' (.reg r) = if r ∈ dsts i then none else statusOf T (.reg r) := by
  obtain ⟨_, _, hw⟩ := generalStep_some hg
  split at hw
  · rw [(clearOverlap?_some hw).1 r, statusOf_clearRegs_reg]
  · rw [hw, statusOf_clearRegs_reg]

/-- The slot statuses after a general step: unchanged, except that the written slot frees what it
overlaps (and every overlapped slot is covered). -/
theorem general_slot_status (hg : generalStep f i T = some T') (t : Slot) :
    (statusOf T' (.slot t) = none ↔ statusOf T (.slot t) = none) ∧
    (∀ n, statusOf T' (.slot t) = some (some n) → statusOf T (.slot t) = some (some n) ∧
      ∀ sl, writeSlot f i = some sl → overlaps sl t = false) := by
  obtain ⟨_, _, hw⟩ := generalStep_some hg
  split at hw
  · rename_i sl hsl
    have h2 := (clearOverlap?_some hw).2.1 t
    rw [statusOf_clearRegs_slot] at h2
    rw [h2]
    constructor
    · split <;> cases statusOf T (.slot t) <;> simp
    · intro n hn
      split at hn
      · cases statusOf T (.slot t) <;> simp at hn
      · rename_i ho
        refine ⟨hn, fun sl' hsl' => ?_⟩
        rw [hsl] at hsl'; cases hsl'; simpa using ho
  · rw [hw, statusOf_clearRegs_slot]
    exact ⟨Iff.rfl, fun n hn => ⟨hn, fun sl hsl => by rw [‹writeSlot f i = none›] at hsl; cases hsl⟩⟩

/-- Writes of the general instructions: only `vstore` and the 32-bit `movst` touch memory. -/
theorem writesMem_general (hc : isCopy i = false) (hv : ∀ w m src, i ≠ .vstore w m src)
    (hm : ∀ w m src, i ≠ .movst w m src) : writesMem i = false := by
  cases i with
  | vstore w m src => exact absurd rfl (hv w m src)
  | movst w m src => exact absurd rfl (hm w m src)
  | push _ => simp [isCopy] at hc
  | _ => rfl

/-- Either every written register is read (so it agrees after the step by the sources) or the
instruction is a straight-line one (its only static successor is `pc + 1`). -/
theorem dsts_or_next (i : Instr) : (∀ r ∈ dsts i, r ∈ srcs i) ∨ ∀ p, RunAgree.succs p i = [p + 1] := by
  cases i with
  | ret => left; intro r hr; simpa [dsts, srcs] using hr
  | jmp _ => left; intro r hr; simp [dsts] at hr
  | jcc _ _ => left; intro r hr; simp [dsts] at hr
  | jccTail _ _ => left; intro r hr; simp [dsts] at hr
  | jmpTail _ => left; intro r hr; simp [dsts] at hr
  | _ => right; intro p; rfl

/-- A non-halting instruction does not halt a non-halted state (success branch of `exec_shape`). -/
theorem halts_false_of (h : halts i = false) : mustHalt i = false := by cases i <;> simp_all [halts, mustHalt]

/-- The effective address of a memory operand agrees between related states (its registers are
sources). -/
theorem effAddr_rel {M : Addr Int → Prop} (h : AgreeM (srcs i) true M s s') (m : MemRef) (hm : ∀ r, r ∈ memRegs m → r ∈ srcs i) :
    effAddr 4 s' m = effAddr 4 s m := effAddr_ag h 4 hm

/-- `vstore` on a successful step. -/
theorem exec_vstore (w : Nat) (m : MemRef) (src : Nat) (hh : s.halted = false)
    (hok : (exec 4 mem0 orc (.vstore w m src) s).err = none) :
    ∃ a, effAddr 4 s m = .ok a ∧ exec 4 mem0 orc (.vstore w m src) s = (storeLanes s a ((s.getV src).take w)).next := by
  unfold exec at hok ⊢
  simp only [hh, Bool.false_eq_true, ite_false] at hok ⊢
  cases ha : effAddr 4 s m with
  | error e =>
    rw [ha] at hok
    exact absurd hok (fail_err s e)
  | ok a => exact ⟨a, rfl, rfl⟩

/-- 32-bit `movst` on a successful step. -/
theorem exec_movst32 (w : Nat) (m : MemRef) (src : Nat) (hw : w ≠ 64) (hh : s.halted = false)
    (hok : (exec 4 mem0 orc (.movst w m src) s).err = none) :
    ∃ a lo hi, effAddr 4 s m = .ok a ∧ s.getG src = .num lo hi ∧
      exec 4 mem0 orc (.movst w m src) s = (storeLane s a lo).next := by
  unfold exec at hok ⊢
  simp only [hh, Bool.false_eq_true, ite_false, hw] at hok ⊢
  cases ha : effAddr 4 s m with
  | error e =>
    rw [ha] at hok
    exact absurd hok (fail_err s e)
  | ok a =>
    rw [ha] at hok
    cases hg : s.getG src with
    | num lo hi => exact ⟨a, lo, hi, rfl, rfl, rfl⟩
    | ptr p =>
      rw [hg] at hok
      exact absurd hok (fail_err s _)

end General


/-! ## The memory reads of a general instruction are outside the listed slots -/

section Reads
variable {mem0 : M0} {B : Nat → Int} {s : CS} {f : Fact} {T : Tags} {i : Instr}

theorem hitsTagged_false_of {sl : Slot} (hnh : (readSlots f i).any (hitsTagged T) = false)
    (hsl : sl ∈ readSlots f i) : hitsTagged T sl = false := by
  cases hc : hitsTagged T sl with
  | false => rfl
  | true =>
    exfalso
    have : (readSlots f i).any (hitsTagged T) = true := List.any_eq_true.mpr ⟨sl, hsl, hc⟩
    rw [this] at hnh; cases hnh

/-- The cells a memory operand reads are outside the listed slots: rsp-based operands by the
certificate (`readSlots` misses every listed slot), the others by region disjointness. -/
theorem memOps_outside (hB : BaseRel B) (h01 : Bases01 T) (hR : RspOk B f s) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    (hnh : (readSlots f i).any (hitsTagged T) = false)
    (hrs : ∀ m ∈ memOps i, ∀ sl, slotOf f m.1 m.2 = some sl → sl ∈ readSlots f i)
    (hidx : ∀ m ∈ memOps i, m.1.base = some 4 → m.1.index = none ∧ m.1.ro = none)
    (hreg : ∀ m ∈ memOps i, m.1.base ≠ some 4 → ∀ a, effAddr 4 s m.1 = .ok a → a.region ≠ rStack) :
    ∀ m ∈ memOps i, ∀ a, effAddr 4 s m.1 = .ok a → ∀ x, Cells a m.2 x → Outside B T x := by
  intro m hm a ha x hx
  by_cases hb4 : m.1.base = some 4
  · obtain ⟨hi, hro⟩ := hidx m hm hb4
    rw [effAddr_rsp hR m.1 hb4 hi hro] at ha
    simp only [Except.ok.injEq] at ha
    subst ha
    have hsl : (f.sp.1, f.sp.2 + m.1.disp, m.2) ∈ readSlots f i :=
      hrs m hm _ (by simp [slotOf, hb4, hi, hro])
    have hh := hitsTagged_false_of hnh hsl
    refine outside_of_not_hits hB h01 hb hh (sl := (f.sp.1, f.sp.2 + m.1.disp, m.2)) ?_
    unfold Cells at hx ⊢
    dsimp only at hx ⊢
    obtain ⟨h1, h2, h3⟩ := hx
    exact ⟨h1, by omega, by omega⟩
  · exact outside_of_region (by rw [cells_region hx]; exact hreg m hm hb4 a ha)

theorem readsM_of_cert (hB : BaseRel B) (h01 : Bases01 T) (hR : RspOk B f s) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    (hcopy : isCopy i = false) (hnh : (readSlots f i).any (hitsTagged T) = false)
    (hidx : ∀ m ∈ memOps i, m.1.base = some 4 → m.1.index = none ∧ m.1.ro = none)
    (hreg : ∀ m ∈ memOps i, m.1.base ≠ some 4 → ∀ a, effAddr 4 s m.1 = .ok a → a.region ≠ rStack) :
    ReadsM 4 (Outside B T) s i := by
  have hout := memOps_outside hB h01 hR hb hnh (i := i)
  cases i <;> (try exact trivial)
  case vop op vex w d v1 v2 =>
    cases v2 with
    | reg _ => exact trivial
    | mem m =>
      intro a ha
      exact MLanes_of_cells _ a w (fun x hx => hout (fun m hm sl hsl => List.mem_filterMap.mpr ⟨m, hm, hsl⟩) hidx hreg (m, 4 * w)
        (by simp [memOps]) a ha x hx)
  case vload vex w d v =>
    cases v with
    | reg _ => exact trivial
    | mem m =>
      intro a ha
      exact MLanes_of_cells _ a w (fun x hx => hout (fun m hm sl hsl => List.mem_filterMap.mpr ⟨m, hm, hsl⟩) hidx hreg (m, 4 * w)
        (by simp [memOps]) a ha x hx)
  case inserti128 d v1 m imm =>
    intro a ha
    exact MLanes_of_cells _ a 4 (fun x hx => hout (fun m hm sl hsl => List.mem_filterMap.mpr ⟨m, hm, hsl⟩) hidx hreg (m, 16)
      (by simp [memOps]) a ha x hx)
  case inserti64x4 d v1 m imm =>
    intro a ha
    exact MLanes_of_cells _ a 8 (fun x hx => hout (fun m hm sl hsl => List.mem_filterMap.mpr ⟨m, hm, hsl⟩) hidx hreg (m, 32)
      (by simp [memOps]) a ha x hx)
  case mov w d src =>
    cases src with
    | reg _ => exact trivial
    | imm _ => exact trivial
    | mem m =>
      have hw : w ≠ 64 := by simpa [isCopy] using hcopy
      intro a ha
      refine ⟨fun h => absurd h hw, fun _ => ?_⟩
      refine M4_of_cells _ a (fun x hx => hout (fun m hm sl hsl => List.mem_filterMap.mpr ⟨m, hm, hsl⟩) hidx hreg (m, 4)
        (by simp [memOps, hw]) a ha x hx)
  case alu op w d src =>
    cases src with
    | reg _ => exact trivial
    | imm _ => exact trivial
    | mem m =>
      intro a ha
      exact M4_of_cells _ a (fun x hx => hout (fun m hm sl hsl => List.mem_filterMap.mpr ⟨m, hm, hsl⟩) hidx hreg (m, 4)
        (by simp [memOps]) a ha x hx)
  case pop _ => simp [isCopy] at hcopy
  case ret =>
    intro sp hsp
    unfold RspOk at hR
    change State.getG s 4 = Val.ptr sp at hsp
    rw [hR] at hsp
    simp only [Val.ptr.injEq] at hsp
    subst hsp
    have hh := hitsTagged_false_of hnh (sl := (f.sp.1, f.sp.2, 8)) (by simp [readSlots])
    exact M8_of_cells _ _ (fun x hx => outside_of_not_hits hB h01 hb hh hx)

end Reads


/-! ## The general step preserves the relation -/

/-- Every listed slot is an 8-byte cell. -/
def Sizes8 (T : Tags) : Prop := ∀ t, statusOf T (.slot t) ≠ none → t.2.2 = 8

section Main
variable {mem0 : M0} {B : Nat → Int} {s0 s0' s s' : CS} {f : Fact} {T T' : Tags} {i : Instr} {orc : Nat → Bool}

/-- `TagRel` as `AgreeM` on the instruction's sources (all agreeing by the certificate). -/
theorem agreeM_srcs (hrel : TagRel mem0 B T s0 s0' s s') (hu : regsUntagged T (srcs i) = true) :
    AgreeM (srcs i) true (Outside B T) s s' where
  gpr r hr := hrel.reg r (by
    simp only [regsUntagged, List.all_eq_true, decide_eq_true_eq] at hu
    exact hu r hr)
  len := hrel.len
  vr := hrel.vr
  flags := fun _ => hrel.flags
  mem := hrel.mem
  pc := hrel.pc
  halted := hrel.halted
  tail := hrel.tail
  err := hrel.err

/-- The registers of every memory operand are sources. -/
theorem memOps_regs_srcs (i : Instr) : ∀ m ∈ memOps i, ∀ r ∈ memRegs m.1, r ∈ srcs i := by
  intro m hm r hr
  cases i with
  | vop op vex w d s1 s2 =>
    cases s2 with
    | reg _ => simp [memOps] at hm
    | mem m' => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, vsrc, hr]
  | vload vex w d src =>
    cases src with
    | reg _ => simp [memOps] at hm
    | mem m' => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, vsrc, hr]
  | vstore w m' src => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, hr]
  | inserti128 d s1 m' imm => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, hr]
  | inserti64x4 d s1 m' imm => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, hr]
  | mov w d src =>
    cases src with
    | reg _ => simp [memOps] at hm
    | imm _ => simp [memOps] at hm
    | mem m' => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, gsrc, hr]
  | movst w m' src => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, hr]
  | alu op w d src =>
    cases src with
    | reg _ => simp [memOps] at hm
    | imm _ => simp [memOps] at hm
    | mem m' => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, gsrc, hr]
  | sub w d src =>
    cases src with
    | reg _ => simp [memOps] at hm
    | imm _ => simp [memOps] at hm
    | mem m' => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, gsrc, hr]
  | cmp w a b =>
    cases b with
    | reg _ => simp [memOps] at hm
    | imm _ => simp [memOps] at hm
    | mem m' => simp only [memOps, List.mem_singleton] at hm; subst hm; simp [srcs, gsrc, hr]
  | _ => simp [memOps] at hm

/-- Either every written register is read, or the instruction is straight-line and never halts. -/
theorem dsts_or_next' (i : Instr) :
    (∀ r ∈ dsts i, r ∈ srcs i) ∨ ((∀ p, RunAgree.succs p i = [p + 1]) ∧ halts i = false) := by
  cases i with
  | ret => left; intro r hr; simpa [dsts, srcs] using hr
  | jmp _ => left; intro r hr; simp [dsts] at hr
  | jcc _ _ => left; intro r hr; simp [dsts] at hr
  | jccTail _ _ => left; intro r hr; simp [dsts] at hr
  | jmpTail _ => left; intro r hr; simp [dsts] at hr
  | _ => right; exact ⟨fun p => rfl, rfl⟩

/-- The cells of a slot listed after a general step are untouched by the step's write
(stated for any state `u` related to the certificate's facts). -/
theorem slot_untouched (hB : BaseRel B) (h01 : Bases01 T) (h8 : Sizes8 T) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    {u : CS} (hR : RspOk B f u) (hh : u.halted = false) (hcopy : isCopy i = false)
    (hg : generalStep f i T = some T')
    (hidx : ∀ m ∈ memOps i, m.1.base = some 4 → m.1.index = none ∧ m.1.ro = none)
    (hreg : ∀ m ∈ memOps i, m.1.base ≠ some 4 → ∀ a, effAddr 4 u m.1 = .ok a → a.region ≠ rStack)
    (hok : (exec 4 mem0 orc i u).err = none) {t : Slot} {n : Nat} (ht : statusOf T' (.slot t) = some (some n)) :
    ∀ x, Cells ⟨rStack, B t.1 + t.2.1⟩ 8 x → lookup x (exec 4 mem0 orc i u).mem = lookup x u.mem := by
  obtain ⟨htT, hov⟩ := (general_slot_status hg t).2 n ht
  have ht8 : t.2.2 = 8 := h8 t (by rw [htT]; simp)
  have htb : t.1 = 0 ∨ t.1 = 1 := h01 t (by rw [htT]; simp)
  intro x hx
  have hxt : inSlot B t x := (inSlot_iff B t x).mpr (by rw [ht8]; exact hx)
  -- a written cell range at `a` (size `sz`, as the certificate records it) is disjoint from `x`
  have disj : ∀ (m : MemRef) (sz : Nat), (m, sz) ∈ memOps i → writeSlot f i = slotOf f m sz →
      ∀ a, effAddr 4 u m = .ok a → ¬ Cells a sz x := by
    intro m sz hm hws a ha hc
    by_cases hb4 : m.base = some 4
    · obtain ⟨hi, hro⟩ := hidx (m, sz) hm hb4
      simp only at hi hro
      rw [effAddr_rsp hR m hb4 hi hro] at ha
      simp only [Except.ok.injEq] at ha
      subst ha
      have hsl : writeSlot f i = some (f.sp.1, f.sp.2 + m.disp, sz) := by rw [hws]; simp [slotOf, hb4, hi, hro]
      have ho := hov _ hsl
      refine not_overlaps_disjoint hB ho hb htb ?_ hxt
      rw [inSlot_iff]
      unfold Cells at hc ⊢
      dsimp only at hc ⊢
      obtain ⟨h1, h2, h3⟩ := hc
      exact ⟨h1, by omega, by omega⟩
    · have := hreg (m, sz) hm hb4 a ha
      exact this (by rw [← cells_region hc]; exact hxt.1)
  cases i with
  | vstore w m src =>
    obtain ⟨a, ha, he⟩ := exec_vstore w m src hh hok
    rw [he]
    show lookup x (storeLanes u a ((u.getV src).take w)).mem = lookup x u.mem
    apply lookup_storeLanes_untouched
    intro hc
    refine disj m (4 * w) (by simp [memOps]) rfl a ha ?_
    obtain ⟨h1, h2, h3⟩ := hc
    refine ⟨h1, h2, ?_⟩
    have hl : ((u.getV src).take w).length ≤ w := List.length_take_le _ _
    have : (4 * ((u.getV src).take w).length : Int) ≤ 4 * w := by omega
    omega
  | movst w m src =>
    have hw : w ≠ 64 := by simpa [isCopy] using hcopy
    obtain ⟨a, lo, hi, ha, _, he⟩ := exec_movst32 w m src hw hh hok
    rw [he]
    show lookup x (storeLane u a lo).mem = lookup x u.mem
    apply lookup_storeLane_untouched
    exact disj m 4 (by simp [memOps, hw]) (by simp [writeSlot, hw]) a ha
  | _ =>
    rcases exec_shape 4 mem0 orc _ u hh with ⟨hne, _⟩ | ⟨_, _, _, hmem, _, _, _⟩
    · exact absurd hok hne
    · rw [hmem (writesMem_general hcopy (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h))]


/-- **The general step preserves the relation.** -/
theorem general_step (hB : BaseRel B) (h01 : Bases01 T) (h8 : Sizes8 T) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    (hrsp : statusOf T (.reg 4) = none)
    (hrel : TagRel mem0 B T s0 s0' s s') (hR : RspOk B f s) (hh : s.halted = false)
    (hcopy : isCopy i = false) (hstep : tagStep f i T = some T')
    (hidx : ∀ m ∈ memOps i, m.1.base = some 4 → m.1.index = none ∧ m.1.ro = none)
    (hreg : ∀ m ∈ memOps i, m.1.base ≠ some 4 → ∀ a, effAddr 4 s m.1 = .ok a → a.region ≠ rStack)
    (hok : (exec 4 mem0 orc i s).err = none) :
    TagRel mem0 B T' s0 s0' (exec 4 mem0 orc i s) (exec 4 mem0 orc i s') ∧
    ((exec 4 mem0 orc i s).pc ∈ RunAgree.succs s.pc i ∨ (exec 4 mem0 orc i s).halted = true) := by
  have hg : generalStep f i T = some T' := by rwa [tagStep_general hcopy] at hstep
  obtain ⟨hu, hnh, _⟩ := generalStep_some hg
  have hA := agreeM_srcs hrel hu
  have hr := readsM_of_cert hB h01 hR hb hcopy hnh hidx hreg
  obtain ⟨hA1, hA2⟩ := exec_agreeM 4 mem0 orc i hA (fun _ h => h) (fun _ => rfl) hr
  have hh' : s'.halted = false := by rw [← hrel.halted]; exact hh
  rcases exec_shape 4 mem0 orc i s hh with ⟨hne, _⟩ | ⟨_, hhalt, hgpr, _, _, _, hpc⟩
  · exact absurd hok hne
  have hok' : (exec 4 mem0 orc i s').err = none := by rw [← hA1.err]; exact hok
  rcases exec_shape 4 mem0 orc i s' hh' with ⟨hne', _⟩ | ⟨_, _, hgpr', _, _, _, _⟩
  · exact absurd hok' hne'
  -- the second run: rsp and the non-rsp operand addresses agree with the first
  have hR' : RspOk B f s' := by unfold RspOk at hR ⊢; rw [← hrel.reg 4 hrsp]; exact hR
  have hreg' : ∀ m ∈ memOps i, m.1.base ≠ some 4 → ∀ a, effAddr 4 s' m.1 = .ok a → a.region ≠ rStack := by
    intro m hm hb4 a ha
    rw [effAddr_rel hA m.1 (memOps_regs_srcs i m hm)] at ha
    exact hreg m hm hb4 a ha
  -- the written registers agree when the pc moved
  have hdsts : ∀ r ∈ dsts i, (exec 4 mem0 orc i s).getG r = (exec 4 mem0 orc i s').getG r := by
    intro r hrd
    rcases dsts_or_next' i with hsub | ⟨hnext, hhalts⟩
    · exact hA1.gpr r (hsub r hrd)
    · have hpc' : (exec 4 mem0 orc i s).pc = s.pc + 1 := by
        rcases hpc with hp | hp
        · rw [hnext] at hp; simpa using hp
        · rcases hhalt with hq | hq
          · rw [hp] at hq; rw [hh] at hq; cases hq
          · rw [hhalts] at hq; cases hq
      rcases hA2 with hA2 | ⟨_, hA3⟩
      · rw [hA2] at hpc'; omega
      · exact hA3.gpr r (List.mem_append_left _ hrd)
  refine ⟨⟨?_, ?_, ?_, ?_, hA1.len, hA1.vr, hA1.flags rfl, hA1.pc, hA1.halted, hA1.tail, hA1.err⟩, hpc⟩
  · intro r hr0
    rw [general_reg_status hg] at hr0
    split at hr0
    · exact hdsts r ‹_›
    · rename_i hnd; rw [hgpr r hnd, hgpr' r hnd]; exact hrel.reg r hr0
  · intro r n hr0
    rw [general_reg_status hg] at hr0
    split at hr0
    · cases hr0
    · rename_i hnd; rw [hgpr r hnd, hgpr' r hnd]; exact hrel.tagReg r n hr0
  · intro t n ht
    obtain ⟨htT, _⟩ := (general_slot_status hg t).2 n ht
    obtain ⟨hv1, hv2⟩ := hrel.tagSlot t n htT
    have hu1 := slot_untouched hB h01 h8 hb hR hh hcopy hg hidx hreg hok ht (mem0 := mem0) (orc := orc)
    have hu2 := slot_untouched hB h01 h8 hb hR' hh' hcopy hg hidx hreg' hok' ht (mem0 := mem0) (orc := orc)
    constructor
    · rw [← hv1]
      unfold slotVal
      exact (loadVal_memAg (M := Cells ⟨rStack, B t.1 + t.2.1⟩ 8) (fun x hx => hu1 x hx) mem0 rfl rfl _
        (M8_of_cells _ _ (fun x hx => hx))).symm
    · rw [← hv2]
      unfold slotVal
      exact (loadVal_memAg (M := Cells ⟨rStack, B t.1 + t.2.1⟩ 8) (fun x hx => hu2 x hx) mem0 rfl rfl _
        (M8_of_cells _ _ (fun x hx => hx))).symm
  · intro a ha
    apply hA1.mem
    rintro ⟨t, ht, hin⟩
    exact ha ⟨t, fun h => ht ((general_slot_status hg t).1.mp h), hin⟩

end Main

end Hashtree.Asm.FrameLift
