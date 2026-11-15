import Hashtree.Asm.FrameTags
import Hashtree.Asm.MemCells
import Hashtree.Asm.RunExit
import Hashtree.Proofs.Win64

/-!
# R5: the frame-slot lift — the semantics of the tag certificate (`Asm/FrameTags`)

(In the Proofs layer for `Win64.exec_gpr_len`: the register file keeps its length 16.)

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

namespace Hashtree.Proofs.FrameLift

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

theorem statusOf_clearItem_self (T : Tags) (i : Item) : statusOf (clearItem T i) i = none :=
  statusOf_filter_none T _ _ (fun st => by simp)

theorem statusOf_clearItem_ne (T : Tags) {i j : Item} (h : j ≠ i) : statusOf (clearItem T i) j = statusOf T j :=
  statusOf_filter T _ _ (fun st => by simp [h])

theorem statusOf_setStatus_self (T : Tags) (i : Item) (st : Option (Option Nat)) :
    statusOf (setStatus T i st) i = st := by
  cases st with
  | none => exact statusOf_clearItem_self T i
  | some st => simp [setStatus, statusOf_cons]

theorem statusOf_setStatus_ne (T : Tags) {i j : Item} (h : j ≠ i) (st : Option (Option Nat)) :
    statusOf (setStatus T i st) j = statusOf T j := by
  cases st with
  | none => exact statusOf_clearItem_ne T h
  | some st => simp [setStatus, statusOf_cons, Ne.symm h, statusOf_clearItem_ne T h]

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
  simp only [effAddr, baseAddr, hro, hb, hi, regPtr, hr.1, Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id]

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
    change State.getG s 4 = Val.ptr sp at hsp
    rw [hR.1] at hsp
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
    (hrsp : statusOf T (.reg 4) = none) (hsav : f.saved ≠ none → statusOf T (.reg 5) = none)
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
  have hR' : RspOk B f s' := by
    refine ⟨?_, ?_⟩
    · rw [← hrel.reg 4 hrsp]; exact hR.1
    · intro v hv; rw [← hrel.reg 5 (hsav (by rw [hv]; simp))]; exact hR.2 v hv
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
  refine ⟨⟨?_, ?_, ?_, ?_, hA1.len, by rw [exec_gpr_len]; exact hrel.len16, hA1.vr, hA1.flags rfl, hA1.pc, hA1.halted, hA1.tail, hA1.err⟩, hpc⟩
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


/-! ## The copies -/

section Copies
variable {mem0 : M0} {B : Nat → Int} {s0 s0' s s' : CS} {f : Fact} {T T' : Tags} {orc : Nat → Bool}

theorem loadVal_mem_eq (mem0 : M0) {u u' : CS} (h : u.mem = u'.mem) (a : Addr Int) :
    loadVal mem0 u a = loadVal mem0 u' a :=
  (loadVal_memAg (M := fun _ => True) (fun x _ => by rw [h]) mem0 rfl rfl a
    ⟨trivial, fun _ _ _ => trivial, ⟨trivial, trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial, trivial⟩⟩).symm

/-- A slot listed in `T` (other than the written one) keeps its 8-byte value across a store to
the slot `sl` that does not overlap it. -/
theorem slotVal_store (hB : BaseRel B) (h01 : Bases01 T) (h8 : Sizes8 T) {sl t : Slot}
    (hsb : sl.1 = 0 ∨ sl.1 = 1) (hs8 : sl.2.2 = 8) (ht : statusOf T (.slot t) ≠ none) (ho : overlaps sl t = false)
    (u : CS) (v : Val W32 Int) :
    slotVal mem0 B (storeVal u ⟨rStack, B sl.1 + sl.2.1⟩ v) t = slotVal mem0 B u t := by
  have ht8 := h8 t ht
  have htb := h01 t ht
  unfold slotVal
  refine (loadVal_memAg (M := Cells ⟨rStack, B t.1 + t.2.1⟩ 8) (fun x hx => ?_) mem0 rfl rfl _
    (M8_of_cells _ _ (fun x hx => hx))).symm
  apply lookup_storeVal_untouched
  intro hc
  refine not_overlaps_disjoint hB ho hsb htb ?_ ((inSlot_iff B t x).mpr (by rw [ht8]; exact hx))
  rw [inSlot_iff, hs8]; exact hc

/-- The relation after storing register `r` into the slot `sl` at its address: the common shape
of `push` and `mov [rsp+k], r`.  `u`, `u'` are the states after the store (with the same other
fields as the related `s`, `s'` except possibly rsp). -/
theorem store_rel (hB : BaseRel B) (h01 : Bases01 T) (h8 : Sizes8 T) {T1 : Tags} {sl : Slot}
    (hsb : sl.1 = 0 ∨ sl.1 = 1) (hs8 : sl.2.2 = 8)
    (hrel : TagRel mem0 B T s0 s0' s s') (r : Nat)
    (hco : clearOverlap? T sl = some T1) (hT' : T' = setStatus T1 (.slot sl) (statusOf T (.reg r)))
    {u u' : CS} (hum : u.mem = (storeVal s ⟨rStack, B sl.1 + sl.2.1⟩ (s.getG r)).mem)
    (hum' : u'.mem = (storeVal s' ⟨rStack, B sl.1 + sl.2.1⟩ (s'.getG r)).mem)
    (hug : ∀ q, statusOf T (.reg q) ≠ none → u.getG q = s.getG q ∧ u'.getG q = s'.getG q)
    (hug0 : ∀ q, statusOf T (.reg q) = none → u.getG q = u'.getG q)
    (hlen : u.gpr.length = u'.gpr.length) (hlen16 : u.gpr.length = 16) (hvr : u.vr = u'.vr) (hfl : u.flags = u'.flags)
    (hpc : u.pc = u'.pc) (hh : u.halted = u'.halted) (htl : u.tail = u'.tail) (he : u.err = u'.err) :
    TagRel mem0 B T' s0 s0' u u' := by
  obtain ⟨hc1, hc2, _⟩ := clearOverlap?_some hco
  subst hT'
  refine ⟨?_, ?_, ?_, ?_, hlen, hlen16, hvr, hfl, hpc, hh, htl, he⟩
  · intro q hq
    rw [statusOf_setStatus_ne _ (by simp), hc1] at hq
    exact hug0 q hq
  · intro q n hq
    rw [statusOf_setStatus_ne _ (by simp), hc1] at hq
    obtain ⟨e1, e2⟩ := hug q (by rw [hq]; simp)
    rw [e1, e2]
    exact hrel.tagReg q n hq
  · intro t n ht
    by_cases hts : t = sl
    · subst hts
      rw [statusOf_setStatus_self] at ht
      obtain ⟨e1, e2⟩ := hrel.tagReg r n ht
      unfold slotVal
      rw [loadVal_mem_eq mem0 hum, loadVal_mem_eq mem0 hum', loadVal_storeVal, loadVal_storeVal, e1, e2]
      exact ⟨rfl, rfl⟩
    · rw [statusOf_setStatus_ne _ (by simpa using hts), hc2 t] at ht
      split at ht
      · cases statusOf T (.slot t) <;> simp at ht
      · rename_i ho
        obtain ⟨e1, e2⟩ := hrel.tagSlot t n ht
        have ho' : overlaps sl t = false := by simpa using ho
        have hl : statusOf T (.slot t) ≠ none := by rw [ht]; simp
        unfold slotVal at e1 e2 ⊢
        rw [loadVal_mem_eq mem0 hum, loadVal_mem_eq mem0 hum']
        have k1 := slotVal_store hB h01 h8 hsb hs8 hl ho' s (s.getG r) (mem0 := mem0)
        have k2 := slotVal_store hB h01 h8 hsb hs8 hl ho' s' (s'.getG r) (mem0 := mem0)
        unfold slotVal at k1 k2
        rw [k1, k2]
        exact ⟨e1, e2⟩
  · intro a ha
    rw [hum, hum']
    by_cases hin : Cells ⟨rStack, B sl.1 + sl.2.1⟩ 8 a
    · -- inside the written slot: it is unlisted after the store, so `r` was agreeing
      have hr0 : statusOf T (.reg r) = none := by
        cases hst : statusOf T (.reg r) with
        | none => rfl
        | some st =>
          exfalso
          apply ha
          refine ⟨sl, ?_, (inSlot_iff B sl a).mpr (by rw [hs8]; exact hin)⟩
          rw [statusOf_setStatus_self, hst]; simp
      rw [hrel.reg r hr0]
      exact lookup_storeVal_inside _ _ _ _ _ hin
    · rw [lookup_storeVal_untouched s _ _ a hin, lookup_storeVal_untouched s' _ _ a hin]
      apply hrel.mem
      rintro ⟨t, ht, hta⟩
      apply ha
      refine ⟨t, ?_, hta⟩
      by_cases hts : t = sl
      · subst hts
        exact absurd ((inSlot_iff B t a).mp hta) (by rw [hs8]; exact hin)
      · rw [statusOf_setStatus_ne _ (by simpa using hts), hc2 t]
        split
        · cases hst : statusOf T (.slot t) with
          | none => exact absurd hst ht
          | some st => simp
        · exact ht


/-! ### Exec forms of the copies -/

theorem exec_push (r : Nat) (hh : s.halted = false) {sp : Addr Int} (hsp : s.getG rsp = .ptr sp) :
    exec 4 mem0 orc (.push r) s = ((storeVal s (sp.plusI (-8)) (s.getG r)).setG rsp (.ptr (sp.plusI (-8)))).next := by
  unfold exec
  simp only [hh, Bool.false_eq_true, ite_false]
  rw [hsp]
  rfl

theorem exec_pop (r : Nat) (hh : s.halted = false) {sp : Addr Int} (hsp : s.getG rsp = .ptr sp)
    {v : Val W32 Int} (hv : loadVal mem0 s sp = .ok v) :
    exec 4 mem0 orc (.pop r) s = ((s.setG r v).setG rsp (.ptr (sp.plusI 8))).next := by
  unfold exec
  simp only [hh, Bool.false_eq_true, ite_false]
  rw [hsp]
  simp only [hv, bind, Except.bind]
  rfl

theorem exec_pop_err (r : Nat) (hh : s.halted = false) {sp : Addr Int} (hsp : s.getG rsp = .ptr sp)
    (hok : (exec 4 mem0 orc (.pop r) s).err = none) : ∃ v, loadVal mem0 s sp = .ok v := by
  unfold exec at hok
  simp only [hh, Bool.false_eq_true, ite_false] at hok
  rw [hsp] at hok
  cases hv : loadVal mem0 s sp with
  | error e =>
    simp only [hv, bind, Except.bind] at hok
    exact absurd hok (fail_err s e)
  | ok v => exact ⟨v, rfl⟩

theorem exec_movst64 (m : MemRef) (src : Nat) (hh : s.halted = false) {a : Addr Int} (ha : effAddr 4 s m = .ok a) :
    exec 4 mem0 orc (.movst 64 m src) s = (storeVal s a (s.getG src)).next := by
  unfold exec
  simp only [hh, Bool.false_eq_true, ite_false, ha, bind, Except.bind, ite_true]
  rfl

theorem exec_movst64_err (m : MemRef) (src : Nat) (hh : s.halted = false)
    (hok : (exec 4 mem0 orc (.movst 64 m src) s).err = none) : ∃ a, effAddr 4 s m = .ok a := by
  unfold exec at hok
  simp only [hh, Bool.false_eq_true, ite_false] at hok
  cases ha : effAddr 4 s m with
  | error e => rw [ha] at hok; exact absurd hok (fail_err s e)
  | ok a => exact ⟨a, rfl⟩

theorem exec_mov64mem (d : Nat) (m : MemRef) (hh : s.halted = false) {a : Addr Int} (ha : effAddr 4 s m = .ok a)
    {v : Val W32 Int} (hv : loadVal mem0 s a = .ok v) :
    exec 4 mem0 orc (.mov 64 d (.mem m)) s = (s.setG d v).next := by
  unfold exec
  simp only [hh, Bool.false_eq_true, ite_false, ha, hv, bind, Except.bind, ite_true]
  rfl

theorem exec_mov64mem_err (d : Nat) (m : MemRef) (hh : s.halted = false)
    (hok : (exec 4 mem0 orc (.mov 64 d (.mem m)) s).err = none) :
    ∃ a v, effAddr 4 s m = .ok a ∧ loadVal mem0 s a = .ok v := by
  unfold exec at hok
  simp only [hh, Bool.false_eq_true, ite_false, ite_true] at hok
  cases ha : effAddr 4 s m with
  | error e => rw [ha] at hok; exact absurd hok (fail_err s e)
  | ok a =>
    rw [ha] at hok
    cases hv : loadVal mem0 s a with
    | error e => simp only [hv, bind, Except.bind] at hok; exact absurd hok (fail_err s e)
    | ok v => exact ⟨a, v, rfl, hv⟩

/-- The relation after loading the slot `sl` into register `d` (the common shape of `pop` and
`mov r, [rsp+k]`). -/
theorem load_rel (hrel : TagRel mem0 B T s0 s0' s s') {sl : Slot} (d : Nat) {v v' : Val W32 Int}
    (hst : statusOf T (.slot sl) ≠ some none)
    (hv : loadVal mem0 s ⟨rStack, B sl.1 + sl.2.1⟩ = .ok v) (hv' : loadVal mem0 s' ⟨rStack, B sl.1 + sl.2.1⟩ = .ok v')
    (hvv : statusOf T (.slot sl) = none → v = v')
    (hT' : T' = setStatus T (.reg d) (statusOf T (.slot sl)))
    {u u' : CS} (hum : u.mem = s.mem) (hum' : u'.mem = s'.mem)
    (hud : u.getG d = v) (hud' : u'.getG d = v')
    (hug : ∀ q, q ≠ d → statusOf T (.reg q) ≠ none → u.getG q = s.getG q ∧ u'.getG q = s'.getG q)
    (hug0 : ∀ q, q ≠ d → statusOf T (.reg q) = none → u.getG q = u'.getG q)
    (hlen : u.gpr.length = u'.gpr.length) (hlen16 : u.gpr.length = 16) (hvr : u.vr = u'.vr) (hfl : u.flags = u'.flags)
    (hpc : u.pc = u'.pc) (hh : u.halted = u'.halted) (htl : u.tail = u'.tail) (he : u.err = u'.err) :
    TagRel mem0 B T' s0 s0' u u' := by
  subst hT'
  refine ⟨?_, ?_, ?_, ?_, hlen, hlen16, hvr, hfl, hpc, hh, htl, he⟩
  · intro q hq
    by_cases hqd : q = d
    · subst hqd
      rw [statusOf_setStatus_self] at hq
      rw [hud, hud']; exact hvv hq
    · rw [statusOf_setStatus_ne _ (by simpa using hqd)] at hq
      exact hug0 q hqd hq
  · intro q n hq
    by_cases hqd : q = d
    · subst hqd
      rw [statusOf_setStatus_self] at hq
      obtain ⟨e1, e2⟩ := hrel.tagSlot sl n hq
      unfold slotVal at e1 e2
      rw [hv] at e1; rw [hv'] at e2
      simp only [Except.ok.injEq] at e1 e2
      rw [hud, hud', e1, e2]; exact ⟨rfl, rfl⟩
    · rw [statusOf_setStatus_ne _ (by simpa using hqd)] at hq
      obtain ⟨e1, e2⟩ := hug q hqd (by rw [hq]; simp)
      rw [e1, e2]; exact hrel.tagReg q n hq
  · intro t n ht
    rw [statusOf_setStatus_ne _ (by simp)] at ht
    obtain ⟨e1, e2⟩ := hrel.tagSlot t n ht
    unfold slotVal at e1 e2 ⊢
    rw [loadVal_mem_eq mem0 hum, loadVal_mem_eq mem0 hum']
    exact ⟨e1, e2⟩
  · intro a ha
    rw [hum, hum']
    apply hrel.mem
    rintro ⟨t, ht, hta⟩
    exact ha ⟨t, by rw [statusOf_setStatus_ne _ (by simp)]; exact ht, hta⟩

/-- Registers of the two related states after the same `setG`s: a helper giving the agreement of
the written register without knowing the register file length. -/
theorem setG_agree (hrel : TagRel mem0 B T s0 s0' s s') {u u' : CS}
    (hlen : u.gpr.length = u'.gpr.length) (hvr : u.vr = u'.vr) (hfl : u.flags = u'.flags) (hpc : u.pc = u'.pc)
    (hh : u.halted = u'.halted) (htl : u.tail = u'.tail) (he : u.err = u'.err) (d : Nat) (v : Val W32 Int) :
    (u.setG d v).getG d = (u'.setG d v).getG d ∧ (u.setG d v).gpr.length = (u'.setG d v).gpr.length := by
  have hA : AgreeM [] true (fun _ => False) u u' :=
    ⟨fun _ h => by simp at h, hlen, hvr, fun _ => hfl, fun _ h => h.elim, hpc, hh, htl, he⟩
  have := setG_ag hA d v
  exact ⟨this.gpr d (by simp), this.len⟩


/-! ### The four copies -/

theorem getG_setG_self' (u : CS) (i : Nat) (v : Val W32 Int) (h : i < u.gpr.length) : (u.setG i v).getG i = v := by
  simp [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set_self h]

theorem getG_setG_ne' (u : CS) (i j : Nat) (v : Val W32 Int) (h : i ≠ j) : (u.setG j v).getG i = u.getG i := by
  simp [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem storeVal_gpr (u : CS) (a : Addr Int) (v : Val W32 Int) : (storeVal u a v).gpr = u.gpr := by cases v <;> rfl
theorem storeVal_vr (u : CS) (a : Addr Int) (v : Val W32 Int) : (storeVal u a v).vr = u.vr := by cases v <;> rfl
theorem storeVal_flags (u : CS) (a : Addr Int) (v : Val W32 Int) : (storeVal u a v).flags = u.flags := by cases v <;> rfl
theorem storeVal_pc (u : CS) (a : Addr Int) (v : Val W32 Int) : (storeVal u a v).pc = u.pc := by cases v <;> rfl
theorem storeVal_halted (u : CS) (a : Addr Int) (v : Val W32 Int) : (storeVal u a v).halted = u.halted := by cases v <;> rfl
theorem storeVal_tail (u : CS) (a : Addr Int) (v : Val W32 Int) : (storeVal u a v).tail = u.tail := by cases v <;> rfl
theorem storeVal_err (u : CS) (a : Addr Int) (v : Val W32 Int) : (storeVal u a v).err = u.err := by cases v <;> rfl

theorem rsp_eq (hrel : TagRel mem0 B T s0 s0' s s') (hrsp : statusOf T (.reg 4) = none) (hR : RspOk B f s) :
    s.getG rsp = .ptr ⟨rStack, B f.sp.1 + f.sp.2⟩ ∧ s'.getG rsp = .ptr ⟨rStack, B f.sp.1 + f.sp.2⟩ :=
  ⟨hR.1, by change s'.getG 4 = _; rw [← hrel.reg 4 hrsp]; exact hR.1⟩

/-- `push r`. -/
theorem push_step (hB : BaseRel B) (h01 : Bases01 T) (h8 : Sizes8 T) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    (hrel : TagRel mem0 B T s0 s0' s s') (hR : RspOk B f s) (hh : s.halted = false) (r : Nat)
    (hstep : tagStep f (.push r) T = some T') :
    TagRel mem0 B T' s0 s0' (exec 4 mem0 orc (.push r) s) (exec 4 mem0 orc (.push r) s') ∧
    (exec 4 mem0 orc (.push r) s).pc = s.pc + 1 := by
  simp only [tagStep] at hstep
  split at hstep
  · cases hstep
  rename_i hrsp0
  have hrsp : statusOf T (.reg 4) = none := by simpa using hrsp0
  obtain ⟨T1, hco, hT'⟩ := Option.map_eq_some_iff.mp hstep
  obtain ⟨hsp, hsp'⟩ := rsp_eq hrel hrsp hR
  have hh' : s'.halted = false := by rw [← hrel.halted]; exact hh
  have haddr : (⟨rStack, B f.sp.1 + f.sp.2⟩ : Addr Int).plusI (-8) = ⟨rStack, B f.sp.1 + (f.sp.2 - 8)⟩ := by
    rw [plusI_int]
    show Addr.mk rStack (B f.sp.1 + f.sp.2 + (-8)) = Addr.mk rStack (B f.sp.1 + (f.sp.2 - 8))
    congr 1; omega
  rw [exec_push r hh hsp, exec_push r hh' hsp', haddr]
  have hq4 : ∀ q, statusOf T (.reg q) ≠ none → q ≠ 4 := fun q hq h => hq (h ▸ hrsp)
  have hag := setG_agree hrel (u := storeVal s ⟨rStack, B f.sp.1 + (f.sp.2 - 8)⟩ (s.getG r))
    (u' := storeVal s' ⟨rStack, B f.sp.1 + (f.sp.2 - 8)⟩ (s'.getG r))
    (by rw [storeVal_gpr, storeVal_gpr]; exact hrel.len) (by rw [storeVal_vr, storeVal_vr]; exact hrel.vr)
    (by rw [storeVal_flags, storeVal_flags]; exact hrel.flags) (by rw [storeVal_pc, storeVal_pc]; exact hrel.pc)
    (by rw [storeVal_halted, storeVal_halted]; exact hrel.halted) (by rw [storeVal_tail, storeVal_tail]; exact hrel.tail)
    (by rw [storeVal_err, storeVal_err]; exact hrel.err) rsp (.ptr ⟨rStack, B f.sp.1 + (f.sp.2 - 8)⟩)
  refine ⟨store_rel hB h01 h8 (sl := (f.sp.1, f.sp.2 - 8, 8)) hb rfl hrel r hco hT'.symm rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
    by simp only [State.next, State.setG, storeVal_pc]⟩
  · intro q hq
    have h4 : ¬ q = rsp := hq4 q hq
    constructor
    · rw [getG_next, getG_setG_of_ne _ _ _ _ h4, getG_storeVal]
    · rw [getG_next, getG_setG_of_ne _ _ _ _ h4, getG_storeVal]
  · intro q hq
    by_cases h4 : q = 4
    · subst h4; rw [getG_next, getG_next]; exact hag.1
    · have h4' : ¬ q = rsp := h4
      rw [getG_next, getG_setG_of_ne _ _ _ _ h4', getG_storeVal, getG_next, getG_setG_of_ne _ _ _ _ h4', getG_storeVal]
      exact hrel.reg q hq
  · exact hag.2
  · simp only [State.next, State.setG, List.length_set, storeVal_gpr]; exact hrel.len16
  · show (storeVal s _ _).vr = (storeVal s' _ _).vr
    rw [storeVal_vr, storeVal_vr]; exact hrel.vr
  · show (storeVal s _ _).flags = (storeVal s' _ _).flags
    rw [storeVal_flags, storeVal_flags]; exact hrel.flags
  · show (storeVal s _ _).pc + 1 = (storeVal s' _ _).pc + 1
    rw [storeVal_pc, storeVal_pc, hrel.pc]
  · show (storeVal s _ _).halted = (storeVal s' _ _).halted
    rw [storeVal_halted, storeVal_halted]; exact hrel.halted
  · show (storeVal s _ _).tail = (storeVal s' _ _).tail
    rw [storeVal_tail, storeVal_tail]; exact hrel.tail
  · show (storeVal s _ _).err = (storeVal s' _ _).err
    rw [storeVal_err, storeVal_err]; exact hrel.err

/-- The second run also loads the slot: tagged slots by the relation, unlisted ones (hitting no
listed slot) by agreement. -/
theorem load_other (hB : BaseRel B) (h01 : Bases01 T) (hrel : TagRel mem0 B T s0 s0' s s')
    {sl : Slot} (hsb : sl.1 = 0 ∨ sl.1 = 1) (hs8 : sl.2.2 = 8) (hst : statusOf T (.slot sl) ≠ some none)
    (hnh : statusOf T (.slot sl) = none → hitsTagged T sl = false) {v : Val W32 Int}
    (hv : loadVal mem0 s ⟨rStack, B sl.1 + sl.2.1⟩ = .ok v) :
    ∃ v', loadVal mem0 s' ⟨rStack, B sl.1 + sl.2.1⟩ = .ok v' ∧ (statusOf T (.slot sl) = none → v = v') := by
  cases hc : statusOf T (.slot sl) with
  | none =>
    refine ⟨v, ?_, fun _ => rfl⟩
    rw [← hv]
    refine loadVal_memAg (M := Outside B T) hrel.mem mem0 rfl rfl _ (M8_of_cells _ _ (fun x hx => ?_))
    exact outside_of_not_hits hB h01 hsb (hnh hc) (by rw [hs8]; exact hx)
  | some st =>
    cases st with
    | none => exact absurd hc hst
    | some n =>
      obtain ⟨_, e2⟩ := hrel.tagSlot sl n hc
      exact ⟨_, e2, fun h => by cases h⟩

/-- The slot status read by a copy, from its `tagStep` result (`pop` / `mov r, [rsp+k]`). -/
theorem load_status {sl : Slot} {d : Nat} {R : Option Tags}
    (h : (match statusOf T (.slot sl) with
      | some none => none
      | none => if hitsTagged T sl then none else some (setStatus T (.reg d) none)
      | some (some n) => some (setStatus T (.reg d) (some (some n)))) = R) (hR : R = some T') :
    statusOf T (.slot sl) ≠ some none ∧ (statusOf T (.slot sl) = none → hitsTagged T sl = false) ∧
    T' = setStatus T (.reg d) (statusOf T (.slot sl)) := by
  subst hR
  cases hc : statusOf T (.slot sl) with
  | none =>
    simp only [hc] at h
    split at h
    · cases h
    · rename_i hh; simp only [Option.some.injEq] at h; exact ⟨by simp, fun _ => by simpa using hh, h.symm⟩
  | some st =>
    cases st with
    | none => simp only [hc] at h; cases h
    | some n =>
      simp only [hc, Option.some.injEq] at h
      exact ⟨by simp, (fun h' => by cases h'), h.symm⟩

/-- `pop r`. -/
theorem pop_step (hB : BaseRel B) (h01 : Bases01 T) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    (hrel : TagRel mem0 B T s0 s0' s s') (hR : RspOk B f s) (hh : s.halted = false) (r : Nat)
    (hstep : tagStep f (.pop r) T = some T') (hok : (exec 4 mem0 orc (.pop r) s).err = none) :
    TagRel mem0 B T' s0 s0' (exec 4 mem0 orc (.pop r) s) (exec 4 mem0 orc (.pop r) s') ∧
    (exec 4 mem0 orc (.pop r) s).pc = s.pc + 1 := by
  simp only [tagStep] at hstep
  split at hstep
  · cases hstep
  rename_i hc
  have hrsp : statusOf T (.reg 4) = none := by
    cases hx : statusOf T (.reg 4) with
    | none => rfl
    | some _ => exact absurd (Or.inl (by rw [hx]; simp)) hc
  have hr4 : r ≠ 4 := fun h => hc (Or.inr (Or.inl h))
  have hr16 : r < 16 := by
    rcases Nat.lt_or_ge r 16 with h | h
    · exact h
    · exact absurd (Or.inr (Or.inr h)) hc
  obtain ⟨hst, hnh, hT'⟩ := load_status (sl := (f.sp.1, f.sp.2, 8)) (d := r) rfl hstep
  obtain ⟨hsp, hsp'⟩ := rsp_eq hrel hrsp hR
  have hh' : s'.halted = false := by rw [← hrel.halted]; exact hh
  obtain ⟨v, hv⟩ := exec_pop_err r hh hsp hok
  obtain ⟨v', hv', hvv⟩ := load_other hB h01 hrel (sl := (f.sp.1, f.sp.2, 8)) hb rfl hst hnh hv
  rw [exec_pop r hh hsp hv, exec_pop r hh' hsp' hv']
  have hag := setG_agree hrel (u := s.setG r v) (u' := s'.setG r v') (by simp [State.setG, hrel.len])
    hrel.vr hrel.flags hrel.pc hrel.halted hrel.tail hrel.err rsp (.ptr (Addr.plusI ⟨rStack, B f.sp.1 + f.sp.2⟩ 8))
  have hlen16 : (s.setG r v).gpr.length = 16 := by simp [State.setG, hrel.len16]
  have hlen16' : (s'.setG r v').gpr.length = 16 := by simp [State.setG, ← hrel.len, hrel.len16]
  refine ⟨load_rel hrel (sl := (f.sp.1, f.sp.2, 8)) r hst hv hv' hvv hT' rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩
  · have hr4' : ¬ r = rsp := hr4
    rw [getG_next, getG_setG_of_ne _ _ _ _ hr4', getG_setG_self' _ _ _ (by rw [hrel.len16]; exact hr16)]
  · have hr4' : ¬ r = rsp := hr4
    rw [getG_next, getG_setG_of_ne _ _ _ _ hr4', getG_setG_self' _ _ _ (by rw [← hrel.len, hrel.len16]; exact hr16)]
  · intro q hqr hq
    have h4 : ¬ q = rsp := fun h => hq (h ▸ hrsp)
    constructor
    · rw [getG_next, getG_setG_of_ne _ _ _ _ h4, getG_setG_ne' _ _ _ _ hqr]
    · rw [getG_next, getG_setG_of_ne _ _ _ _ h4, getG_setG_ne' _ _ _ _ hqr]
  · intro q hqr hq
    by_cases h4 : q = 4
    · subst h4; rw [getG_next, getG_next]; exact hag.1
    · have h4' : ¬ q = rsp := h4
      rw [getG_next, getG_setG_of_ne _ _ _ _ h4', getG_setG_ne' _ _ _ _ hqr, getG_next, getG_setG_of_ne _ _ _ _ h4',
        getG_setG_ne' _ _ _ _ hqr]
      exact hrel.reg q hq
  · exact hag.2
  · show ((s.setG r v).setG rsp _).gpr.length = 16
    simp [State.setG, hrel.len16]
  · exact hrel.vr
  · exact hrel.flags
  · show (s.setG r v).pc + 1 = (s'.setG r v').pc + 1
    exact congrArg (· + 1) hrel.pc
  · exact hrel.halted
  · exact hrel.tail
  · exact hrel.err


/-- Agreement on the registers of a memory operand whose registers are all agreeing. -/
theorem agreeM_regs (hrel : TagRel mem0 B T s0 s0' s s') (rs : List Nat) (hu : regsUntagged T rs = true) :
    AgreeM rs true (Outside B T) s s' where
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

/-- A store of an agreeing value outside the stack region keeps the relation at the same tags. -/
theorem store_nonstack (hrel : TagRel mem0 B T s0 s0' s s') {a : Addr Int} (ha : a.region ≠ rStack)
    {v : Val W32 Int} :
    TagRel mem0 B T s0 s0' (storeVal s a v).next (storeVal s' a v).next := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq; rw [getG_next, getG_storeVal, getG_next, getG_storeVal]; exact hrel.reg q hq
  · intro q n hq; rw [getG_next, getG_storeVal, getG_next, getG_storeVal]; exact hrel.tagReg q n hq
  · intro t n ht
    obtain ⟨e1, e2⟩ := hrel.tagSlot t n ht
    unfold slotVal at e1 e2 ⊢
    have hd : ∀ x, Cells ⟨rStack, B t.1 + t.2.1⟩ 8 x → ¬ Cells a 8 x := by
      intro x hx hc; exact ha (by rw [← cells_region hc, cells_region hx])
    constructor
    · rw [← e1]
      exact (loadVal_memAg (M := Cells ⟨rStack, B t.1 + t.2.1⟩ 8)
        (fun x hx => show lookup x (storeVal s a v).next.mem = lookup x s.mem from lookup_storeVal_untouched _ _ _ _ (hd x hx))
        mem0 rfl rfl _ (M8_of_cells _ _ (fun x hx => hx))).symm
    · rw [← e2]
      exact (loadVal_memAg (M := Cells ⟨rStack, B t.1 + t.2.1⟩ 8)
        (fun x hx => show lookup x (storeVal s' a v).next.mem = lookup x s'.mem from lookup_storeVal_untouched _ _ _ _ (hd x hx))
        mem0 rfl rfl _ (M8_of_cells _ _ (fun x hx => hx))).symm
  · intro x hx
    show lookup x (storeVal s a v).mem = lookup x (storeVal s' a v).mem
    by_cases hc : Cells a 8 x
    · exact lookup_storeVal_inside _ _ _ _ _ hc
    · exact lookup_storeVal_outside _ _ _ _ _ hc (hrel.mem x hx)
  · show (storeVal s a v).gpr.length = (storeVal s' a v).gpr.length
    rw [storeVal_gpr, storeVal_gpr]; exact hrel.len
  · show (storeVal s a v).gpr.length = 16
    rw [storeVal_gpr]; exact hrel.len16
  · show (storeVal s a v).vr = (storeVal s' a v).vr
    rw [storeVal_vr, storeVal_vr]; exact hrel.vr
  · show (storeVal s a v).flags = (storeVal s' a v).flags
    rw [storeVal_flags, storeVal_flags]; exact hrel.flags
  · show (storeVal s a v).pc + 1 = (storeVal s' a v).pc + 1
    rw [storeVal_pc, storeVal_pc, hrel.pc]
  · show (storeVal s a v).halted = (storeVal s' a v).halted
    rw [storeVal_halted, storeVal_halted]; exact hrel.halted
  · show (storeVal s a v).tail = (storeVal s' a v).tail
    rw [storeVal_tail, storeVal_tail]; exact hrel.tail
  · show (storeVal s a v).err = (storeVal s' a v).err
    rw [storeVal_err, storeVal_err]; exact hrel.err

/-- `mov [rsp+k], r` (64-bit) and the non-stack 64-bit store. -/
theorem movst_step (hB : BaseRel B) (h01 : Bases01 T) (h8 : Sizes8 T) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    (hrel : TagRel mem0 B T s0 s0' s s') (hR : RspOk B f s) (hh : s.halted = false) (m : MemRef) (src : Nat)
    (hstep : tagStep f (.movst 64 m src) T = some T')
    (hidx : ∀ m' ∈ memOps (.movst 64 m src), m'.1.base = some 4 → m'.1.index = none ∧ m'.1.ro = none)
    (hreg : ∀ m' ∈ memOps (.movst 64 m src), m'.1.base ≠ some 4 → ∀ a, effAddr 4 s m'.1 = .ok a → a.region ≠ rStack)
    (hok : (exec 4 mem0 orc (.movst 64 m src) s).err = none) :
    TagRel mem0 B T' s0 s0' (exec 4 mem0 orc (.movst 64 m src) s) (exec 4 mem0 orc (.movst 64 m src) s') ∧
    (exec 4 mem0 orc (.movst 64 m src) s).pc = s.pc + 1 := by
  simp only [tagStep, ite_true] at hstep
  split at hstep
  · cases hstep
  rename_i hu0
  have hu : regsUntagged T (memRegs m) = true := by simpa using hu0
  have hh' : s'.halted = false := by rw [← hrel.halted]; exact hh
  obtain ⟨a, ha⟩ := exec_movst64_err m src hh hok
  have ha' : effAddr 4 s' m = .ok a := by rw [effAddr_ag (agreeM_regs hrel _ hu) 4 (fun _ h => h)]; exact ha
  rw [exec_movst64 m src hh ha, exec_movst64 m src hh' ha']
  split at hstep
  · rename_i sl hsl
    obtain ⟨T1, hco, hT'⟩ := Option.map_eq_some_iff.mp hstep
    have hb4 : m.base = some 4 ∧ m.index = none ∧ m.ro = none := by
      simp only [slotOf] at hsl; split at hsl
      · assumption
      · cases hsl
    have hsl' : sl = (f.sp.1, f.sp.2 + m.disp, 8) := by
      simp only [slotOf, hb4, and_self, ite_true, Option.some.injEq] at hsl; exact hsl.symm
    subst hsl'
    rw [effAddr_rsp hR m hb4.1 hb4.2.1 hb4.2.2] at ha
    simp only [Except.ok.injEq] at ha
    subst ha
    have haddr : (⟨rStack, B f.sp.1 + f.sp.2 + m.disp⟩ : Addr Int) = ⟨rStack, B f.sp.1 + (f.sp.2 + m.disp)⟩ := by
      congr 1; omega
    rw [haddr]
    refine ⟨store_rel hB h01 h8 (sl := (f.sp.1, f.sp.2 + m.disp, 8)) hb rfl hrel src hco hT'.symm rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,
      by simp only [State.next, storeVal_pc]⟩
    · intro q _; constructor <;> rw [getG_next, getG_storeVal]
    · intro q hq; rw [getG_next, getG_storeVal, getG_next, getG_storeVal]; exact hrel.reg q hq
    · show (storeVal s _ _).gpr.length = (storeVal s' _ _).gpr.length
      rw [storeVal_gpr, storeVal_gpr]; exact hrel.len
    · show (storeVal s _ _).gpr.length = 16
      rw [storeVal_gpr]; exact hrel.len16
    · show (storeVal s _ _).vr = (storeVal s' _ _).vr
      rw [storeVal_vr, storeVal_vr]; exact hrel.vr
    · show (storeVal s _ _).flags = (storeVal s' _ _).flags
      rw [storeVal_flags, storeVal_flags]; exact hrel.flags
    · show (storeVal s _ _).pc + 1 = (storeVal s' _ _).pc + 1
      rw [storeVal_pc, storeVal_pc, hrel.pc]
    · show (storeVal s _ _).halted = (storeVal s' _ _).halted
      rw [storeVal_halted, storeVal_halted]; exact hrel.halted
    · show (storeVal s _ _).tail = (storeVal s' _ _).tail
      rw [storeVal_tail, storeVal_tail]; exact hrel.tail
    · show (storeVal s _ _).err = (storeVal s' _ _).err
      rw [storeVal_err, storeVal_err]; exact hrel.err
  · rename_i hsl
    split at hstep
    · cases hstep
    rename_i hsrc0
    have hsrc : statusOf T (.reg src) = none := by simpa using hsrc0
    simp only [Option.some.injEq] at hstep
    subst hstep
    have hb4 : m.base ≠ some 4 := by
      intro h
      obtain ⟨hi, hro⟩ := hidx (m, 8) (by simp [memOps]) h
      simp only at hi hro
      simp [slotOf, h, hi, hro] at hsl
    have hreg' := hreg (m, 8) (by simp [memOps]) hb4 a ha
    rw [hrel.reg src hsrc]
    exact ⟨store_nonstack hrel hreg', by simp only [State.next, storeVal_pc]⟩

/-- `mov r, [rsp+k]` (64-bit) and the non-stack 64-bit load. -/
theorem movload_step (hB : BaseRel B) (h01 : Bases01 T) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    (hrel : TagRel mem0 B T s0 s0' s s') (hR : RspOk B f s) (hh : s.halted = false) (d : Nat) (m : MemRef)
    (hstep : tagStep f (.mov 64 d (.mem m)) T = some T')
    (hidx : ∀ m' ∈ memOps (.mov 64 d (.mem m)), m'.1.base = some 4 → m'.1.index = none ∧ m'.1.ro = none)
    (hreg : ∀ m' ∈ memOps (.mov 64 d (.mem m)), m'.1.base ≠ some 4 → ∀ a, effAddr 4 s m'.1 = .ok a → a.region ≠ rStack)
    (hok : (exec 4 mem0 orc (.mov 64 d (.mem m)) s).err = none) :
    TagRel mem0 B T' s0 s0' (exec 4 mem0 orc (.mov 64 d (.mem m)) s) (exec 4 mem0 orc (.mov 64 d (.mem m)) s') ∧
    (exec 4 mem0 orc (.mov 64 d (.mem m)) s).pc = s.pc + 1 := by
  simp only [tagStep, ite_true] at hstep
  split at hstep
  · cases hstep
  rename_i hu0
  have hu : regsUntagged T (memRegs m) = true ∧ d < 16 := by
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false] at hu0
    exact ⟨hu0.1, by omega⟩
  have hh' : s'.halted = false := by rw [← hrel.halted]; exact hh
  obtain ⟨a, v, ha, hv⟩ := exec_mov64mem_err d m hh hok
  have ha' : effAddr 4 s' m = .ok a := by rw [effAddr_ag (agreeM_regs hrel _ hu.1) 4 (fun _ h => h)]; exact ha
  have hlen16 : (s.setG d v).gpr.length = 16 := by simp [State.setG, hrel.len16]
  split at hstep
  · rename_i sl hsl
    have hb4 : m.base = some 4 ∧ m.index = none ∧ m.ro = none := by
      simp only [slotOf] at hsl; split at hsl
      · assumption
      · cases hsl
    have hsl' : sl = (f.sp.1, f.sp.2 + m.disp, 8) := by
      simp only [slotOf, hb4, and_self, ite_true, Option.some.injEq] at hsl; exact hsl.symm
    subst hsl'
    rw [effAddr_rsp hR m hb4.1 hb4.2.1 hb4.2.2] at ha
    simp only [Except.ok.injEq] at ha
    subst ha
    have haddr : (⟨rStack, B f.sp.1 + f.sp.2 + m.disp⟩ : Addr Int) = ⟨rStack, B f.sp.1 + (f.sp.2 + m.disp)⟩ := by
      congr 1; omega
    rw [haddr] at hv ha'
    have ha2 : effAddr 4 s m = .ok ⟨rStack, B f.sp.1 + (f.sp.2 + m.disp)⟩ := by
      rw [effAddr_rsp hR m hb4.1 hb4.2.1 hb4.2.2, haddr]
    obtain ⟨hst, hnh, hT'⟩ := load_status (sl := (f.sp.1, f.sp.2 + m.disp, 8)) (d := d) rfl hstep
    obtain ⟨v', hv', hvv⟩ := load_other hB h01 hrel (sl := (f.sp.1, f.sp.2 + m.disp, 8)) hb rfl hst hnh hv
    rw [exec_mov64mem d m hh ha2 hv, exec_mov64mem d m hh' ha' hv']
    refine ⟨load_rel hrel (sl := (f.sp.1, f.sp.2 + m.disp, 8)) d hst hv hv' hvv hT' rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩
    · rw [getG_next, getG_setG_self' _ _ _ (by rw [hrel.len16]; exact hu.2)]
    · rw [getG_next, getG_setG_self' _ _ _ (by rw [← hrel.len, hrel.len16]; exact hu.2)]
    · intro q hqd _; constructor <;> rw [getG_next, getG_setG_ne' _ _ _ _ hqd]
    · intro q hqd hq; rw [getG_next, getG_setG_ne' _ _ _ _ hqd, getG_next, getG_setG_ne' _ _ _ _ hqd]; exact hrel.reg q hq
    · simp [State.setG, hrel.len]
    · exact hlen16
    · exact hrel.vr
    · exact hrel.flags
    · exact congrArg (· + 1) hrel.pc
    · exact hrel.halted
    · exact hrel.tail
    · exact hrel.err
  · rename_i hsl
    simp only [Option.some.injEq] at hstep
    subst hstep
    have hb4 : m.base ≠ some 4 := by
      intro h
      obtain ⟨hi, hro⟩ := hidx (m, 8) (by simp [memOps]) h
      simp only at hi hro
      simp [slotOf, h, hi, hro] at hsl
    have hreg' := hreg (m, 8) (by simp [memOps]) hb4 a ha
    have hv' : loadVal mem0 s' a = .ok v := by
      rw [← hv]
      exact loadVal_memAg (M := Outside B T) hrel.mem mem0 rfl rfl _
        (M8_of_cells _ _ (fun x hx => outside_of_region (by rw [cells_region hx]; exact hreg')))
    rw [exec_mov64mem d m hh ha hv, exec_mov64mem d m hh' ha' hv']
    refine ⟨⟨?_, ?_, ?_, ?_, by simp [State.setG, hrel.len], hlen16, hrel.vr, hrel.flags, congrArg (· + 1) hrel.pc,
      hrel.halted, hrel.tail, hrel.err⟩, rfl⟩
    · intro q hq
      by_cases hqd : q = d
      · subst hqd
        rw [getG_next, getG_next, getG_setG_self' _ _ _ (by rw [hrel.len16]; exact hu.2),
          getG_setG_self' _ _ _ (by rw [← hrel.len, hrel.len16]; exact hu.2)]
      · rw [statusOf_clearItem_ne _ (by simpa using hqd)] at hq
        rw [getG_next, getG_setG_ne' _ _ _ _ hqd, getG_next, getG_setG_ne' _ _ _ _ hqd]; exact hrel.reg q hq
    · intro q n hq
      by_cases hqd : q = d
      · subst hqd; rw [statusOf_clearItem_self] at hq; cases hq
      · rw [statusOf_clearItem_ne _ (by simpa using hqd)] at hq
        rw [getG_next, getG_setG_ne' _ _ _ _ hqd, getG_next, getG_setG_ne' _ _ _ _ hqd]; exact hrel.tagReg q n hq
    · intro t n ht
      rw [statusOf_clearItem_ne _ (by simp)] at ht
      exact hrel.tagSlot t n ht
    · intro x hx
      apply hrel.mem
      rintro ⟨t, ht, hta⟩
      exact hx ⟨t, by rw [statusOf_clearItem_ne _ (by simp)]; exact ht, hta⟩

/-- **The copies preserve the relation.** -/
theorem copy_step (hB : BaseRel B) (h01 : Bases01 T) (h8 : Sizes8 T) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    (hrel : TagRel mem0 B T s0 s0' s s') (hR : RspOk B f s) (hh : s.halted = false) {i : Instr}
    (hcopy : isCopy i = true) (hstep : tagStep f i T = some T')
    (hidx : ∀ m ∈ memOps i, m.1.base = some 4 → m.1.index = none ∧ m.1.ro = none)
    (hreg : ∀ m ∈ memOps i, m.1.base ≠ some 4 → ∀ a, effAddr 4 s m.1 = .ok a → a.region ≠ rStack)
    (hok : (exec 4 mem0 orc i s).err = none) :
    TagRel mem0 B T' s0 s0' (exec 4 mem0 orc i s) (exec 4 mem0 orc i s') ∧
    (exec 4 mem0 orc i s).pc = s.pc + 1 := by
  cases i with
  | push r => exact push_step hB h01 h8 hb hrel hR hh r hstep
  | pop r => exact pop_step hB h01 hb hrel hR hh r hstep hok
  | movst w m src =>
    have hw : w = 64 := by simpa [isCopy] using hcopy
    subst hw
    exact movst_step hB h01 h8 hb hrel hR hh m src hstep hidx hreg hok
  | mov w d src =>
    cases src with
    | mem m =>
      have hw : w = 64 := by simpa [isCopy] using hcopy
      subst hw
      exact movload_step hB h01 hb hrel hR hh d m hstep hidx hreg hok
    | reg _ => simp [isCopy] at hcopy
    | imm _ => simp [isCopy] at hcopy
  | _ => simp [isCopy] at hcopy

/-- **One instruction of a certified stream preserves the relation.** -/
theorem lift_step (hB : BaseRel B) (h01 : Bases01 T) (h8 : Sizes8 T) (hb : f.sp.1 = 0 ∨ f.sp.1 = 1)
    (hrsp : statusOf T (.reg 4) = none) (hsav : f.saved ≠ none → statusOf T (.reg 5) = none)
    (hrel : TagRel mem0 B T s0 s0' s s') (hR : RspOk B f s) (hh : s.halted = false) {i : Instr}
    (hstep : tagStep f i T = some T')
    (hidx : ∀ m ∈ memOps i, m.1.base = some 4 → m.1.index = none ∧ m.1.ro = none)
    (hreg : ∀ m ∈ memOps i, m.1.base ≠ some 4 → ∀ a, effAddr 4 s m.1 = .ok a → a.region ≠ rStack)
    (hok : (exec 4 mem0 orc i s).err = none) :
    TagRel mem0 B T' s0 s0' (exec 4 mem0 orc i s) (exec 4 mem0 orc i s') ∧
    ((exec 4 mem0 orc i s).pc ∈ RunAgree.succs s.pc i ∨ (exec 4 mem0 orc i s).halted = true) := by
  cases hc : isCopy i with
  | false => exact general_step hB h01 h8 hb hrsp hsav hrel hR hh hc hstep hidx hreg hok
  | true =>
    obtain ⟨h1, h2⟩ := copy_step hB h01 h8 hb hrel hR hh hc hstep hidx hreg hok
    refine ⟨h1, Or.inl ?_⟩
    rw [h2]
    cases i <;> simp [isCopy] at hc <;> simp [RunAgree.succs]

end Copies


/-! ## The rsp map along a step -/

section Rsp
variable {mem0 : M0} {B : Nat → Int} {s : CS} {f f' : Fact} {orc : Nat → Bool}

theorem exec_sub_rsp (k : Int) (hh : s.halted = false) {sp : Addr Int} (hsp : s.getG 4 = .ptr sp) :
    exec 4 mem0 orc (.sub 64 4 (.imm k)) s =
      (setFlags (s.setG 4 (.ptr ⟨sp.region, sp.off + (-1) * k⟩)) sp.off k).next := by
  unfold exec
  simp only [hh, Bool.false_eq_true, ite_false, ite_true, gCtl, bind, Except.bind, pure, Except.pure]
  rw [hsp]
  simp [okOr, Addr.plus, Ctl.smul, Ctl.ofInt, Ctl.add, rNum]

theorem exec_add_rsp (k : Int) (hh : s.halted = false) {sp : Addr Int} (hsp : s.getG 4 = .ptr sp) :
    exec 4 mem0 orc (.alu .add 64 4 (.imm k)) s =
      (setFlags (s.setG 4 (.ptr ⟨sp.region, sp.off + k⟩)) (sp.off + k) 0).next := by
  unfold exec
  simp only [hh, Bool.false_eq_true, ite_false, ite_true, gCtl, bind, Except.bind, pure, Except.pure]
  have hne : ¬ (LOp.add = LOp.xor ∧ GSrc.imm k = GSrc.reg 4) := by simp
  simp only [hne, ite_false]
  rw [hsp]
  simp [okOr, Ctl.ofInt, Ctl.add, rNum]

theorem exec_and_rsp (hh : s.halted = false) {sp : Addr Int} (hsp : s.getG 4 = .ptr sp) (hreg : sp.region = rStack)
    {r : Int} (hr : andInt sp.off (-32) = some r) :
    exec 4 mem0 orc (.alu .and 64 4 (.imm (-32))) s = (clearFlags (s.setG 4 (.ptr ⟨sp.region, r⟩))).next := by
  unfold exec
  simp only [hh, Bool.false_eq_true, ite_false, ite_true, gCtl, bind, Except.bind, pure, Except.pure]
  have hne : ¬ (LOp.and = LOp.xor ∧ GSrc.imm (-32) = GSrc.reg 4) := by simp
  simp only [hne, ite_false]
  rw [hsp]
  simp [okOr, Ctl.ofInt, Ctl.asInt, hr, rNum, hreg, rStack]

theorem exec_and_rsp_some (hh : s.halted = false) {sp : Addr Int} (hsp : s.getG 4 = .ptr sp)
    (hok : (exec 4 mem0 orc (.alu .and 64 4 (.imm (-32))) s).err = none) : ∃ r, andInt sp.off (-32) = some r := by
  unfold exec at hok
  simp only [hh, Bool.false_eq_true, ite_false, ite_true, gCtl, bind, Except.bind, pure, Except.pure] at hok
  have hne : ¬ (LOp.and = LOp.xor ∧ GSrc.imm (-32) = GSrc.reg 4) := by simp
  simp only [hne, ite_false] at hok
  rw [hsp] at hok
  cases hr : andInt sp.off (-32) with
  | none =>
    simp [okOr, Ctl.ofInt, Ctl.asInt, hr] at hok
    exact absurd hok (fail_err s _)
  | some r => exact ⟨r, rfl⟩

theorem exec_mov_reg (d q : Nat) (hh : s.halted = false) :
    exec 4 mem0 orc (.mov 64 d (.reg q)) s = (s.setG d (s.getG q)).next := by
  unfold exec
  simp only [hh, Bool.false_eq_true, ite_false, ite_true]
  rfl

theorem exec_ret_rsp (hh : s.halted = false) (hlen : s.gpr.length = 16) {sp : Addr Int} (hsp : s.getG rsp = .ptr sp)
    (hok : (exec 4 mem0 orc .ret s).err = none) :
    (exec 4 mem0 orc .ret s).getG 4 = .ptr (sp.plusI 8) ∧ ∀ q, q ≠ 4 → (exec 4 mem0 orc .ret s).getG q = s.getG q := by
  unfold exec at hok ⊢
  simp only [hh, Bool.false_eq_true, ite_false] at hok ⊢
  rw [hsp] at hok ⊢
  cases hv : loadVal mem0 s sp with
  | error e => simp only [hv, bind, Except.bind] at hok; exact absurd hok (fail_err s e)
  | ok v =>
    simp only [hv, bind, Except.bind] at hok ⊢
    rcases v with ⟨lo, hi⟩ | ⟨⟨reg, off⟩⟩
    · exact absurd hok (fail_err s _)
    · by_cases h5 : reg = 5
      · subst h5
        simp only [okOr, pure, Except.pure, getG_halt]
        constructor
        · exact getG_setG_self' _ _ _ (by rw [hlen]; decide)
        · intro q hq; exact getG_setG_of_ne _ _ _ _ hq
      · exfalso
        rcases reg with _ | _ | _ | _ | _ | _ | n
        all_goals first | exact absurd hok (fail_err s _) | exact absurd rfl h5


/-- The rsp map along an instruction with no rsp form: rsp is not written, a write of rbp drops
the saved value. -/
theorem rspOk_other (hR : RspOk B f s) (hh : s.halted = false) {i : Instr}
    (hok : (exec 4 mem0 orc i s).err = none) (hst : stepOther i f = some f') :
    RspOk B f' (exec 4 mem0 orc i s) := by
  simp only [stepOther] at hst
  rcases exec_shape 4 mem0 orc i s hh with ⟨hne, _⟩ | ⟨_, _, hgpr, _, _, _, _⟩
  · exact absurd hok hne
  split at hst
  · cases hst
  · rename_i h4
    split at hst
    · rename_i h5
      simp only [Option.some.injEq] at hst; subst hst
      refine ⟨?_, fun v hv => by cases hv⟩
      rw [hgpr 4 h4]; exact hR.1
    · rename_i h5
      simp only [Option.some.injEq] at hst; subst hst
      refine ⟨?_, fun v hv => ?_⟩
      · rw [hgpr 4 h4]; exact hR.1
      · rw [hgpr 5 h5]; exact hR.2 v hv

theorem getG_setG_rsp (u : CS) (v : Val W32 Int) (h : 4 < u.gpr.length) : (u.setG rsp v).getG 4 = v :=
  getG_setG_self' u 4 v h

theorem ptr_mk_eq (r : Region) (a b : Int) (h : a = b) : (Val.ptr ⟨r, a⟩ : Val W32 Int) = Val.ptr ⟨r, b⟩ := by rw [h]

/-- **The rsp map is sound along a step**: the fact of the successor describes rsp (and the saved
rsp in rbp) of the stepped state; the aligned base is the result of `and rsp, -32`. -/
theorem rspOk_step (hR : RspOk B f s) (hh : s.halted = false) (hlen : s.gpr.length = 16) {i : Instr}
    (hst : RspMap.step i f = some f') (hok : (exec 4 mem0 orc i s).err = none)
    (hand : i = .alu .and 64 4 (.imm (-32)) → ∀ r, andInt (B f.sp.1 + f.sp.2) (-32) = some r → B (f.sp.1 + 1) = r) :
    RspOk B f' (exec 4 mem0 orc i s) := by
  have hsp : s.getG 4 = .ptr ⟨rStack, B f.sp.1 + f.sp.2⟩ := hR.1
  cases i <;> (try exact rspOk_other hR hh hok hst)
  case push r =>
    simp only [RspMap.step, Option.some.injEq] at hst; subst hst
    rw [exec_push r hh hsp]
    refine ⟨?_, fun v hv => ?_⟩
    · dsimp only
      rw [getG_next, getG_setG_rsp _ _ (by rw [storeVal_gpr, hlen]; decide), plusI_int]
      exact ptr_mk_eq _ _ _ (by (try dsimp only); omega)
    · dsimp only at hv
      rw [getG_next, getG_setG_of_ne _ _ _ _ (by decide), getG_storeVal]; exact hR.2 v hv
  case pop r =>
    simp only [RspMap.step] at hst
    split at hst
    · cases hst
    rename_i hr4
    simp only [Option.some.injEq] at hst; subst hst
    obtain ⟨v, hv⟩ := exec_pop_err r hh hsp hok
    rw [exec_pop r hh hsp hv]
    refine ⟨?_, fun w hw => ?_⟩
    · dsimp only
      rw [getG_next, getG_setG_rsp _ _ (by simp [State.setG, hlen]), plusI_int]
      exact ptr_mk_eq _ _ _ (by (try dsimp only); omega)
    · simp only at hw
      split at hw
      · cases hw
      · rename_i hr5
        rw [getG_next, getG_setG_of_ne _ _ _ _ (by decide), getG_setG_ne' _ _ _ _ (Ne.symm hr5)]; exact hR.2 w hw
  case ret =>
    simp only [RspMap.step, Option.some.injEq] at hst; subst hst
    obtain ⟨h4, hq⟩ := exec_ret_rsp hh hlen hsp hok
    refine ⟨?_, fun v hv => ?_⟩
    · dsimp only; rw [h4, plusI_int]; exact ptr_mk_eq _ _ _ (by (try dsimp only); omega)
    · dsimp only at hv; rw [hq 5 (by decide)]; exact hR.2 v hv
  case sub w d src =>
    simp only [RspMap.step] at hst
    split at hst
    · rename_i hwd
      obtain ⟨rfl, rfl⟩ := hwd
      split at hst
      · rename_i k
        simp only [Option.some.injEq] at hst; subst hst
        rw [exec_sub_rsp k hh hsp]
        refine ⟨?_, fun v hv => ?_⟩
        · dsimp only
          rw [getG_next, getG_setFlags, getG_setG_self' _ _ _ (by rw [hlen]; decide)]
          exact ptr_mk_eq _ _ _ (by (try dsimp only); omega)
        · dsimp only at hv
          rw [getG_next, getG_setFlags, getG_setG_of_ne _ _ _ _ (by decide)]; exact hR.2 v hv
      · cases hst
    · exact rspOk_other hR hh hok hst
  case alu op w d src =>
    simp only [RspMap.step] at hst
    split at hst
    · rename_i hwd
      obtain ⟨rfl, rfl⟩ := hwd
      split at hst
      · rename_i k
        simp only [Option.some.injEq] at hst; subst hst
        rw [exec_add_rsp k hh hsp]
        refine ⟨?_, fun v hv => ?_⟩
        · dsimp only
          rw [getG_next, getG_setFlags, getG_setG_self' _ _ _ (by rw [hlen]; decide)]
          exact ptr_mk_eq _ _ _ (by (try dsimp only); omega)
        · dsimp only at hv
          rw [getG_next, getG_setFlags, getG_setG_of_ne _ _ _ _ (by decide)]; exact hR.2 v hv
      · rename_i k
        split at hst
        · rename_i hk
          subst hk
          simp only [Option.some.injEq] at hst; subst hst
          obtain ⟨r, hr⟩ := exec_and_rsp_some hh hsp hok
          rw [exec_and_rsp hh hsp rfl hr]
          refine ⟨?_, fun v hv => ?_⟩
          · dsimp only
            rw [getG_next, getG_clearFlags, getG_setG_self' _ _ _ (by rw [hlen]; decide)]
            have := hand rfl r hr
            exact ptr_mk_eq _ _ _ (by rw [Int.add_zero]; exact this.symm)
          · dsimp only at hv
            rw [getG_next, getG_clearFlags, getG_setG_of_ne _ _ _ _ (by decide)]; exact hR.2 v hv
        · cases hst
      · cases hst
    · exact rspOk_other hR hh hok hst
  case mov w d src =>
    simp only [RspMap.step] at hst
    split at hst
    · rename_i hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at hst; subst hst
      rw [exec_mov_reg 5 4 hh]
      refine ⟨?_, fun v hv => ?_⟩
      · dsimp only; rw [getG_next, getG_setG_of_ne _ _ _ _ (by decide)]; exact hsp
      · simp only [Option.some.injEq] at hv; subst hv
        rw [getG_next, getG_setG_self' _ _ _ (by rw [hlen]; decide)]; exact hsp
    · split at hst
      · rename_i hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        split at hst
        · rename_i v hv
          simp only [Option.some.injEq] at hst; subst hst
          rw [exec_mov_reg 4 5 hh]
          refine ⟨?_, fun w hw => ?_⟩
          · dsimp only; rw [getG_next, getG_setG_self' _ _ _ (by rw [hlen]; decide)]; exact hR.2 v hv
          · dsimp only at hw; rw [getG_next, getG_setG_of_ne _ _ _ _ (by decide)]; exact hR.2 w hw
        · cases hst
      · exact rspOk_other hR hh hok hst

end Rsp


/-! ## The run -/

section Run
variable {mem0 : M0} {B : Nat → Int} {s0 s0' : CS} {orc : Nat → Bool}

/-- The per-pc check of the tag certificate, from the linear sweep. -/
theorem tagAux_at (n : Nat) (D : Int) (segs : List (Nat × Option Fact)) (TT : TagSegs) (cs : List Nat) :
    ∀ (p : Nat) (l : List Instr), tagAux n D segs TT cs p l = true →
      ∀ j i, l[j]? = some i → tagAt n D segs TT cs (p + j) i = true
  | _, [], _, _, _, h => by simp at h
  | p, i :: rest, h, j, i', hj => by
    simp only [tagAux, Bool.and_eq_true] at h
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; simpa using h.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have := tagAux_at n D segs TT cs (p + 1) rest h.2 j i' hj
      rwa [show p + (j + 1) = p + 1 + j by omega]

theorem tagCert_at {n : Nat} {D : Int} {prog : Array Instr} {segs : List (Nat × Option Fact)} {TT : TagSegs}
    {cs : List Nat} (h : tagCert n D prog segs TT cs = true) {p : Nat} {i : Instr} (hp : prog[p]? = some i) :
    tagAt n D segs TT cs p i = true := by
  simp only [tagCert, Bool.and_eq_true] at h
  have := tagAux_at n D segs TT cs 0 prog.toList h.2 p i (by rw [Array.getElem?_toList]; exact hp)
  simpa using this

theorem okAux_at (n : Nat) (segs : List (Nat × Option Fact)) :
    ∀ (p : Nat) (l : List Instr), okAux n segs p l = true →
      ∀ j i, l[j]? = some i → okAt n segs (p + j) i = true
  | _, [], _, _, _, h => by simp at h
  | p, i :: rest, h, j, i', hj => by
    simp only [okAux, Bool.and_eq_true] at h
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; simpa using h.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have := okAux_at n segs (p + 1) rest h.2 j i' hj
      rwa [show p + (j + 1) = p + 1 + j by omega]

theorem ok_at {n : Nat} {prog : Array Instr} {segs : List (Nat × Option Fact)} (h : RspMap.ok n prog segs = true)
    {p : Nat} {i : Instr} (hp : prog[p]? = some i) : okAt n segs p i = true := by
  simp only [RspMap.ok, Bool.and_eq_true] at h
  have := okAux_at n segs 0 prog.toList h.2 p i (by rw [Array.getElem?_toList]; exact hp)
  simpa using this

/-- A listed item is an entry with its status. -/
theorem statusOf_eq_some {T : Tags} {i : Item} {st : Option Nat} (h : statusOf T i = some st) :
    ∃ p ∈ T, p.1 = i ∧ p.2 = st := by
  induction T with
  | nil => simp [statusOf_nil] at h
  | cons p T ih =>
    rw [statusOf_cons] at h
    split at h
    · rename_i hp; simp only [Option.some.injEq] at h; exact ⟨p, List.mem_cons_self .., hp, h⟩
    · obtain ⟨q, hq, h1, h2⟩ := ih h; exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

theorem mem_statusOf {T : Tags} {p : Item × Option Nat} (h : p ∈ T) : statusOf T p.1 ≠ none := by
  induction T with
  | nil => simp at h
  | cons q T ih =>
    rw [statusOf_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · simp
    · split
      · simp
      · exact ih h'

/-- The window of the listed slots: every cell is in `[B 0 - D, B 0)`. -/
def InWindow (D : Int) (B : Nat → Int) (T : Tags) : Prop :=
  ∀ sl, statusOf T (.slot sl) ≠ none → ∀ a, inSlot B sl a → B 0 - D ≤ a.off ∧ a.off < B 0

theorem tableOk_facts {D : Int} {T : Tags} (hB : BaseRel B) (h : tableOk D T = true) :
    Bases01 T ∧ Sizes8 T ∧ InWindow D B T := by
  simp only [tableOk, List.all_eq_true] at h
  have hs : ∀ sl, statusOf T (.slot sl) ≠ none →
      sl.2.2 = 8 ∧ ((sl.1 = 0 ∧ -D ≤ sl.2.1 ∧ sl.2.1 + 8 ≤ 0) ∨ (sl.1 = 1 ∧ 47 - D ≤ sl.2.1 ∧ sl.2.1 + 8 ≤ -16)) := by
    intro sl hsl
    obtain ⟨p, hp, hpi⟩ := listed_mem hsl
    have := h p hp
    rw [hpi] at this
    simpa [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using this
  refine ⟨fun sl hsl => ?_, fun sl hsl => (hs sl hsl).1, fun sl hsl a ha => ?_⟩
  · rcases (hs sl hsl).2 with ⟨h0, _⟩ | ⟨h1, _⟩
    · exact Or.inl h0
    · exact Or.inr h1
  · obtain ⟨_, h2, h3⟩ := ha
    obtain ⟨h8, hc⟩ := hs sl hsl
    obtain ⟨hB1, hB2⟩ := hB
    rw [h8] at h3
    rcases hc with ⟨h0, h4, h5⟩ | ⟨h1, h4, h5⟩
    · rw [h0] at h2 h3; omega
    · rw [h1] at h2 h3; omega

/-- The relation is monotone along the status lattice (`leqTags`). -/
theorem tagRel_mono {T T' : Tags} (hle : leqTags T T' = true) {s s' : CS}
    (h : TagRel mem0 B T s0 s0' s s') : TagRel mem0 B T' s0 s0' s s' := by
  simp only [leqTags, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hle
  obtain ⟨h1, h2⟩ := hle
  -- an item unlisted in `T'` is unlisted in `T`
  have unl : ∀ i, statusOf T' i = none → statusOf T i = none := by
    intro i hi
    cases hc : statusOf T i with
    | none => rfl
    | some st =>
      obtain ⟨p, hp, hpi, _⟩ := statusOf_eq_some hc
      rcases h1 p hp with h' | h' <;> (rw [hpi] at h'; rw [hi] at h'; cases h')
  -- an item tagged in `T'` is tagged the same in `T`
  have tg : ∀ i n, statusOf T' i = some (some n) → statusOf T i = some (some n) := by
    intro i n hi
    obtain ⟨p, hp, hpi, hpn⟩ := statusOf_eq_some hi
    rcases h2 p hp with h' | h'
    · rw [hpn] at h'; cases h'
    · rw [hpi, hpn] at h'; exact h'
  refine ⟨?_, ?_, ?_, ?_, h.len, h.len16, h.vr, h.flags, h.pc, h.halted, h.tail, h.err⟩
  · intro r hr; exact h.reg r (unl _ hr)
  · intro r n hr; exact h.tagReg r n (tg _ n hr)
  · intro t n ht; exact h.tagSlot t n (tg _ n ht)
  · intro a ha
    apply h.mem
    rintro ⟨t, ht, hta⟩
    apply ha
    refine ⟨t, ?_, hta⟩
    intro h0; exact ht (unl _ h0)

theorem nexts_eq_succs (p : Nat) (i : Instr) : nexts p i = RunAgree.succs p i := by cases i <;> rfl

theorem run_succ' (prog : Array Instr) (n : Nat) (s : CS) {i : Instr} (hh : s.halted = false)
    (hi : prog[s.pc]? = some i) : run prog 4 mem0 orc (n + 1) s = run prog 4 mem0 orc n (exec 4 mem0 orc i s) := by
  simp [run, hh, hi]

theorem run_halted' (prog : Array Instr) (n : Nat) (s : CS) (hh : s.halted = true) : run prog 4 mem0 orc n s = s := by
  cases n with
  | zero => rfl
  | succ n => simp [run, hh]

/-- The exits of a certified stream halt the machine with every callee-saved register restored. -/
theorem halts_of_isExit {i : Instr} (h : isExit i = false) : halts i = false := by
  cases i <;> simp_all [isExit, halts]

/-- The run invariant: at a mapped, visited pc, related states under the pc's facts; or halted
at an exit with the exit tags (every callee-saved register tagged with itself) inside the frame. -/
def Inv (D : Int) (segs : List (Nat × Option Fact)) (TT : TagSegs) (cs : List Nat) (s s' : CS) : Prop :=
  (s.halted = false ∧ ∃ f T, at? segs s.pc = some f ∧ atT TT s.pc = some T ∧ RspOk B f s ∧
      TagRel mem0 B T s0 s0' s s') ∨
  (s.halted = true ∧ ∃ T, FrameTags.exitOk cs T = true ∧ InWindow D B T ∧ TagRel mem0 B T s0 s0' s s')

/-- The region hypothesis at a state: every memory operand of its instruction whose base is not
rsp evaluates outside `rStack`. -/
def RegionOk (prog : Array Instr) (u : CS) : Prop :=
  ∀ i, prog[u.pc]? = some i → ∀ m ∈ memOps i, m.1.base ≠ some 4 → ∀ a, effAddr 4 u m.1 = .ok a → a.region ≠ rStack

/-- The base hypothesis: the aligned base is the result of `and rsp, -32` at its pc. -/
def AndOk (prog : Array Instr) (segs : List (Nat × Option Fact)) (B : Nat → Int) : Prop :=
  ∀ p f, at? segs p = some f → prog[p]? = some (.alu .and 64 4 (.imm (-32))) →
    ∀ r, andInt (B f.sp.1 + f.sp.2) (-32) = some r → B (f.sp.1 + 1) = r

/-- One certified step keeps the invariant. -/
theorem inv_step {n : Nat} {D : Int} {prog : Array Instr} {segs : List (Nat × Option Fact)} {TT : TagSegs}
    {cs : List Nat} (hsz : prog.size = n) (hok0 : RspMap.ok n prog segs = true)
    (hcert : tagCert n D prog segs TT cs = true) (hB : BaseRel B) (hand : AndOk prog segs B)
    (hidx : ∀ (p : Nat) (i : Instr), prog[p]? = some i → ∀ m ∈ memOps i, m.1.base = some 4 → m.1.index = none ∧ m.1.ro = none)
    {s s' : CS} (hinv : Inv (B := B) (mem0 := mem0) (s0 := s0) (s0' := s0') D segs TT cs s s')
    (hreg : RegionOk prog s) {i : Instr} (hi : prog[s.pc]? = some i) (hh : s.halted = false)
    (hok : (exec 4 mem0 orc i s).err = none) :
    Inv (B := B) (mem0 := mem0) (s0 := s0) (s0' := s0') D segs TT cs (exec 4 mem0 orc i s) (exec 4 mem0 orc i s') := by
  rcases hinv with ⟨_, f, T, hf, hT, hR, hrel⟩ | ⟨hh', _⟩
  · -- the per-pc facts
    have hta := tagCert_at hcert hi
    have hoa := ok_at hok0 hi
    simp only [tagAt, hf, hT, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hta
    simp only [okAt, hf, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hoa
    obtain ⟨⟨⟨hrsp, hsav⟩, htab⟩, hrest⟩ := hta
    obtain ⟨hb, hrest'⟩ := hoa
    split at hrest
    · cases hrest
    rename_i T' hstep
    split at hrest'
    · cases hrest'
    rename_i f' hst
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq] at hrest hrest'
    obtain ⟨hexit, hsucc⟩ := hrest
    obtain ⟨_, hsucc'⟩ := hrest'
    obtain ⟨h01, h8, hwin⟩ := tableOk_facts hB htab
    have hsav' : f.saved ≠ none → statusOf T (.reg 5) = none := fun h => by
      rcases hsav with h' | h'
      · exact absurd h' h
      · exact h'
    obtain ⟨hrel', hpc⟩ := lift_step hB h01 h8 hb hrsp hsav' hrel hR hh hstep (hidx _ _ hi) (hreg i hi) hok
    have hR' := rspOk_step hR hh hrel.len16 hst hok (fun hi' r hr => hand _ f hf (hi' ▸ hi) r hr)
    -- the exit / successor
    rcases hpc with hq | hhalt
    · have hq' : (exec 4 mem0 orc i s).pc ∈ nexts s.pc i := by rw [nexts_eq_succs]; exact hq
      obtain ⟨_, hTq⟩ := hsucc _ hq'
      obtain ⟨_, hfq⟩ := hsucc' _ hq'
      split at hTq
      · rename_i Tq hTq'
        rcases exec_shape 4 mem0 orc i s hh with ⟨hne, _⟩ | ⟨_, hhalt, _⟩
        · exact absurd hok hne
        · by_cases hhl : (exec 4 mem0 orc i s).halted = true
          · -- halted and at a successor: an exit (jccTail) -- use the exit branch
            right
            refine ⟨hhl, T', ?_, ?_, hrel'⟩
            · rcases hhalt with h' | h'
              · rw [hhl] at h'; rw [hh] at h'; cases h'
              · have : isExit i = true := by cases i <;> simp_all [isExit, halts]
                rw [this] at hexit
                rcases hexit with h | h
                · cases h
                · exact h
            · intro sl hsl a ha
              apply hwin sl _ a ha
              cases hc : isCopy i with
              | false =>
                have hg : generalStep f i T = some T' := by rwa [tagStep_general hc] at hstep
                exact fun h0 => hsl ((general_slot_status hg sl).1.mpr h0)
              | true =>
                -- halting instructions are not copies
                exfalso
                rcases hhalt with h' | h'
                · rw [hhl] at h'; rw [hh] at h'; cases h'
                · cases i <;> simp_all [isCopy, halts]
          · left
            refine ⟨by simpa using hhl, f', Tq, hfq, hTq', hR', tagRel_mono hTq hrel'⟩
      · cases hTq
    · right
      refine ⟨hhalt, T', ?_, ?_, hrel'⟩
      · rcases exec_shape 4 mem0 orc i s hh with ⟨hne, _⟩ | ⟨_, hhalt', _⟩
        · exact absurd hok hne
        · rcases hhalt' with h' | h'
          · rw [hhalt] at h'; rw [hh] at h'; cases h'
          · have : isExit i = true := by cases i <;> simp_all [isExit, halts]
            rw [this] at hexit
            rcases hexit with h | h
            · cases h
            · exact h
      · intro sl hsl a ha
        apply hwin sl _ a ha
        cases hc : isCopy i with
        | false =>
          have hg : generalStep f i T = some T' := by rwa [tagStep_general hc] at hstep
          exact fun h0 => hsl ((general_slot_status hg sl).1.mpr h0)
        | true =>
          exfalso
          rcases exec_shape 4 mem0 orc i s hh with ⟨hne, _⟩ | ⟨_, hhalt', _⟩
          · exact absurd hok hne
          · rcases hhalt' with h' | h'
            · rw [hhalt] at h'; rw [hh] at h'; cases h'
            · cases i <;> simp_all [isCopy, halts]
  · rw [hh'] at hh; cases hh

/-- **The run lift**: the invariant holds along every error-free run of a certified stream. -/
theorem run_lift {n : Nat} {D : Int} {prog : Array Instr} {segs : List (Nat × Option Fact)} {TT : TagSegs}
    {cs : List Nat} (hsz : prog.size = n) (hok0 : RspMap.ok n prog segs = true)
    (hcert : tagCert n D prog segs TT cs = true) (hB : BaseRel B) (hand : AndOk prog segs B)
    (hidx : ∀ (p : Nat) (i : Instr), prog[p]? = some i → ∀ m ∈ memOps i, m.1.base = some 4 → m.1.index = none ∧ m.1.ro = none) :
    ∀ (k : Nat) (s s' : CS), Inv (B := B) (mem0 := mem0) (s0 := s0) (s0' := s0') D segs TT cs s s' →
      (∀ j, j ≤ k → (run prog 4 mem0 orc j s).halted = false → RegionOk prog (run prog 4 mem0 orc j s)) →
      (run prog 4 mem0 orc k s).err = none →
      Inv (B := B) (mem0 := mem0) (s0 := s0) (s0' := s0') D segs TT cs (run prog 4 mem0 orc k s) (run prog 4 mem0 orc k s')
  | 0, s, s', hinv, _, _ => hinv
  | k + 1, s, s', hinv, hreg, hok => by
    by_cases hh : s.halted = true
    · have hh' : s'.halted = true := by
        rcases hinv with ⟨h0, _⟩ | ⟨_, T, _, _, hrel⟩
        · rw [h0] at hh; cases hh
        · rw [← hrel.halted]; exact hh
      rw [run_halted' prog _ s hh, run_halted' prog _ s' hh']
      exact hinv
    · have hh0 : s.halted = false := by simpa using hh
      have hrel : s'.halted = false ∧ s'.pc = s.pc := by
        rcases hinv with ⟨_, _, _, _, _, _, hrel⟩ | ⟨h1, _⟩
        · exact ⟨by rw [← hrel.halted]; exact hh0, hrel.pc.symm⟩
        · rw [h1] at hh0; cases hh0
      cases hi : prog[s.pc]? with
      | none =>
        -- `pc out of program`: the run fails
        exfalso
        have : (run prog 4 mem0 orc (k + 1) s).err ≠ none := by
          simp only [run, hh0, Bool.false_eq_true, ite_false, hi]
          exact fail_err s _
        exact this hok
      | some i =>
        rw [run_succ' prog k s hh0 hi] at hok ⊢
        rw [run_succ' prog k s' hrel.1 (by rw [hrel.2]; exact hi)]
        have hok1 : (exec 4 mem0 orc i s).err = none :=
          RunExit.run_err_none prog 4 mem0 orc k _ hok 0 (Nat.zero_le _)
        have hreg0 : RegionOk prog s := hreg 0 (Nat.zero_le _) hh0
        apply run_lift hsz hok0 hcert hB hand hidx k _ _
          (inv_step hsz hok0 hcert hB hand hidx hinv hreg0 hi hh0 hok1)
          (fun j hj hhj => by
            have := hreg (j + 1) (by omega)
            rw [run_succ' prog j s hh0 hi] at this
            exact this hhj)
          hok

end Run


/-! ## Entry, exit, and the top-level statement -/

section Top
variable {mem0 : M0} {B : Nat → Int} {orc : Nat → Bool}

theorem entryTags_reg (cs : List Nat) (hnd : cs.Nodup) (r : Nat) :
    statusOf (entryTags cs) (.reg r) = if r ∈ cs then some (some r) else none := by
  induction cs with
  | nil => simp [entryTags, statusOf_nil]
  | cons c cs ih =>
    simp only [entryTags, List.map_cons, statusOf_cons]
    by_cases hc : c = r
    · subst hc; simp
    · simp only [Item.reg.injEq, hc, ite_false, List.mem_cons]
      rw [show List.map (fun r => (Item.reg r, some r)) cs = entryTags cs from rfl, ih (List.nodup_cons.mp hnd).2]
      simp [Ne.symm hc]

theorem entryTags_slot (cs : List Nat) (t : Slot) : statusOf (entryTags cs) (.slot t) = none := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [entryTags, List.map_cons, statusOf_cons]
    rw [show List.map (fun r => (Item.reg r, some r)) cs = entryTags cs from rfl, ih]
    simp

/-- The entry relation: two call states that agree on everything except the callee-saved
registers (and are at pc 0 with the register file of length 16). -/
theorem entry_rel (cs : List Nat) {s0 s0' : CS} (hreg : ∀ r, r ∉ cs → s0.getG r = s0'.getG r)
    (hlen : s0.gpr.length = s0'.gpr.length) (hlen16 : s0.gpr.length = 16) (hvr : s0.vr = s0'.vr)
    (hfl : s0.flags = s0'.flags) (hmem : s0.mem = s0'.mem) (hpc : s0.pc = s0'.pc) (hh : s0.halted = s0'.halted)
    (htl : s0.tail = s0'.tail) (he : s0.err = s0'.err) (hnd : cs.Nodup) :
    TagRel mem0 B (entryTags cs) s0 s0' s0 s0' := by
  refine ⟨?_, ?_, ?_, ?_, hlen, hlen16, hvr, hfl, hpc, hh, htl, he⟩
  · intro r hr; rw [entryTags_reg cs hnd] at hr; split at hr; · cases hr
    exact hreg r ‹_›
  · intro r n hr; rw [entryTags_reg cs hnd] at hr; split at hr
    · simp only [Option.some.injEq] at hr; subst hr; exact ⟨rfl, rfl⟩
    · cases hr
  · intro t n ht; rw [entryTags_slot] at ht; cases ht
  · intro a _; rw [hmem]

/-- At an exit: every callee-saved register holds its entry value in both runs, and the two
runs agree outside the frame window (and on everything but the general registers). -/
theorem exit_facts {D : Int} {segs : List (Nat × Option Fact)} {TT : TagSegs} {cs : List Nat} {s0 s0' s s' : CS}
    (hinv : Inv (B := B) (mem0 := mem0) (s0 := s0) (s0' := s0') D segs TT cs s s') (hh : s.halted = true) :
    (∀ r ∈ cs, s.getG r = s0.getG r ∧ s'.getG r = s0'.getG r) ∧
    (∀ a : Addr Int, (a.region ≠ rStack ∨ a.off < B 0 - D ∨ B 0 ≤ a.off) → lookup a s.mem = lookup a s'.mem) ∧
    s.getG 4 = s'.getG 4 ∧ s.vr = s'.vr ∧ s.flags = s'.flags ∧ s.pc = s'.pc ∧ s.halted = s'.halted ∧
    s.tail = s'.tail ∧ s.err = s'.err := by
  rcases hinv with ⟨h0, _⟩ | ⟨_, T, hex, hwin, hrel⟩
  · rw [h0] at hh; cases hh
  · simp only [FrameTags.exitOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hex
    refine ⟨fun r hr => hrel.tagReg r r (hex.1 r hr), fun a ha => hrel.mem a ?_, hrel.reg 4 hex.2, hrel.vr,
      hrel.flags, hrel.pc, hrel.halted, hrel.tail, hrel.err⟩
    rintro ⟨t, ht, hta⟩
    have hw := hwin t ht a hta
    rcases ha with h | h | h
    · exact h hta.1
    · omega
    · omega

/-- `slotsOk` gives the operand condition of the lift. -/
theorem slotsOkAux_at (segs : List (Nat × Option Fact)) :
    ∀ (p : Nat) (l : List Instr), slotsOkAux segs p l = true → ∀ j i, l[j]? = some i → slotsOkAt segs (p + j) i = true
  | _, [], _, _, _, h => by simp at h
  | p, i :: rest, h, j, i', hj => by
    simp only [slotsOkAux, Bool.and_eq_true] at h
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; simpa using h.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have := slotsOkAux_at segs (p + 1) rest h.2 j i' hj
      rwa [show p + (j + 1) = p + 1 + j by omega]

theorem hidx_of_slotsOk {prog : Array Instr} {segs : List (Nat × Option Fact)} (h : slotsOk prog segs = true) :
    ∀ (p : Nat) (i : Instr), prog[p]? = some i → ∀ m ∈ memOps i, m.1.base = some 4 → m.1.index = none ∧ m.1.ro = none := by
  intro p i hp m hm hb
  have := slotsOkAux_at segs 0 prog.toList h p i (by rw [Array.getElem?_toList]; exact hp)
  simp only [Nat.zero_add, slotsOkAt, Bool.and_eq_true, Bool.not_eq_true', rspIndexed, List.any_eq_false] at this
  have h1 := this.1 m hm
  simp only [hb, true_and, decide_eq_true_eq, not_or] at h1
  exact ⟨Decidable.not_not.mp h1.1, Decidable.not_not.mp h1.2⟩

/-- The region of an effective address: rip-relative operands read the rodata region, register
bases carry their register's region (an index only moves the offset). -/
theorem effAddr_region (u : CS) (m : MemRef) {a : Addr Int} (ha : effAddr 4 u m = .ok a) :
    (m.ro ≠ none ∧ a.region = 4) ∨ (m.ro = none ∧ m.base = none ∧ a.region = rNum) ∨
    (m.ro = none ∧ ∃ b p, m.base = some b ∧ u.getG b = .ptr p ∧ a.region = p.region) := by
  simp only [effAddr, baseAddr] at ha
  cases hro : m.ro with
  | some o =>
    rw [hro] at ha
    simp only at ha
    left
    refine ⟨by simp, ?_⟩
    cases hi : m.index with
    | none => rw [hi] at ha; simp only [Except.ok.injEq] at ha; rw [← ha]; rfl
    | some i =>
      rw [hi] at ha
      simp only at ha
      split at ha
      · rename_i n _
        simp only [Except.ok.injEq] at ha; rw [← ha]; rfl
      · cases ha
  | none =>
    rw [hro] at ha
    simp only at ha
    cases hb : m.base with
    | none =>
      rw [hb] at ha; simp only at ha
      right; left
      refine ⟨rfl, rfl, ?_⟩
      cases hi : m.index with
      | none => rw [hi] at ha; simp only [Except.ok.injEq] at ha; rw [← ha]; rfl
      | some i =>
        rw [hi] at ha; simp only at ha
        split at ha
        · simp only [Except.ok.injEq] at ha; rw [← ha]; rfl
        · cases ha
    | some b =>
      rw [hb] at ha; simp only [regPtr] at ha
      right; right
      refine ⟨rfl, b, ?_⟩
      cases hg : u.getG b with
      | num _ _ => rw [hg] at ha; simp at ha
      | ptr p =>
        rw [hg] at ha; simp only at ha
        refine ⟨p, rfl, rfl, ?_⟩
        cases hi : m.index with
        | none => rw [hi] at ha; simp only [Except.ok.injEq] at ha; rw [← ha]; rfl
        | some i =>
          rw [hi] at ha; simp only at ha
          split at ha
          · simp only [Except.ok.injEq] at ha; rw [← ha]; rfl
          · cases ha

/-- **The frame-slot lift, top level**: for a stream with a verified rsp map and tag certificate,
two runs from call states that differ only in the callee-saved registers, under the base and
region hypotheses, stay related; when the first run halts after `k` error-free steps, every
callee-saved register holds its entry value in both runs, the runs agree outside the frame
window `[B 0 - D, B 0)` of the stack, and on rsp, the vector file, flags, pc, halted, tail, err. -/
theorem frame_lift {n : Nat} {D : Int} {prog : Array Instr} {segs : List (Nat × Option Fact)} {TT : TagSegs}
    {cs : List Nat} {f0 : Fact}
    (hsz : prog.size = n) (hok0 : RspMap.ok n prog segs = true) (hsl : slotsOk prog segs = true)
    (hcert : tagCert n D prog segs TT cs = true) (hnd : cs.Nodup) (hf0 : at? segs 0 = some f0)
    (hB : BaseRel B) (hand : AndOk prog segs B) {s0 s0' : CS}
    (hreg : ∀ r, r ∉ cs → s0.getG r = s0'.getG r) (hlen : s0.gpr.length = s0'.gpr.length) (hlen16 : s0.gpr.length = 16)
    (hvr : s0.vr = s0'.vr) (hfl : s0.flags = s0'.flags) (hmem : s0.mem = s0'.mem) (hpc : s0.pc = 0) (hpc' : s0'.pc = 0)
    (hh : s0.halted = false) (hh' : s0'.halted = false) (htl : s0.tail = s0'.tail) (he : s0.err = s0'.err)
    (hR : RspOk B f0 s0) (k : Nat)
    (hregion : ∀ j, j ≤ k → (run prog 4 mem0 orc j s0).halted = false → RegionOk prog (run prog 4 mem0 orc j s0))
    (hok : (run prog 4 mem0 orc k s0).err = none) (hhalt : (run prog 4 mem0 orc k s0).halted = true) :
    (∀ r ∈ cs, (run prog 4 mem0 orc k s0).getG r = s0.getG r ∧ (run prog 4 mem0 orc k s0').getG r = s0'.getG r) ∧
    (∀ a : Addr Int, (a.region ≠ rStack ∨ a.off < B 0 - D ∨ B 0 ≤ a.off) →
      lookup a (run prog 4 mem0 orc k s0).mem = lookup a (run prog 4 mem0 orc k s0').mem) ∧
    (run prog 4 mem0 orc k s0).getG 4 = (run prog 4 mem0 orc k s0').getG 4 ∧
    (run prog 4 mem0 orc k s0).vr = (run prog 4 mem0 orc k s0').vr ∧
    (run prog 4 mem0 orc k s0).flags = (run prog 4 mem0 orc k s0').flags ∧
    (run prog 4 mem0 orc k s0).pc = (run prog 4 mem0 orc k s0').pc ∧
    (run prog 4 mem0 orc k s0).halted = (run prog 4 mem0 orc k s0').halted ∧
    (run prog 4 mem0 orc k s0).tail = (run prog 4 mem0 orc k s0').tail ∧
    (run prog 4 mem0 orc k s0).err = (run prog 4 mem0 orc k s0').err := by
  have hT0 : atT TT 0 = some (entryTags cs) := by
    simp only [tagCert, Bool.and_eq_true, decide_eq_true_eq] at hcert; exact hcert.1
  have hinv0 : Inv (B := B) (mem0 := mem0) (s0 := s0) (s0' := s0') D segs TT cs s0 s0' := by
    left
    refine ⟨hh, f0, entryTags cs, by rw [hpc]; exact hf0, by rw [hpc]; exact hT0, hR, ?_⟩
    exact entry_rel cs hreg hlen hlen16 hvr hfl hmem (by rw [hpc, hpc']) (by rw [hh, hh']) htl he hnd
  have hinv := run_lift hsz hok0 hcert hB hand (hidx_of_slotsOk hsl) k s0 s0' hinv0 hregion hok
  exact exit_facts hinv hhalt

end Top

end Hashtree.Proofs.FrameLift
