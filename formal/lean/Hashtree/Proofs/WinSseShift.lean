import Hashtree.Proofs.WinFrameStack

/-!
# R5: the stack-memory shift of the `sse_x1`/`avx_x1` frame transfer

`sse_x1`/`avx_x1` keep the linux `rsp`-relative displacements but their body-entry `rsp` is 128
lower (`entry_rsp-264` against `entry_rsp-136`), so the windows body touches cells 128 below the
linux ones.  The shani frame transfer (`WinFrameStack.exec_frame`) cannot apply: it needs
`δ + d = 0`, i.e. both runs touching the same absolute cells.

This module starts the relation the transfer needs (R5.md section 12): a shift of the `rStack`
part of the address space and of the memory log, lifting to a state `shSt μ`.  `shCell` shifts
the *payload* of pointer cells as well, because a saved stack pointer is itself shifted in the
windows run.

Proved here: the address algebra (`shAddr` commutes with `plusI`, preserves regions and the
address comparison `AddrEq.same`).  The `lookup`/`readCell`/store/load commutation and the
39-case `exec_sh` dispatch are the next step; see R5.md section 12.
-/

open Hashtree.Asm
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.deprecated false

namespace Hashtree.Asm.X86

/-- Shift an address into the stack region by `μ`: `⟨rStack, o⟩ ↦ ⟨rStack, o + μ⟩`; every other
address is unchanged. -/
def shAddr (μ : Int) (a : Addr Int) : Addr Int :=
  if a.region = rStack then a.plusI μ else a

/-- Shift the payload of a pointer cell: a `pb` cell of a stack pointer is itself shifted. -/
def shCell (μ : Int) : Cell W32 Int → Cell W32 Int
  | .dat x k => .dat x k
  | .pb a k => .pb (shAddr μ a) k

/-- Shift every address and every pointer payload of a memory log. -/
def shLog (μ : Int) (l : List (Addr Int × Cell W32 Int)) : List (Addr Int × Cell W32 Int) :=
  l.map (fun p => (shAddr μ p.1, shCell μ p.2))

/-- Shift a register value: a stack pointer is shifted, a number or any other pointer is not. -/
def shVal (μ : Int) : Val W32 Int → Val W32 Int
  | .ptr a => .ptr (shAddr μ a)
  | .num l h => .num l h

/-- The shifted state: every register value and every memory cell is shifted by `μ`. -/
def shSt (μ : Int) (s : State W32 Int) : State W32 Int :=
  { s with gpr := s.gpr.map (shVal μ), mem := shLog μ s.mem }

@[simp] theorem shSt_gpr (μ : Int) (s : State W32 Int) :
    (shSt μ s).gpr = s.gpr.map (shVal μ) := rfl

@[simp] theorem shSt_mem (μ : Int) (s : State W32 Int) :
    (shSt μ s).mem = shLog μ s.mem := rfl

@[simp] theorem shSt_vr (μ : Int) (s : State W32 Int) : (shSt μ s).vr = s.vr := rfl
@[simp] theorem shSt_flags (μ : Int) (s : State W32 Int) : (shSt μ s).flags = s.flags := rfl
@[simp] theorem shSt_pc (μ : Int) (s : State W32 Int) : (shSt μ s).pc = s.pc := rfl
@[simp] theorem shSt_halted (μ : Int) (s : State W32 Int) : (shSt μ s).halted = s.halted := rfl
@[simp] theorem shSt_tail (μ : Int) (s : State W32 Int) : (shSt μ s).tail = s.tail := rfl
@[simp] theorem shSt_err (μ : Int) (s : State W32 Int) : (shSt μ s).err = s.err := rfl
@[simp] theorem shSt_assume (μ : Int) (s : State W32 Int) : (shSt μ s).assume = s.assume := rfl

@[simp] theorem shCell_dat (μ : Int) (x : W32) (k : Nat) :
    shCell μ (.dat x k) = .dat x k := rfl

@[simp] theorem shCell_pb (μ : Int) (a : Addr Int) (k : Nat) :
    shCell μ (.pb a k) = .pb (shAddr μ a) k := rfl

@[simp] theorem shLog_nil (μ : Int) : shLog μ [] = [] := rfl

@[simp] theorem shLog_cons (μ : Int) (a : Addr Int) (c : Cell W32 Int)
    (l : List (Addr Int × Cell W32 Int)) :
    shLog μ ((a, c) :: l) = (shAddr μ a, shCell μ c) :: shLog μ l := rfl

@[simp] theorem shVal_ptr (μ : Int) (a : Addr Int) : shVal μ (.ptr a) = .ptr (shAddr μ a) := rfl
@[simp] theorem shVal_num (μ : Int) (l h : W32) : shVal μ (.num l h) = .num l h := rfl

/-- The shift of a stack address is the lowered address. -/
theorem shAddr_of_eq (μ : Int) (a : Addr Int) (h : a.region = rStack) :
    shAddr μ a = a.plusI μ := by
  rw [shAddr, ite_eq_left h]

/-- The shift fixes every address outside the stack region. -/
theorem shAddr_of_ne (μ : Int) (a : Addr Int) (h : a.region ≠ rStack) :
    shAddr μ a = a := by
  rw [shAddr, ite_eq_right h]

theorem shAddr_region (μ : Int) (a : Addr Int) : (shAddr μ a).region = a.region := by
  by_cases h : a.region = rStack
  · rw [shAddr_of_eq μ a h]
    obtain ⟨r, o⟩ := a
    rfl
  · rw [shAddr_of_ne μ a h]

/-- The shift commutes with adding a byte offset, so `lane`-sized walks of the log stay shifted
walks. -/
theorem shAddr_plusI (μ : Int) (a : Addr Int) (k : Int) :
    shAddr μ (a.plusI k) = (shAddr μ a).plusI k := by
  by_cases h : a.region = rStack
  · have h' : (a.plusI k).region = rStack := by
      obtain ⟨r, o⟩ := a
      exact h
    rw [shAddr_of_eq μ _ h', shAddr_of_eq μ a h]
    obtain ⟨r, o⟩ := a
    simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq]
    congr 1
    omega
  · have h' : (a.plusI k).region ≠ rStack := by
      obtain ⟨r, o⟩ := a
      exact h
    rw [shAddr_of_ne μ _ h', shAddr_of_ne μ a h]



theorem shAddr_same (μ : Int) (a b : Addr Int) :
    AddrEq.same (shAddr μ a) (shAddr μ b) = AddrEq.same a b := by
  obtain ⟨ra, oa⟩ := a
  obtain ⟨rb, ob⟩ := b
  by_cases ha : ra = rStack <;> by_cases hb : rb = rStack
  · rw [shAddr_of_eq μ _ ha, shAddr_of_eq μ _ hb]
    show some ((ra == rb) && (oa + μ == ob + μ)) = some ((ra == rb) && (oa == ob))
    rw [ha, hb]
    by_cases h : oa = ob
    · rw [h]; simp
    · have h2 : oa + μ ≠ ob + μ := by omega
      rw [show (oa + μ == ob + μ) = false from by simpa using (beq_eq_false_iff_ne.mpr h2),
          show (oa == ob) = false from by simpa using (beq_eq_false_iff_ne.mpr h)]
  · rw [shAddr_of_eq μ _ ha, shAddr_of_ne μ _ hb]
    show some ((ra == rb) && (oa + μ == ob)) = some ((ra == rb) && (oa == ob))
    have hr : (rStack == rb) = false := by rw [beq_eq_false_iff_ne]; exact fun h => hb h.symm
    have hr2 : (ra == rb) = false := by rw [beq_eq_false_iff_ne]; exact fun h => hb (h.symm.trans ha)
    rw [hr2]; rfl
  · rw [shAddr_of_ne μ _ ha, shAddr_of_eq μ _ hb]
    show some ((ra == rb) && (oa == ob + μ)) = some ((ra == rb) && (oa == ob))
    have hr : (ra == rStack) = false := by rw [beq_eq_false_iff_ne]; exact fun h => ha h
    have hr2 : (ra == rb) = false := by rw [beq_eq_false_iff_ne]; exact fun h => ha (h.trans hb)
    rw [hr2]; rfl
  · rw [shAddr_of_ne μ _ ha, shAddr_of_ne μ _ hb]

theorem lookup_sh (μ : Int) (a : Addr Int) (l : List (Addr Int × Cell W32 Int)) :
    lookup (shAddr μ a) (shLog μ l) = (lookup a l).map (Option.map (shCell μ)) := by
  induction l with
  | nil => rfl
  | cons bc l ih =>
    obtain ⟨b, c⟩ := bc
    simp only [shLog_cons, lookup, shAddr_same]
    cases h : AddrEq.same a b with
    | none => rfl
    | some v =>
      cases v with
      | true => rfl
      | false => simpa only [h] using ih

theorem readCell_sh (μ : Int) (mem0w mem0l : Addr Int → Cell W32 Int)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a)) (s : State W32 Int) (a : Addr Int) :
    readCell mem0w (shSt μ s) (shAddr μ a) = (readCell mem0l s a).map (shCell μ) := by
  simp only [readCell, shSt_mem, lookup_sh]
  cases h : lookup a s.mem with
  | error e => rfl
  | ok o =>
    cases o with
    | none => simp only [Except.map, Option.map, h0]
    | some c => rfl


/-! ## Map/bind plumbing for `Except` and `getD` -/

theorem emap_bind {ε α β δ : Type} (e : Except ε α) (f : α → β) (g : β → Except ε δ) :
    (e.map f >>= g) = (e >>= fun x => g (f x)) := by
  cases e <;> rfl

theorem ebind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

theorem emap_ok {ε α β : Type} (f : α → β) (a : α) :
    Except.map f (Except.ok a : Except ε α) = Except.ok (f a) := rfl

theorem ebind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = Except.error e := rfl

theorem emap_error {ε α β : Type} (f : α → β) (e : ε) :
    Except.map f (Except.error e : Except ε α) = Except.error e := rfl

theorem emap_throw {ε α β : Type} (f : α → β) (e : ε) :
    Except.map f (throw e : Except ε α) = throw e := rfl

theorem emap_pure {ε α β : Type} (f : α → β) (a : α) :
    Except.map f (pure a : Except ε α) = pure (f a) := rfl

theorem emap_bind_congr {ε α β : Type} (e : Except ε α) (f : α → α) (g g' : α → Except ε β)
    (h : ∀ x, g' (f x) = g x) : (e.map f >>= g') = (e >>= g) := by
  cases e with
  | error e => rfl
  | ok x => exact h x

theorem emap_bind_map {ε α β δ : Type} (e : Except ε α) (g : α → Except ε β) (f : β → δ) :
    ((e >>= g).map f) = (e >>= fun x => (g x).map f) := by
  cases e <;> rfl

theorem getD_map_shVal (μ : Int) (l : List (Val W32 Int)) (i : Nat) (d : Val W32 Int)
    (hd : shVal μ d = d) :
    (l.map (shVal μ)).getD i d = shVal μ (l.getD i d) := by
  induction l generalizing i with
  | nil => simp [List.getD, hd]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getG_sh (μ : Int) (s : State W32 Int) (i : Nat) :
    (shSt μ s).getG i = shVal μ (s.getG i) := by
  rw [State.getG, shSt_gpr, State.getG]
  exact getD_map_shVal μ s.gpr i _ rfl

theorem setG_sh (μ : Int) (s : State W32 Int) (i : Nat) (v : Val W32 Int) :
    (shSt μ s).setG i (shVal μ v) = shSt μ (s.setG i v) := by
  simp only [State.setG, shSt, List.map_set]

theorem getV_sh (μ : Int) (s : State W32 Int) (i : Nat) : (shSt μ s).getV i = s.getV i := rfl

theorem setV_sh (μ : Int) (s : State W32 Int) (i : Nat) (v : List W32) :
    (shSt μ s).setV i v = shSt μ (s.setV i v) := by
  simp only [State.setV, shSt]

theorem next_sh (μ : Int) (s : State W32 Int) : (shSt μ s).next = shSt μ s.next := by
  simp only [State.next, shSt]

theorem clearFlags_sh (μ : Int) (s : State W32 Int) :
    clearFlags (shSt μ s) = shSt μ (clearFlags s) := by
  simp only [clearFlags, shSt]

theorem setFlags_sh (μ : Int) (s : State W32 Int) (a b : Int) :
    setFlags (shSt μ s) a b = shSt μ (setFlags s a b) := by
  simp only [setFlags, shSt]

theorem setData32_sh (μ : Int) (s : State W32 Int) (d : Nat) (x : W32) :
    setData32 (shSt μ s) d x = shSt μ (setData32 s d x) := by
  have h := setG_sh μ s d (.num x (Lane.const 0))
  rw [shVal_num] at h
  simpa only [setData32] using h

theorem halt_sh (μ : Int) (s : State W32 Int) : halt (shSt μ s) = shSt μ (halt s) := by
  simp only [halt, shSt]

theorem fail_sh (μ : Int) (s : State W32 Int) (msg : String) :
    (shSt μ s).fail msg = shSt μ (s.fail msg) := by
  simp only [State.fail, shSt]
  by_cases h : s.err.isSome <;> simp [h]

theorem okOr_sh (μ : Int) (s : State W32 Int) (r r' : Except String (State W32 Int))
    (h : r' = r.map (shSt μ)) :
    okOr (shSt μ s) r' = shSt μ (okOr s r) := by
  rw [h]
  cases r with
  | error e => simp only [okOr, Except.map, fail_sh]
  | ok s' => rfl

theorem branch_sh (μ : Int) (orc : Nat → Bool) (s : State W32 Int) (c : Cond Int)
    (t : Nat) : (shSt μ s).branch orc c t = shSt μ (s.branch orc c t) := by
  simp only [State.branch, shSt_pc]
  cases hd : c.decideC with
  | none => simp only [hd, Option.isNone]; split <;> simp [State.next, shSt]
  | some b => simp only [hd, Option.isNone]; split <;> simp [State.next, shSt]

/-! ## Address arithmetic -/

theorem shAddr_plus (μ : Int) (a : Addr Int) (n : Int) :
    shAddr μ (a.plus n) = (shAddr μ a).plus n := by
  by_cases h : a.region = rStack
  · have h' : (a.plus n).region = rStack := by obtain ⟨r, o⟩ := a; exact h
    rw [shAddr_of_eq μ _ h', shAddr_of_eq μ a h]
    obtain ⟨r, o⟩ := a
    simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq]
    congr 1; omega
  · have h' : (a.plus n).region ≠ rStack := by obtain ⟨r, o⟩ := a; exact h
    rw [shAddr_of_ne μ _ h', shAddr_of_ne μ a h]

theorem regPtr_sh (μ : Int) (s : State W32 Int) (r : Nat) :
    regPtr (shSt μ s) r = (regPtr s r).map (shAddr μ) := by
  simp only [regPtr, getG_sh]
  cases h : s.getG r with
  | num lo hi => rfl
  | ptr a => rfl

theorem baseAddr_sh (μ : Int) (ro : Region) (hro : ro ≠ rStack) (s : State W32 Int)
    (m : MemRef) : baseAddr ro (shSt μ s) m = (baseAddr ro s m).map (shAddr μ) := by
  obtain ⟨base, index, scale, disp, ro'⟩ := m
  cases ro' with
  | none =>
    cases base with
    | none =>
      simp only [baseAddr, Except.map]
      rw [shAddr_of_ne μ _ (by decide : (rNum : Region) ≠ rStack)]
    | some b => exact regPtr_sh μ s b
  | some o =>
    simp only [baseAddr, Except.map]
    rw [shAddr_of_ne μ _ (show (⟨ro, Ctl.ofInt o⟩ : Addr Int).region ≠ rStack from hro)]

theorem effAddr_sh (μ : Int) (ro : Region) (hro : ro ≠ rStack) (s : State W32 Int)
    (m : MemRef) : effAddr ro (shSt μ s) m = (effAddr ro s m).map (shAddr μ) := by
  obtain ⟨base, index, scale, disp, ro'⟩ := m
  simp only [effAddr]
  rw [baseAddr_sh μ ro hro s ⟨base, index, scale, disp, ro'⟩]
  cases hb : baseAddr ro s ⟨base, index, scale, disp, ro'⟩ with
  | error e => rfl
  | ok b =>
    simp only [Except.map]
    rw [← shAddr_plusI]
    cases index with
    | none => rfl
    | some i =>
      dsimp only
      rw [getG_sh]
      cases hg : s.getG i with
      | num lo hi => rfl
      | ptr a =>
        obtain ⟨r, o⟩ := a
        cases r with
        | zero =>
          rw [shVal_ptr,
            shAddr_of_ne μ (⟨0, o⟩ : Addr Int) (by decide : (0 : Region) ≠ rStack)]
          simp only [shAddr_plusI, shAddr_plus]
        | succ k =>
          rw [shVal_ptr]
          by_cases hk : Nat.succ k = rStack
          · rw [show (⟨Nat.succ k, o⟩ : Addr Int) = ⟨rStack, o⟩ from by rw [hk]]
            rw [shAddr_of_eq μ (⟨rStack, o⟩ : Addr Int) rfl]
            rfl
          · rw [shAddr_of_ne μ (⟨Nat.succ k, o⟩ : Addr Int) hk]
            rfl

/-! ## Lane load/store commutation -/

theorem cellData_sh (μ : Int) (c : Cell W32 Int) : cellData (shCell μ c) = cellData c := by
  cases c with
  | dat x k => rfl
  | pb a k => rfl

theorem lanePat_sh (μ : Int) (c0 c1 c2 c3 : Cell W32 Int) :
    lanePat (shCell μ c0) (shCell μ c1) (shCell μ c2) (shCell μ c3)
      = lanePat c0 c1 c2 c3 := by
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> rfl

theorem loadLane_sh (μ : Int) (mem0w mem0l : Addr Int → Cell W32 Int)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a)) (s : State W32 Int) (a : Addr Int) :
    loadLane mem0w (shSt μ s) (shAddr μ a) = loadLane mem0l s a := by
  simp only [loadLane, ← shAddr_plusI, readCell_sh μ mem0w mem0l h0, emap_bind, lanePat_sh,
    cellData_sh]

theorem loadLanes_sh (μ : Int) (mem0w mem0l : Addr Int → Cell W32 Int)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a)) (s : State W32 Int) (a : Addr Int) :
    ∀ n, loadLanes mem0w (shSt μ s) (shAddr μ a) n = loadLanes mem0l s a n := by
  intro n
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [loadLanes, ← shAddr_plusI, loadLane_sh μ mem0w mem0l h0, ih (a.plusI 4)]

theorem storeLane_sh (μ : Int) (s : State W32 Int) (a : Addr Int) (x : W32) :
    storeLane (shSt μ s) (shAddr μ a) x = shSt μ (storeLane s a x) := by
  simp only [storeLane, shSt, shLog_cons, shCell_dat, shAddr_plusI]

theorem storeLanes_sh (μ : Int) (a : Addr Int) (xs : List W32) (s : State W32 Int) :
    storeLanes (shSt μ s) (shAddr μ a) xs = shSt μ (storeLanes s a xs) := by
  induction xs generalizing a s with
  | nil => rfl
  | cons x xs ih =>
    simp only [storeLanes, storeLane_sh, ← shAddr_plusI, ih (a.plusI 4) (storeLane s a x)]

theorem isPb_sh (μ : Int) (p : Addr Int) (k : Nat) (c : Cell W32 Int) :
    isPb (shAddr μ p) k (shCell μ c) = isPb p k c := by
  cases c with
  | dat x j => rfl
  | pb q j => simp only [isPb, shCell_pb, shAddr_same]

theorem pbRest_sh (μ : Int) (mem0w mem0l : Addr Int → Cell W32 Int)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a)) (s : State W32 Int)
    (p a : Addr Int) :
    ∀ n k, pbRest mem0w (shSt μ s) (shAddr μ p) (shAddr μ a) n k
      = pbRest mem0l s p a n k := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    simp only [pbRest, ← shAddr_plusI, readCell_sh μ mem0w mem0l h0]
    rw [emap_bind_congr (readCell mem0l s (a.plusI k)) (shCell μ)
      (fun c => if isPb p k c then pbRest mem0l s p a n (k + 1) else return false)
      (fun c => if isPb (shAddr μ p) k c then
        pbRest mem0w (shSt μ s) (shAddr μ p) (shAddr μ a) n (k + 1) else return false)
      (by intro c; simp only [isPb_sh, ih (k + 1)])]

theorem loadVal_sh (μ : Int) (mem0w mem0l : Addr Int → Cell W32 Int)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a)) (s : State W32 Int) (a : Addr Int) :
    loadVal mem0w (shSt μ s) (shAddr μ a) = (loadVal mem0l s a).map (shVal μ) := by
  simp only [loadVal, readCell_sh μ mem0w mem0l h0]
  cases hc : readCell mem0l s a with
  | error e => rfl
  | ok c0 =>
    cases c0 with
    | dat x k =>
      simp only [← shAddr_plusI, loadLane_sh μ mem0w mem0l h0]
      cases h1 : loadLane mem0l s a with
      | error e => rfl
      | ok lo =>
        cases h2 : loadLane mem0l s (a.plusI 4) with
        | error e => rfl
        | ok hi => rfl
    | pb q k =>
      cases k with
      | zero =>
        rw [emap_ok, ebind_ok]
        simp only [shCell_pb]
        rw [pbRest_sh μ mem0w mem0l h0]
        cases hb : pbRest mem0l s q a 7 1 with
        | error e =>
          simp only [emap_ok, emap_bind_map, ebind_ok]
          rw [hb]
          simp only [emap_error, ebind_error, ebind_ok, emap_bind_map, emap_ok]
        | ok b =>
          simp only [emap_ok, emap_bind_map, ebind_ok]
          rw [hb]
          cases b <;>
            simp only [ite_true, ite_false, Bool.false_eq_true, shVal_ptr, emap_pure,
              emap_throw, emap_error, ebind_error, ebind_ok, emap_bind_map, emap_ok]
      | succ k =>
        simp only [← shAddr_plusI, loadLane_sh μ mem0w mem0l h0]
        cases h1 : loadLane mem0l s a with
        | error e => rfl
        | ok lo =>
          cases h2 : loadLane mem0l s (a.plusI 4) with
          | error e => rfl
          | ok hi => rfl

theorem pbList_sh (μ : Int) (p a : Addr Int) :
    (List.range 8).reverse.map (fun i => ((shAddr μ a).plusI (Int.ofNat i),
        (Cell.pb (shAddr μ p) i : Cell W32 Int)))
      = List.map ((fun q : Addr Int × Cell W32 Int => (shAddr μ q.1, shCell μ q.2)) ∘
          fun i => (a.plusI (Int.ofNat i), (Cell.pb p i : Cell W32 Int)))
          (List.range 8).reverse := by
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, shCell_pb, shAddr_plusI]

theorem storeVal_sh (μ : Int) (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) :
    storeVal (shSt μ s) (shAddr μ a) (shVal μ v) = shSt μ (storeVal s a v) := by
  cases v with
  | num lo hi => simp only [shVal_num, storeVal, ← shAddr_plusI, storeLane_sh]
  | ptr p =>
    simp only [shVal_ptr, storeVal, shSt, shLog, List.map_append, List.map_map]
    rw [pbList_sh]

/-! ## Operand commutation -/

theorem gData32_sh (μ : Int) (ro : Region) (hro : ro ≠ rStack)
    (mem0w mem0l : Addr Int → Cell W32 Int)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a))
    (s : State W32 Int) (src : GSrc) :
    gData32 ro mem0w (shSt μ s) src = gData32 ro mem0l s src := by
  cases src with
  | reg i =>
    simp only [gData32, getG_sh]
    cases hg : s.getG i with
    | num lo hi => rfl
    | ptr a =>
      obtain ⟨r, o⟩ := a
      cases r with
      | zero =>
        rw [shVal_ptr,
          shAddr_of_ne μ (⟨0, o⟩ : Addr Int) (by decide : (0 : Region) ≠ rStack)]
        try rfl
      | succ k =>
        rw [shVal_ptr]
        by_cases hk : Nat.succ k = rStack
        · rw [show (⟨Nat.succ k, o⟩ : Addr Int) = ⟨rStack, o⟩ from by rw [hk],
            shAddr_of_eq μ (⟨rStack, o⟩ : Addr Int) rfl]
          try rfl
        · rw [shAddr_of_ne μ (⟨Nat.succ k, o⟩ : Addr Int) hk]
          try rfl
  | imm v => rfl
  | mem m =>
    simp only [gData32, effAddr_sh μ ro hro s m, emap_bind,
      loadLane_sh μ mem0w mem0l h0]

theorem gCtl_sh (μ : Int) (s : State W32 Int) (src : GSrc) :
    gCtl (shSt μ s) src = (gCtl s src).map (shAddr μ) := by
  cases src with
  | reg i =>
    simp only [gCtl, getG_sh]
    cases hg : s.getG i with
    | num lo hi =>
      cases h1 : Lane.asConst lo with
      | none => rfl
      | some l =>
        cases h2 : Lane.asConst hi with
        | none => rfl
        | some h => simp only [shVal_num, Except.map]; rfl
    | ptr a => rfl
  | imm v => simp only [gCtl, Except.map]; rfl
  | mem m => rfl

theorem readVSrc_sh (μ : Int) (ro : Region) (hro : ro ≠ rStack)
    (mem0w mem0l : Addr Int → Cell W32 Int)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a))
    (s : State W32 Int) (w : Nat) (src : VSrc) :
    readVSrc ro mem0w (shSt μ s) w src = readVSrc ro mem0l s w src := by
  cases src with
  | reg i => rfl
  | mem m =>
    simp only [readVSrc, effAddr_sh μ ro hro s m, emap_bind,
      loadLanes_sh μ mem0w mem0l h0]



end Hashtree.Asm.X86
