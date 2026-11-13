import Hashtree.Asm.X86

set_option linter.unusedSectionVars false

/-!
# Region renaming for the amd64 semantics

A chain gives every kernel its own rodata region, but the fixed-count kernel theorems are
stated with the table in region 4.  This module is the simulation layer that moves a run
between regions: an involutive bijection `ρ` of `Region` is lifted to addresses, register
values, memory cells, the register file, the write log and the memory function, and the
instruction semantics commutes with the lift.  `swap ro r` is the instance used by the
chain: it exchanges `ro` with a fresh region `r` and fixes every other region.

The lift is an involution and preserves the sentinel regions (`rNum` for numbers, `rRet` for
return addresses); those are the only region tests in `exec`.
-/

namespace Hashtree.Asm.X86Ren
open Hashtree.Asm Hashtree.Asm.X86

variable {α : Type}
variable [Lane α]

/-- `rNum` is definitionally `0`; named so `simp` can rewrite with it. -/
theorem rNum_zero : rNum = (0 : Region) := rfl
theorem rRet_zero : rRet = (5 : Region) := rfl

/-- An involutive renaming of regions: a bijection that is its own inverse. -/
structure RegionRenaming where
  f : Region → Region
  invol : ∀ x, f (f x) = x

namespace RegionRenaming

variable (ρ : RegionRenaming)

/-! ## Addresses, values, cells -/

def addr {γ : Type} (a : Addr γ) : Addr γ := ⟨ρ.f a.region, a.off⟩

@[simp] theorem addr_invol {γ : Type} (a : Addr γ) : ρ.addr (ρ.addr a) = a := by
  cases a; simp [addr, ρ.invol]

theorem addr_inj {γ : Type} {a b : Addr γ} : ρ.addr a = ρ.addr b ↔ a = b := by
  constructor
  · intro h
    have := congrArg ρ.addr h
    simpa using this
  · intro h; subst h; rfl

theorem f_inj {x y : Region} : ρ.f x = ρ.f y ↔ x = y := by
  constructor
  · intro h
    have := congrArg ρ.f h
    simpa [ρ.invol] using this
  · intro h; subst h; rfl

@[simp] theorem addr_plusI {γ : Type} [Ctl γ] [Inhabited γ] (a : Addr γ) (n : Int) :
    ρ.addr (a.plusI n) = (ρ.addr a).plusI n := rfl

@[simp] theorem addr_off {γ : Type} (a : Addr γ) : (ρ.addr a).off = a.off := rfl

@[simp] theorem addr_region {γ : Type} (a : Addr γ) : (ρ.addr a).region = ρ.f a.region := rfl

def val {γ : Type} : Val α γ → Val α γ
  | .num lo hi => .num lo hi
  | .ptr a => .ptr (ρ.addr a)

def cell {γ : Type} : Cell α γ → Cell α γ
  | .dat x k => .dat x k
  | .pb a k => .pb (ρ.addr a) k

@[simp] theorem val_invol {γ : Type} (v : Val α γ) : ρ.val (ρ.val v) = v := by
  cases v <;> simp [val]

@[simp] theorem cell_invol {γ : Type} (c : Cell α γ) : ρ.cell (ρ.cell c) = c := by
  cases c <;> simp [cell]

/-! ## States -/

def state {γ : Type} (s : State α γ) : State α γ :=
  { s with
    gpr := s.gpr.map ρ.val
    mem := s.mem.map fun p => (ρ.addr p.1, ρ.cell p.2) }

@[simp] theorem state_gpr {γ : Type} (s : State α γ) : (ρ.state s).gpr = s.gpr.map ρ.val := rfl
@[simp] theorem state_vr {γ : Type} (s : State α γ) : (ρ.state s).vr = s.vr := rfl
@[simp] theorem state_flags {γ : Type} (s : State α γ) : (ρ.state s).flags = s.flags := rfl
@[simp] theorem state_mem {γ : Type} (s : State α γ) :
    (ρ.state s).mem = s.mem.map fun p => (ρ.addr p.1, ρ.cell p.2) := rfl
@[simp] theorem state_pc {γ : Type} (s : State α γ) : (ρ.state s).pc = s.pc := rfl
@[simp] theorem state_halted {γ : Type} (s : State α γ) : (ρ.state s).halted = s.halted := rfl
@[simp] theorem state_tail {γ : Type} (s : State α γ) : (ρ.state s).tail = s.tail := rfl
@[simp] theorem state_err {γ : Type} (s : State α γ) : (ρ.state s).err = s.err := rfl
@[simp] theorem state_assume {γ : Type} (s : State α γ) : (ρ.state s).assume = s.assume := rfl

theorem state_invol {γ : Type} (s : State α γ) : ρ.state (ρ.state s) = s := by
  cases s with
  | mk gpr vr flags mem pc halted tail err assume =>
    have hg : List.map ρ.val (List.map ρ.val gpr) = gpr := by
      induction gpr with
      | nil => rfl
      | cons v vs ih => simp [ih]
    have hm : List.map (fun p : Addr γ × Cell α γ => (ρ.addr p.1, ρ.cell p.2))
        (List.map (fun p : Addr γ × Cell α γ => (ρ.addr p.1, ρ.cell p.2)) mem) = mem := by
      induction mem with
      | nil => rfl
      | cons p ps ih => obtain ⟨a, c⟩ := p; simp [ih]
    simp only [state, hg, hm]

/-! ## Memory function -/

def mem {γ : Type} (m : Addr γ → Cell α γ) : Addr γ → Cell α γ :=
  fun a => ρ.cell (m (ρ.addr a))

@[simp] theorem mem_at {γ : Type} (m : Addr γ → Cell α γ) (a : Addr γ) :
    ρ.mem m (ρ.addr a) = ρ.cell (m a) := by
  simp only [mem, addr_invol]

theorem mem_invol {γ : Type} (m : Addr γ → Cell α γ) : ρ.mem (ρ.mem m) = m := by
  funext a
  simp only [mem, addr_invol, cell_invol]

/-- Map the value of an `Except`: identity on errors. -/
def emap {β γ : Type} (f : β → γ) : Except String β → Except String γ
  | .ok b => .ok (f b)
  | .error e => .error e

@[simp] theorem emap_ok {β γ : Type} (f : β → γ) (b : β) : emap f (.ok b) = .ok (f b) := rfl
@[simp] theorem emap_error {β γ : Type} (f : β → γ) (e : String) : emap f (.error e) = .error e := rfl

/-- A `do let` whose source is `ok` reduces definitionally. -/
@[simp] theorem bind_ok_e {β γ : Type} (a : β) (f : β → Except String γ) :
    (do let c ← (Except.ok a : Except String β); f c) = f a := rfl

/-- A `do let` whose source is `error` propagates the error. -/
@[simp] theorem bind_error_e {β γ : Type} (e : String) (f : β → Except String γ) :
    (do let c ← (Except.error e : Except String β); f c) = Except.error e := rfl

@[simp] theorem emap_pure {β γ : Type} (f : β → γ) (x : β) :
    emap f (pure x : Except String β) = pure (f x) := rfl

@[simp] theorem emap_ite {β γ : Type} (f : β → γ) (b : Bool) (X Y : Except String β) :
    emap f (if b then X else Y) = if b then emap f X else emap f Y := by
  cases b <;> rfl

@[simp] theorem emap_throw {β γ : Type} (f : β → γ) (e : String) :
    emap f (throw e : Except String β) = throw e := rfl

/-- A propositional `if` pushes through `emap`. -/
theorem emap_dite {β γ : Type} (f : β → γ) (c : Prop) [Decidable c]
    (X Y : Except String β) :
    emap f (if c then X else Y) = if c then emap f X else emap f Y := by
  by_cases h : c <;> simp [h]

/-- `Ctl.asInt` on `Int` is `some`. -/
theorem ctlAsInt_int (x : Int) : (Ctl.asInt x : Option Int) = some x := rfl

theorem map_eq_bind {β γ : Type} (f : β → γ) (X : Except String β) :
    (f <$> X) = (do let x ← X; pure (f x)) := by cases X <;> rfl

theorem emap_map {β γ δ : Type} (f : β → γ) (g : δ → β) (X : Except String δ) :
    emap f (g <$> X) = (fun x => f (g x)) <$> X := by
  cases X <;> rfl

/-- `emap` pushes through a bind: the bound value is mapped where it is consumed. -/
theorem emap_bind {β γ δ : Type} (f : β → γ) (X : Except String δ) (g : δ → Except String β) :
    emap f (X >>= g) = X >>= fun x => emap f (g x) := by
  cases X <;> rfl

/-- `emap` of a producer: its bound value is renamed before it is consumed. -/
theorem bind_emap {β γ δ : Type} (f : β → γ) (X : Except String β) (g : γ → Except String δ) :
    (emap f X >>= g) = X >>= fun x => g (f x) := by
  cases X <;> rfl

/-! ## `AddrEq`, `lookup`, `readCell` -/

/-- Region renaming preserves address comparison. -/
theorem same_ren (a b : Addr Int) :
    AddrEq.same (ρ.addr a) (ρ.addr b) = AddrEq.same a b := by
  have hb : (ρ.f a.region == ρ.f b.region) = (a.region == b.region) := by
    by_cases h : (a.region = b.region)
    · rw [h]; simp
    · have h' : ρ.f a.region ≠ ρ.f b.region := fun hh => h (ρ.f_inj.mp hh)
      have hb1 : (a.region == b.region) = false := by
        cases hh : (a.region == b.region) with
        | false => rfl
        | true => exact absurd (by simpa using hh) h
      have hb2 : (ρ.f a.region == ρ.f b.region) = false := by
        cases hh : (ρ.f a.region == ρ.f b.region) with
        | false => rfl
        | true => exact absurd (by simpa using hh) h'
      rw [hb1, hb2]
  change some ((ρ.f a.region == ρ.f b.region) && (a.off == b.off)) =
    some ((a.region == b.region) && (a.off == b.off))
  rw [hb]

theorem lookup_ren (a : Addr Int) (l : List (Addr Int × Cell α Int)) :
    lookup (ρ.addr a) (l.map fun p => (ρ.addr p.1, ρ.cell p.2)) =
      match lookup a l with
      | .ok none => .ok none
      | .ok (some c) => .ok (some (ρ.cell c))
      | .error e => .error e := by
  induction l with
  | nil => simp [lookup]
  | cons p rest ih =>
    obtain ⟨b, c⟩ := p
    simp only [List.map_cons]
    cases h : AddrEq.same a b with
    | none => simp [lookup, h, same_ren]
    | some v =>
      cases v
      · simpa [lookup, h, same_ren] using ih
      · simp [lookup, h, same_ren]

theorem readCell_ren (m : Addr Int → Cell α Int) (s : State α Int) (a : Addr Int) :
    readCell (ρ.mem m) (ρ.state s) (ρ.addr a) =
      match readCell m s a with
      | .ok c => .ok (ρ.cell c)
      | .error e => .error e := by
  unfold readCell
  simp only [state_mem]
  rw [lookup_ren]
  cases h : lookup a s.mem with
  | error e => rfl
  | ok o =>
    cases o with
    | none => simp [h]
    | some c => rfl

/-! ## Lanes, values, stores -/

@[simp] theorem cellData_ren (c : Cell α Int) : cellData (ρ.cell c) = cellData c := by
  cases c <;> rfl

theorem lanePat_ren (c0 c1 c2 c3 : Cell α Int) :
    lanePat (ρ.cell c0) (ρ.cell c1) (ρ.cell c2) (ρ.cell c3) =
      lanePat c0 c1 c2 c3 := by
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> rfl

theorem loadLane_ren (m : Addr Int → Cell α Int) (s : State α Int) (a : Addr Int) :
    loadLane (ρ.mem m) (ρ.state s) (ρ.addr a) = loadLane m s a := by
  unfold loadLane
  simp only [readCell_ren, ← addr_plusI]
  cases h0 : readCell m s a with
  | error e => rfl
  | ok c0 =>
    cases h1 : readCell m s (a.plusI 1) with
    | error e => rfl
    | ok c1 =>
      cases h2 : readCell m s (a.plusI 2) with
      | error e => rfl
      | ok c2 =>
        cases h3 : readCell m s (a.plusI 3) with
        | error e => rfl
        | ok c3 =>
          simp [emap_ok, lanePat_ren]

theorem loadLanes_ren (m : Addr Int → Cell α Int) (s : State α Int) :
    ∀ (n : Nat) (a : Addr Int),
      loadLanes (ρ.mem m) (ρ.state s) (ρ.addr a) n = loadLanes m s a n
  | 0, a => rfl
  | n + 1, a => by
      simp only [loadLanes, loadLane_ren, ← addr_plusI,
        loadLanes_ren m s n (a.plusI 4)]

theorem isPb_ren (p : Addr Int) (k : Nat) (c : Cell α Int) :
    isPb (ρ.addr p) k (ρ.cell c) = isPb p k c := by
  cases c <;> simp [isPb, same_ren, RegionRenaming.cell]

theorem pbRest_ren (m : Addr Int → Cell α Int) (s : State α Int)
    (p a : Addr Int) :
    ∀ (n k : Nat),
      pbRest (ρ.mem m) (ρ.state s) (ρ.addr p) (ρ.addr a) n k =
        pbRest m s p a n k
  | 0, _ => rfl
  | n + 1, k => by
      simp only [pbRest, readCell_ren, ← addr_plusI, isPb_ren]
      cases h : readCell m s (a.plusI k) with
      | error e => rfl
      | ok c =>
        simp [h, emap_ok, isPb_ren, pbRest_ren m s p a n (k + 1)]

theorem loadVal_ren (m : Addr Int → Cell α Int) (s : State α Int) (a : Addr Int) :
    loadVal (ρ.mem m) (ρ.state s) (ρ.addr a) = emap ρ.val (loadVal m s a) := by
  unfold loadVal
  simp only [readCell_ren, ← addr_plusI]
  cases h : readCell m s a with
  | error e => rfl
  | ok c =>
    cases c with
    | dat x k =>
      simp [h, emap_ok, emap_bind, emap_map, loadLane_ren, ← addr_plusI,
        RegionRenaming.cell, RegionRenaming.val]
    | pb p k =>
      cases k with
      | zero =>
        simp [h, emap_ok, emap_pure, emap_ite, emap_throw, emap_bind, pbRest_ren,
          RegionRenaming.cell, RegionRenaming.val]
      | succ k =>
        simp [h, emap_ok, emap_bind, emap_map, loadLane_ren, ← addr_plusI,
          RegionRenaming.cell, RegionRenaming.val]

theorem storeLane_ren (s : State α Int) (a : Addr Int) (x : α) :
    ρ.state (storeLane s a x) = storeLane (ρ.state s) (ρ.addr a) x := by
  simp [storeLane, RegionRenaming.state, RegionRenaming.cell, addr_plusI]

theorem storeLanes_ren (s : State α Int) :
    ∀ (xs : List α) (a : Addr Int),
      ρ.state (storeLanes s a xs) = storeLanes (ρ.state s) (ρ.addr a) xs
  | [], a => rfl
  | x :: xs, a => by
      simp only [storeLanes, storeLane_ren, ← addr_plusI,
        storeLanes_ren (storeLane s a x) xs (a.plusI 4)]

theorem storeVal_ren (s : State α Int) (a : Addr Int) (v : Val α Int) :
    ρ.state (storeVal s a v) = storeVal (ρ.state s) (ρ.addr a) (ρ.val v) := by
  cases v with
  | num lo hi =>
    simp [storeVal, storeLane_ren, RegionRenaming.val, ← addr_plusI]
  | ptr p =>
    simp [storeVal, RegionRenaming.state, RegionRenaming.val, RegionRenaming.cell,
      addr_plusI, Function.comp_def]

/-! ## Registers and operands -/

theorem getD_map {β γ : Type} (f : β → γ) (l : List β) (i : Nat) (d : β) :
    (l.map f).getD i (f d) = f (l.getD i d) := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

theorem set_map {β γ : Type} (f : β → γ) (l : List β) (i : Nat) (a : β) :
    (l.map f).set i (f a) = (l.set i a).map f := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

theorem getG_ren (s : State α Int) (i : Nat) :
    (ρ.state s).getG i = ρ.val (s.getG i) := by
  unfold State.getG
  simp only [RegionRenaming.state]
  exact getD_map ρ.val s.gpr i (.num (Lane.const 0) (Lane.const 0))

theorem setG_ren (s : State α Int) (i : Nat) (v : Val α Int) :
    ρ.state (s.setG i v) = (ρ.state s).setG i (ρ.val v) := by
  unfold State.setG
  simp only [RegionRenaming.state, set_map]

theorem getV_ren (s : State α Int) (i : Nat) : (ρ.state s).getV i = s.getV i := rfl

theorem setV_ren (s : State α Int) (i : Nat) (v : List α) :
    ρ.state (s.setV i v) = (ρ.state s).setV i v := by
  unfold State.setV
  simp only [RegionRenaming.state]

theorem setVec_ren (s : State α Int) (vex : Bool) (w d : Nat) (v : List α) :
    ρ.state (setVec s vex w d v) = setVec (ρ.state s) vex w d v := by
  simp [setVec, State.setV, State.getV, RegionRenaming.state]

theorem setData32_ren (s : State α Int) (d : Nat) (x : α) :
    ρ.state (setData32 s d x) = setData32 (ρ.state s) d x := by
  simp [setData32, setG_ren, RegionRenaming.val]

theorem clearFlags_ren (s : State α Int) :
    ρ.state (clearFlags s) = clearFlags (ρ.state s) := rfl

theorem setFlags_ren (s : State α Int) (a b : Int) :
    ρ.state (setFlags s a b) = setFlags (ρ.state s) a b := rfl

theorem halt_ren (s : State α Int) : ρ.state (halt s) = halt (ρ.state s) := rfl

theorem next_ren (s : State α Int) : ρ.state (s.next) = (ρ.state s).next := rfl

theorem state_ite {γ : Type} (c : Prop) [Decidable c] (a b : State α γ) :
    ρ.state (if c then a else b) = if c then ρ.state a else ρ.state b := by
  by_cases h : c <;> simp [h]

theorem state_set3 (s : State α Int) (pc : Nat) (h : Bool) (n : Option String) :
    ρ.state { s with pc := pc, halted := h, tail := n } =
      { ρ.state s with pc := pc, halted := h, tail := n } := rfl

theorem fail_ren (s : State α Int) (msg : String) :
    ρ.state (s.fail msg) = (ρ.state s).fail msg := by
  unfold State.fail
  cases h : s.err.isSome <;> simp [h, RegionRenaming.state]

theorem branch_ren (s : State α Int) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    ρ.state (s.branch orc c t) = (ρ.state s).branch orc c t := by
  unfold State.branch
  cases h : c.decideC with
  | none => cases hb : orc s.pc <;> simp [h, hb, State.next, RegionRenaming.state]
  | some b => cases b <;> cases hb : orc s.pc <;>
      simp [h, hb, State.next, RegionRenaming.state]


theorem branch_pc_ren (s : State α Int) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    (State.branch orc (ρ.state s) c t).pc = (State.branch orc s c t).pc := by
  rw [← branch_ren ρ s orc c t]
  exact state_pc ρ (State.branch orc s c t)

/-! ## Effective addresses and operands -/

theorem regPtr_ren (s : State α Int) (r : Nat) :
    regPtr (ρ.state s) r = emap ρ.addr (regPtr s r) := by
  unfold regPtr
  rw [getG_ren]
  cases s.getG r <;> rfl

theorem baseAddr_ren (h0 : ρ.f rNum = rNum) (ro : Region) (s : State α Int)
    (m : MemRef) :
    baseAddr (ρ.f ro) (ρ.state s) m = emap ρ.addr (baseAddr ro s m) := by
  unfold baseAddr
  cases m.ro with
  | none =>
    cases m.base with
    | none => simp [h0, RegionRenaming.addr]
    | some b => simp [regPtr_ren]
  | some o => rfl

theorem effAddr_ren (h0 : ρ.f rNum = rNum) (ro : Region) (s : State α Int)
    (m : MemRef) :
    effAddr (ρ.f ro) (ρ.state s) m = emap ρ.addr (effAddr ro s m) := by
  unfold effAddr
  rw [baseAddr_ren ρ h0]
  cases baseAddr ro s m with
  | error e => rfl
  | ok b =>
    simp only [emap_ok, bind_emap]
    cases h : m.index with
    | none => simp [h, addr_plusI]
    | some i =>
      simp only [h]
      rw [getG_ren]
      cases s.getG i with
      | num lo hi => rfl
      | ptr a =>
        cases a with
        | mk r off =>
          by_cases ha : (r = rNum)
          · subst ha
            simp only [RegionRenaming.val, RegionRenaming.addr]
            rw [h0, show rNum = (0 : Region) from rfl]
            rfl
          · have hane : ρ.f r ≠ rNum := fun hh => ha (ρ.f_inj.mp (hh.trans h0.symm))
            simp [RegionRenaming.val, RegionRenaming.addr,
              show ¬ r = 0 from ha, show ρ.f r ≠ 0 from hane]

theorem gData32_ren (h0 : ρ.f rNum = rNum) (ro : Region) (m : Addr Int → Cell α Int)
    (s : State α Int) (src : GSrc) :
    gData32 (ρ.f ro) (ρ.mem m) (ρ.state s) src = gData32 ro m s src := by
  cases src with
  | reg i =>
    simp only [gData32]
    rw [getG_ren]
    cases h : s.getG i with
    | num lo hi => rfl
    | ptr a =>
      cases a with
      | mk r off =>
        by_cases ha : (r = rNum)
        · subst ha; simp [RegionRenaming.val, RegionRenaming.addr, h0]
        · have hane : ρ.f r ≠ rNum := fun hh => ha (ρ.f_inj.mp (hh.trans h0.symm))
          simp [RegionRenaming.val, RegionRenaming.addr,
            show ¬ r = 0 from ha, show ρ.f r ≠ 0 from hane]
  | imm v => rfl
  | mem mref =>
    simp only [gData32]
    rw [effAddr_ren ρ h0]
    simp [bind_emap, loadLane_ren ρ]

theorem gCtl_ren (h0 : ρ.f rNum = rNum) (s : State α Int) (src : GSrc) :
    gCtl (ρ.state s) src = emap ρ.addr (gCtl s src) := by
  cases src with
  | reg i =>
    simp only [gCtl]
    rw [getG_ren]
    cases h : s.getG i with
    | ptr a => rfl
    | num lo hi =>
      simp only [RegionRenaming.val]
      split <;> simp [RegionRenaming.addr, h0]
  | imm v => simp [gCtl, RegionRenaming.addr, h0]
  | mem m => simp [gCtl]

theorem readVSrc_ren (h0 : ρ.f rNum = rNum) (ro : Region) (m : Addr Int → Cell α Int)
    (s : State α Int) (w : Nat) (src : VSrc) :
    readVSrc (ρ.f ro) (ρ.mem m) (ρ.state s) w src = readVSrc ro m s w src := by
  cases src with
  | reg i => rfl
  | mem mref =>
    simp only [readVSrc]
    rw [effAddr_ren ρ h0]
    simp [bind_emap, loadLanes_ren ρ]

end RegionRenaming

/-! ## The swap used by the tail-call chain -/

/-- Exchange `ro` with `r`, fixing every other region. -/
def swapF (ro r x : Region) : Region :=
  if x = ro then r else if x = r then ro else x

theorem swapF_invol (ro r x : Region) : swapF ro r (swapF ro r x) = x := by
  unfold swapF
  by_cases h1 : x = ro <;> by_cases h2 : x = r <;> simp_all

def swap (ro r : Region) : RegionRenaming where
  f := swapF ro r
  invol := swapF_invol ro r

@[simp] theorem swap_ro (ro r : Region) : (swap ro r).f ro = r := by
  simp [swap, swapF]

@[simp] theorem swap_r (ro r : Region) : (swap ro r).f r = ro := by
  by_cases h : ro = r <;> simp [swap, swapF, h]

theorem swap_fixes (ro r x : Region) (h1 : x ≠ ro) (h2 : x ≠ r) :
    (swap ro r).f x = x := by
  simp [swap, swapF, h1, h2]

theorem swap_rNum (ro r : Region) (h1 : ro ≠ rNum) (h2 : r ≠ rNum) :
    (swap ro r).f rNum = rNum := swap_fixes ro r rNum (Ne.symm h1) (Ne.symm h2)

theorem swap_rRet (ro r : Region) (h1 : ro ≠ rRet) (h2 : r ≠ rRet) :
    (swap ro r).f rRet = rRet := swap_fixes ro r rRet (Ne.symm h1) (Ne.symm h2)


/-! ## Region sentinels and `okOr` -/

namespace RegionRenaming

variable (ρ : RegionRenaming)

/-- The renaming preserves the number sentinel `rNum`. -/
theorem f_eq_rNum (h0 : ρ.f rNum = rNum) (r : Region) :
    (ρ.f r = rNum ↔ r = rNum) := by
  constructor
  · intro hh
    have h2 : ρ.f (ρ.f r) = rNum := by rw [hh, h0]
    simpa [ρ.invol] using h2
  · intro hh; rw [hh]; exact h0

/-- The renaming preserves the return-address sentinel `rRet`. -/
theorem f_eq_rRet (h5 : ρ.f rRet = rRet) (r : Region) :
    (ρ.f r = rRet ↔ r = rRet) := by
  constructor
  · intro hh
    have h2 : ρ.f (ρ.f r) = rRet := by rw [hh, h5]
    simpa [ρ.invol] using h2
  · intro hh; rw [hh]; exact h5

/-- `ρ.state` pushes through `okOr`. -/
theorem state_okOr (s : State α Int) (X : Except String (State α Int)) :
    ρ.state (okOr s X) = okOr (ρ.state s) (emap ρ.state X) := by
  unfold okOr
  cases X with
  | ok s' => rfl
  | error e => exact fail_ren ρ s e

/-! ## `exec` commutes with the renaming -/

/-- One instruction: running the renamed program on the renamed state is the renamed
result of running the original instruction.  Only the two sentinel regions (`rNum` for
numbers, `rRet` for return addresses) are inspected by the semantics, so those are the
only regions the renaming has to fix. -/
theorem exec_ren (h0 : ρ.f rNum = rNum) (h5 : ρ.f rRet = rRet)
    (ro : Region) (m : Addr Int → Cell α Int) (orc : Nat → Bool) (i : Instr)
    (s : State α Int) :
    exec (ρ.f ro) (ρ.mem m) orc i (ρ.state s) = ρ.state (exec ro m orc i s) := by
  cases hh : s.halted
  · cases i with
    | nop =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      exact (next_ren ρ s).symm
    | vop op vex w d s1 s2 =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_bind, map_eq_bind, readVSrc_ren ρ h0, emap_pure, getV_ren,
          setVec_ren, next_ren] <;> rfl)
    | vshift k vex w d src n =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | vshiftq vex w d src n =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | vror w d src n =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | vtern w d s1 s2 imm =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | vload vex w d src =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_bind, map_eq_bind, readVSrc_ren ρ h0, emap_pure, setVec_ren,
          next_ren] <;> rfl)
    | vstore w mref src =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_bind, map_eq_bind, bind_emap, effAddr_ren ρ h0, emap_pure,
          getV_ren, storeLanes_ren, next_ren] <;> rfl)
    | pshufd vex d src imm =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | pshufb vex w d src mask =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_bind, map_eq_bind, emap_pure, getV_ren, setVec_ren, next_ren]
          <;> rfl)
    | palignr vex d s1 s2 imm =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | pblendw d src imm =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | shufps w d s1 s2 imm =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | perm2f128 d s1 s2 imm =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | inserti128 d s1 mref imm =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_bind, map_eq_bind, bind_emap, effAddr_ren ρ h0, loadLanes_ren ρ,
          emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | inserti64x4 d s1 mref imm =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_bind, map_eq_bind, bind_emap, effAddr_ren ρ h0, loadLanes_ren ρ,
          emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | permi2d d s1 s2 =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_bind, emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | permi2q d s1 s2 =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_bind, emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | sha256rnds2 d src =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | sha256msg1 d src =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | sha256msg2 d src =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr] <;> (try congr 1) <;>
        try (simp only [emap_pure, getV_ren, setVec_ren, next_ren] <;> rfl)
    | mov w d src =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      by_cases hw : (w = 64)
      · simp only [if_pos hw]
        cases src with
        | reg r =>
          simp only [emap_pure, getG_ren, setG_ren, next_ren] <;> rfl
        | imm v =>
          simp only [emap_pure, setG_ren, RegionRenaming.val, RegionRenaming.addr, h0,
            next_ren] <;> rfl
        | mem mref =>
          simp only [emap_bind, map_eq_bind, bind_emap, effAddr_ren ρ h0, loadVal_ren ρ,
            emap_pure, setG_ren, next_ren] <;> rfl
      · simp only [if_neg hw]
        simp only [emap_bind, map_eq_bind, bind_emap, gData32_ren ρ h0, emap_pure,
          setData32_ren, next_ren] <;> rfl
    | movst w mref src =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      cases hsrc : s.getG src with
      | num lo hi =>
        by_cases hw : (w = 64)
        · simp only [if_pos hw, hsrc, getG_ren, emap_bind, map_eq_bind, bind_emap,
            effAddr_ren ρ h0, emap_pure, storeVal_ren, RegionRenaming.val, next_ren] <;> rfl
        · simp only [if_neg hw, hsrc, getG_ren, RegionRenaming.val, emap_bind, map_eq_bind,
            bind_emap, effAddr_ren ρ h0, emap_pure, storeLane_ren, next_ren] <;> rfl
      | ptr a =>
        by_cases hw : (w = 64)
        · simp only [if_pos hw, hsrc, getG_ren, emap_bind, map_eq_bind, bind_emap,
            effAddr_ren ρ h0, emap_pure, storeVal_ren, RegionRenaming.val, RegionRenaming.addr,
            next_ren] <;> rfl
        · simp only [if_neg hw, hsrc, getG_ren, RegionRenaming.val, RegionRenaming.addr,
            emap_bind, map_eq_bind, bind_emap, effAddr_ren ρ h0, emap_throw]
    | alu op w d src =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      by_cases hw : (w = 64)
      · simp only [if_pos hw]
        by_cases hxor : (op = .xor ∧ src = .reg d)
        · simp only [emap_ok, emap_error, bind_ok_e, if_pos hxor, emap_pure, setG_ren, clearFlags_ren, RegionRenaming.val,
            RegionRenaming.addr, h0, next_ren] <;> rfl
        · simp only [if_neg hxor, gCtl_ren ρ h0]
          cases h1 : gCtl s (.reg d) with
          | error e =>
            simp only [h1, bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite,
              emap_throw]
          | ok a =>
            cases h2 : gCtl s src with
            | error e =>
              simp only [h1, h2, bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite,
                emap_throw]
            | ok b =>
              cases op with
              | add =>
                by_cases hc : (b.region = rNum ∨ a.region = rNum)
                · by_cases hb0 : (b.region = rNum)
                  · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, if_pos hc, if_pos hb0, setFlags_ren, setG_ren, clearFlags_ren, RegionRenaming.val, RegionRenaming.addr, next_ren] <;> rfl
                  · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, if_pos hc, if_neg hb0, setFlags_ren, setG_ren, clearFlags_ren, RegionRenaming.val, RegionRenaming.addr, next_ren] <;> rfl
                · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, if_neg hc, setFlags_ren, setG_ren, clearFlags_ren, RegionRenaming.val, RegionRenaming.addr, next_ren] <;> rfl
              | and =>
                have hAa : (ρ.addr a).off = a.off := rfl
                have hAb : (ρ.addr b).off = b.off := rfl
                simp only [ctlAsInt_int, hAa, hAb]
                cases hA : andInt a.off b.off with
                | none => simp only [hA, map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, hAa, hAb] <;> rfl
                | some r =>
                  by_cases hc : (b.region = rNum ∧ (a.region = rNum ∨ (-64 ≤ b.off ∧ b.off < 0)))
                  · simp only [hA, map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, hAa, hAb, f_eq_rNum ρ h0, if_pos hc, setG_ren, clearFlags_ren, RegionRenaming.val, RegionRenaming.addr, next_ren] <;> rfl
                  · simp only [hA, map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, hAa, hAb, f_eq_rNum ρ h0, if_neg hc, setG_ren, clearFlags_ren, RegionRenaming.val, RegionRenaming.addr, next_ren] <;> rfl
              | xor =>
                simp only [bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite,
                  emap_throw]
              | or =>
                simp only [bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite,
                  emap_throw]
      · simp only [if_neg hw]
        by_cases hxor : (op = .xor ∧ src = .reg d)
        · simp only [emap_ok, emap_error, bind_ok_e, if_pos hxor, emap_pure, setData32_ren, clearFlags_ren, next_ren] <;> rfl
        · simp only [emap_ok, emap_error, bind_ok_e, if_neg hxor, emap_bind, map_eq_bind, bind_emap, gData32_ren ρ h0,
            emap_pure, setData32_ren, clearFlags_ren, next_ren] <;> rfl
    | sub w d src =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      by_cases hw : (w = 64)
      · simp only [if_pos hw, gCtl_ren ρ h0]
        cases h1 : gCtl s (.reg d) with
        | error e =>
          simp only [h1, bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite, emap_throw]
        | ok a =>
          cases h2 : gCtl s src with
          | error e =>
            simp only [h1, h2, bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite, emap_throw]
          | ok b =>
            by_cases hc : (b.region = rNum)
            · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, if_pos hc, emap_dite, emap_pure, emap_throw, setFlags_ren, setG_ren, RegionRenaming.val, addr_region, addr_off, next_ren] <;> rfl
            · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, if_neg hc, emap_dite, emap_pure, emap_throw, addr_region, addr_off] <;> rfl
      · simp only [if_neg hw, emap_throw]
    | lea d mref =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      simp only [emap_bind, map_eq_bind, bind_emap, effAddr_ren ρ h0, emap_pure, setG_ren,
        RegionRenaming.val, next_ren] <;> rfl
    | ror w d n =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      by_cases hw : (w = 32)
      · simp only [if_pos hw, emap_bind, map_eq_bind, bind_emap, gData32_ren ρ h0, emap_pure,
          setData32_ren, clearFlags_ren, next_ren] <;> rfl
      · simp only [if_neg hw, emap_throw]
    | shld w d src n =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      by_cases hw : (w = 32)
      · simp only [if_pos hw, emap_bind, map_eq_bind, bind_emap, gData32_ren ρ h0, emap_pure,
          setData32_ren, clearFlags_ren, next_ren] <;> rfl
      · simp only [if_neg hw, emap_throw]
    | shl w d n =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      by_cases hw : (w = 64)
      · simp only [if_pos hw, gCtl_ren ρ h0]
        cases h1 : gCtl s (.reg d) with
        | error e =>
          simp only [h1, bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite, emap_throw]
        | ok a =>
          by_cases hc : (a.region = rNum)
          · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, if_pos hc, emap_dite, emap_pure, emap_throw, setG_ren, clearFlags_ren, RegionRenaming.val, RegionRenaming.addr, h0, addr_region, addr_off, next_ren] <;> rfl
          · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, if_neg hc, emap_dite, emap_pure, emap_throw, addr_region, addr_off] <;> rfl
      · simp only [if_neg hw, emap_bind, map_eq_bind, bind_emap, gData32_ren ρ h0, emap_pure,
          setData32_ren, clearFlags_ren, next_ren] <;> rfl
    | bswap w d =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      by_cases hw : (w = 32)
      · simp only [if_pos hw, emap_bind, map_eq_bind, bind_emap, gData32_ren ρ h0, emap_pure,
          setData32_ren, next_ren] <;> rfl
      · simp only [if_neg hw, emap_throw]
    | push r =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      cases h : s.getG rsp with
      | num lo hi =>
        simp only [h, getG_ren, RegionRenaming.val, emap_throw]
      | ptr sp =>
        simp only [h, getG_ren, RegionRenaming.val, emap_bind,
          map_eq_bind, bind_emap, emap_pure, storeVal_ren, setG_ren, addr_plusI, next_ren] <;> rfl
    | pop r =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      cases h : s.getG rsp with
      | num lo hi =>
        simp only [h, getG_ren, RegionRenaming.val, emap_throw]
      | ptr sp =>
        simp only [h, getG_ren, RegionRenaming.val, emap_bind,
          map_eq_bind, bind_emap, loadVal_ren ρ, emap_pure, getG_ren, setG_ren, addr_plusI,
          next_ren] <;> rfl
    | cmp w a b =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      by_cases hw : (w = 64)
      · simp only [if_pos hw, gCtl_ren ρ h0]
        cases h1 : gCtl s (.reg a) with
        | error e =>
          simp only [h1, bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite, emap_throw]
        | ok x =>
          cases h2 : gCtl s b with
          | error e =>
            simp only [h1, h2, bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite, emap_throw]
          | ok y =>
            by_cases hc : (y.region = rNum ∨ y.region = x.region)
            · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, f_inj ρ, if_pos hc, emap_dite, emap_pure, emap_throw, setFlags_ren, addr_region, next_ren] <;> rfl
            · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, f_inj ρ, if_neg hc, emap_dite, emap_pure, emap_throw, addr_region, addr_off] <;> rfl
      · simp only [if_neg hw, emap_throw]
    | test w a b =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      by_cases hw : (w = 64 ∧ a = b)
      · simp only [if_pos hw, gCtl_ren ρ h0]
        cases h1 : gCtl s (.reg a) with
        | error e =>
          simp only [h1, bind_ok_e, emap_ok, emap_error, emap_bind, bind_error_e, emap_dite, emap_throw]
        | ok x =>
          by_cases hc : (x.region = rNum)
          · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, if_pos hc, emap_dite, emap_pure, emap_throw, setFlags_ren, addr_region, next_ren] <;> rfl
          · simp only [map_eq_bind, emap_bind, bind_ok_e, bind_error_e, emap_pure, emap_throw, emap_ok, emap_error, emap_dite, f_eq_rNum ρ h0, if_neg hc, emap_dite, emap_pure, emap_throw, addr_region, addr_off] <;> rfl
      · simp only [if_neg hw, emap_throw]
    | jcc c t =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      simp only [RegionRenaming.state_flags]
      cases hf : s.flags with
      | none => simp [hf, emap_throw]
      | some ab =>
        obtain ⟨a, b⟩ := ab
        simp only [hf, emap_pure, branch_ren, next_ren] <;> rfl
    | jmp t =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      simp only [RegionRenaming.state]
    | jccTail c name =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      simp only [RegionRenaming.state_flags]
      cases hf : s.flags with
      | none => simp [hf, emap_throw]
      | some ab =>
        obtain ⟨a, b⟩ := ab
        dsimp only
        simp only [hf, map_eq_bind, emap_bind, emap_dite, emap_pure]
        by_cases hp : (State.branch orc s (ccCond c a b) 1000000000).pc = 1000000000
        · have hp' : (State.branch orc (ρ.state s) (ccCond c a b) 1000000000).pc = 1000000000 := by
            rw [branch_pc_ren ρ s orc (ccCond c a b) 1000000000]; exact hp
          simp only [hp, hp', if_pos hp, if_pos hp', state_set3, branch_ren, state_pc]
        · have hp' : ¬ ((State.branch orc (ρ.state s) (ccCond c a b) 1000000000).pc = 1000000000) := by
            rw [branch_pc_ren ρ s orc (ccCond c a b) 1000000000]; exact hp
          simp only [hp, hp', if_neg hp, if_neg hp', state_set3, branch_ren, state_pc]
    | jmpTail name =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      simp only [RegionRenaming.state]
    | ret =>
      simp only [exec, hh, RegionRenaming.state_halted, Bool.false_eq_true, ite_false]
      rw [state_okOr]
      try congr 1
      simp only [map_eq_bind, emap_bind, getG_ren]
      cases h : s.getG rsp with
      | num lo hi =>
        simp only [h, RegionRenaming.val, emap_throw]
      | ptr sp =>
        simp only [h, RegionRenaming.val]
        cases hlv : loadVal m s sp with
        | error e =>
          simp only [loadVal_ren ρ, hlv, bind_error_e, emap_error, emap_throw]
        | ok v =>
          cases v with
          | num lo hi =>
            simp only [loadVal_ren ρ, hlv, RegionRenaming.val, emap_ok, emap_bind,
              map_eq_bind, bind_ok_e, bind_error_e, emap_error, emap_throw]
          | ptr a =>
            cases a with
            | mk r o =>
              simp only [loadVal_ren ρ, hlv, RegionRenaming.val, bind_ok_e, emap_ok]
              by_cases hr : (r = rRet)
              · subst hr
                have hf5 : ρ.f rRet = rRet := (f_eq_rRet ρ h5 rRet).mpr rfl
                have hlit : (⟨rRet, o⟩ : Addr Int) = ⟨(5 : Region), o⟩ := rfl
                simp only [RegionRenaming.addr, hf5, hlit, emap_pure, halt_ren, setG_ren,
                  RegionRenaming.val, addr_plusI, next_ren]
                rfl
              · have hf5 : ¬ (ρ.f r = 5) := fun hh => hr ((f_eq_rRet ρ h5 r).mp hh)
                simp only [RegionRenaming.addr]
                split
                · rename_i hh
                  injection hh with h1
                  injection h1 with hreg _
                  exact absurd hreg hf5
                · split
                  · rename_i hh
                    injection hh with h1
                    injection h1 with hreg _
                    exact absurd hreg hr
                  · simp only [emap_throw]

  · simp [exec, hh, RegionRenaming.state_halted]

/-- Running a program commutes with the renaming, provided the two sentinel regions are
fixed.  The program itself is unchanged: region tests in the semantics only compare against
`rNum` and `rRet`, and the rodata base is passed as the `ro` argument. -/
theorem run_ren (h0 : ρ.f rNum = rNum) (h5 : ρ.f rRet = rRet)
    (prog : Array Instr) (ro : Region) (m : Addr Int → Cell α Int) (orc : Nat → Bool) :
    ∀ (n : Nat) (s : State α Int),
      run prog (ρ.f ro) (ρ.mem m) orc n (ρ.state s) = ρ.state (run prog ro m orc n s) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [run, state_ite]
    split
    · rename_i h
      have hs : s.halted = true := h
      simp only [if_pos hs]
    · rename_i h
      have hs : ¬ (s.halted = true) := fun hh => h hh
      simp only [if_neg hs, RegionRenaming.state_pc]
      cases hp : prog[s.pc]? with
      | none =>
        simp only [hp]
        exact (fail_ren ρ s "pc out of program").symm
      | some i =>
        simp only [hp]
        rw [exec_ren ρ h0 h5 ro m orc i s]
        exact ih (exec ro m orc i s)

end RegionRenaming

/-! ## The chain instance

The fixed-count kernel theorems are proved with the rodata table in region 4.  A chain gives
each link a fresh region `r`; `swap 4 r` moves the table between the two.  These corollaries
are the form step 3 uses: the run at the link's own region is the renamed region-4 run. -/

/-- Run a program at a fresh rodata region `r`, with the memory handed to it moved by the
swap.  This is the region-4 run renamed by `swap 4 r` (the program image is unchanged). -/
theorem run_swap (r : Region) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet)
    (prog : Array Instr) (m : Addr Int → Cell α Int) (orc : Nat → Bool) (n : Nat)
    (s : State α Int) :
    run prog r ((swap 4 r).mem m) orc n ((swap 4 r).state s)
      = (swap 4 r).state (run prog 4 m orc n s) := by
  have h0 : (swap 4 r).f rNum = rNum :=
    swap_rNum 4 r (by rw [rNum_zero]; decide) hrNum
  have h5 : (swap 4 r).f rRet = rRet :=
    swap_rRet 4 r (by rw [rRet_zero]; decide) hrRet
  have h := RegionRenaming.run_ren (swap 4 r) h0 h5 prog 4 m orc n s
  simpa only [swap_ro] using h

/-- Same, with the memory the chain actually holds on the left: `m` is the unswapped
(region-4) memory, so the run sees `(swap 4 r).mem ((swap 4 r).mem m) = m`. -/
theorem run_swap_chain (r : Region) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet)
    (prog : Array Instr) (m : Addr Int → Cell α Int) (orc : Nat → Bool) (n : Nat)
    (s : State α Int) :
    run prog r m orc n ((swap 4 r).state s)
      = (swap 4 r).state (run prog 4 ((swap 4 r).mem m) orc n s) := by
  have h := run_swap (α := α) r hrNum hrRet prog ((swap 4 r).mem m) orc n s
  rwa [RegionRenaming.mem_invol] at h

end Hashtree.Asm.X86Ren
