import Hashtree.Asm.Core
import Std.Tactic.BVDecide

/-!
# Soundness of the symbolic machine: evaluation is a homomorphism

The symbolic instances (`E`, `Lin`) and the concrete ones (`BitVec 32`, `Int`) run the same
functions.  Evaluating a symbolic value with an environment (`env` for lane variables, `σ` for
the symbols of control values) commutes with every operation; this file proves it for the lane
and control operations and the memory model.  `X86Hom.lean` etc. lift it to instructions.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Hashtree.Asm

/-! ## Lanes -/

section Lanes
variable (env : Key → W32)

@[simp] theorem eval_const (v : W32) : (Lane.const v : E).eval env = v := rfl

@[simp] theorem eval_add (a b : E) : (Lane.add a b : E).eval env = a.eval env + b.eval env := by
  cases a <;> cases b <;> rfl
@[simp] theorem eval_xor (a b : E) : (Lane.xor a b : E).eval env = a.eval env ^^^ b.eval env := by
  cases a <;> cases b <;> rfl
@[simp] theorem eval_and (a b : E) : (Lane.and a b : E).eval env = a.eval env &&& b.eval env := by
  cases a <;> cases b <;> rfl
@[simp] theorem eval_or (a b : E) : (Lane.or a b : E).eval env = a.eval env ||| b.eval env := by
  cases a <;> cases b <;> rfl
@[simp] theorem eval_not (a : E) : (Lane.not a : E).eval env = ~~~ a.eval env := by
  cases a <;> rfl
@[simp] theorem eval_shl (a : E) (n : Nat) : (Lane.shl a n : E).eval env = a.eval env <<< n := by
  cases a <;> rfl
@[simp] theorem eval_shr (a : E) (n : Nat) : (Lane.shr a n : E).eval env = a.eval env >>> n := by
  cases a <;> rfl
@[simp] theorem eval_sar (a : E) (n : Nat) : (Lane.sar a n : E).eval env = (a.eval env).sshiftRight n := by
  cases a <;> rfl
@[simp] theorem eval_ror (a : E) (n : Nat) : (Lane.ror a n : E).eval env = (a.eval env).rotateRight n := by
  cases a <;> rfl
@[simp] theorem eval_tern (i : Nat) (a b c : E) :
    (Lane.tern i a b c : E).eval env = ternW i (a.eval env) (b.eval env) (c.eval env) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem eval_asConst (a : E) (v : W32) (h : (Lane.asConst a : Option W32) = some v) : a.eval env = v := by
  cases a <;> simp_all [Lane.asConst, E.eval]

theorem eval_same (a b : E) (h : (Lane.same a b) = true) : a.eval env = b.eval env := by
  simp only [Lane.same, decide_eq_true_eq] at h; rw [h]

/-- The concrete lane operations, named (for rewriting `Lane.op` on `W32`). -/
@[simp] theorem W32_const (v : W32) : (Lane.const v : W32) = v := rfl
@[simp] theorem W32_add (a b : W32) : (Lane.add a b : W32) = a + b := rfl
@[simp] theorem W32_xor (a b : W32) : (Lane.xor a b : W32) = a ^^^ b := rfl
@[simp] theorem W32_and (a b : W32) : (Lane.and a b : W32) = a &&& b := rfl
@[simp] theorem W32_or (a b : W32) : (Lane.or a b : W32) = a ||| b := rfl
@[simp] theorem W32_not (a : W32) : (Lane.not a : W32) = ~~~ a := rfl
@[simp] theorem W32_shl (a : W32) (n : Nat) : (Lane.shl a n : W32) = a <<< n := rfl
@[simp] theorem W32_shr (a : W32) (n : Nat) : (Lane.shr a n : W32) = a >>> n := rfl
@[simp] theorem W32_sar (a : W32) (n : Nat) : (Lane.sar a n : W32) = a.sshiftRight n := rfl
@[simp] theorem W32_ror (a : W32) (n : Nat) : (Lane.ror a n : W32) = a.rotateRight n := rfl
@[simp] theorem W32_tern (i : Nat) (a b c : W32) : (Lane.tern i a b c : W32) = ternW i a b c := rfl
@[simp] theorem W32_asConst (a : W32) : (Lane.asConst a : Option W32) = some a := rfl
@[simp] theorem W32_same (a b : W32) : (Lane.same a b : Bool) = false := rfl

theorem eval_byteOf (x : E) (k : Nat) : (byteOf x k).eval env = byteOf (x.eval env) k := by
  simp [byteOf]

end Lanes

/-! ## Control values -/

theorem dotC_addC (σ : Nat → Int) : ∀ (a b : List Int) (i : Nat),
    dotC (addC a b) i σ = dotC a i σ + dotC b i σ
  | [], b, i => by simp [addC, dotC]
  | x :: xs, [], i => by simp [addC, dotC]
  | x :: xs, y :: ys, i => by
    simp only [addC, dotC, dotC_addC σ xs ys (i + 1)]; rw [Int.add_mul]; omega

theorem dotC_map_mul (σ : Nat → Int) (n : Int) : ∀ (a : List Int) (i : Nat),
    dotC (a.map (n * ·)) i σ = n * dotC a i σ
  | [], i => by simp [dotC]
  | x :: xs, i => by
    simp only [List.map, dotC, dotC_map_mul σ n xs (i + 1)]; rw [Int.mul_add, Int.mul_assoc]

theorem dotC_zero (σ : Nat → Int) : ∀ (a : List Int) (i : Nat), a.all (· == 0) = true → dotC a i σ = 0
  | [], _, _ => rfl
  | x :: xs, i, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [dotC, h.1, Int.zero_mul, Int.zero_add]
    exact dotC_zero σ xs (i + 1) (by simpa using h.2)

section Ctl
variable (σ : Nat → Int)

@[simp] theorem Lin.eval_ofInt (k : Int) : (Ctl.ofInt k : Lin).eval σ = k := by
  simp [Ctl.ofInt, Lin.ofInt, Lin.eval, dotC]
@[simp] theorem Lin.eval_add (a b : Lin) : (Ctl.add a b : Lin).eval σ = a.eval σ + b.eval σ := by
  simp only [Ctl.add, Lin.add, Lin.eval, dotC_addC]; omega
@[simp] theorem Lin.eval_smul (n : Int) (a : Lin) : (Ctl.smul n a : Lin).eval σ = n * a.eval σ := by
  simp only [Ctl.smul, Lin.smul, Lin.eval, dotC_map_mul]; rw [Int.mul_add]

theorem Lin.eval_asInt (a : Lin) (k : Int) (h : (Ctl.asInt a : Option Int) = some k) : a.eval σ = k := by
  simp only [Ctl.asInt, Lin.asInt] at h
  split at h
  · cases h; simp only [Lin.eval]; rw [dotC_zero σ a.c 0 (by assumption)]; omega
  · cases h

@[simp] theorem Int_ofInt (k : Int) : (Ctl.ofInt k : Int) = k := rfl
@[simp] theorem Int_add (a b : Int) : (Ctl.add a b : Int) = a + b := rfl
@[simp] theorem Int_smul (n a : Int) : (Ctl.smul n a : Int) = n * a := rfl
@[simp] theorem Int_asInt (a : Int) : (Ctl.asInt a : Option Int) = some a := rfl

theorem Lin.eval_sub (a b : Lin) : (Ctl.sub a b : Lin).eval σ = a.eval σ - b.eval σ := by
  simp only [Ctl.sub, Lin.eval_add, Lin.eval_smul]; omega

end Ctl

/-! ## Evaluation maps on values, cells, addresses, conditions, states -/

section Maps
variable (env : Key → W32) (σ : Nat → Int)

def mapAddr (a : Addr Lin) : Addr Int := ⟨a.region, a.off.eval σ⟩

def mapVal : Val E Lin → Val W32 Int
  | .num lo hi => .num (lo.eval env) (hi.eval env)
  | .ptr a => .ptr (mapAddr σ a)

def mapCell : Cell E Lin → Cell W32 Int
  | .dat x k => .dat (x.eval env) k
  | .pb a k => .pb (mapAddr σ a) k

def mapCond : Cond Lin → Cond Int
  | .eq a b => .eq (a.eval σ) (b.eval σ)
  | .lt a b => .lt (a.eval σ) (b.eval σ)
  | .le a b => .le (a.eval σ) (b.eval σ)
  | .not c => .not (mapCond c)
  | .tt => .tt

/-- The concrete state a symbolic state denotes (the recorded assumptions are dropped: concrete
runs never record any). -/
def mapState (s : State E Lin) : State W32 Int where
  gpr := s.gpr.map (mapVal env σ)
  vr := s.vr.map (·.map (E.eval env))
  flags := s.flags.map (fun p => (p.1.eval σ, p.2.eval σ))
  mem := s.mem.map (fun p => (mapAddr σ p.1, mapCell env σ p.2))
  pc := s.pc
  halted := s.halted
  tail := s.tail
  err := s.err
  assume := []

/-- The recorded branch conditions hold. -/
def AssumeOk (s : State E Lin) : Prop :=
  ∀ p ∈ s.assume, (mapCond σ p.1).decideC = some p.2

/-- The symbolic initial memory denotes the concrete one, except at poison cells (pointer bytes
with index ≥ 8): no successful load reads one, so the concrete memory there is unconstrained. -/
def Mem0Rel (mem0s : Addr Lin → Cell E Lin) (mem0c : Addr Int → Cell W32 Int) : Prop :=
  ∀ a, Cell.okC (mem0s a) → mem0c (mapAddr σ a) = mapCell env σ (mem0s a)

end Maps

/-! ## Addresses and lookups -/

theorem okC_dat {α γ : Type} (x : α) (k : Nat) : Cell.okC (Cell.dat x k : Cell α γ) := trivial

theorem okC_of_cellData {α γ : Type} [Lane α] (c : Cell α γ) (b : α) (h : cellData c = .ok b) : Cell.okC c := by
  cases c with
  | dat _ _ => trivial
  | pb _ _ => simp [cellData] at h

theorem okC_of_lanePat {α γ : Type} (c0 c1 c2 c3 : Cell α γ) (q : α × α × α × α) (h : lanePat c0 c1 c2 c3 = some q) :
    Cell.okC c0 ∧ Cell.okC c1 ∧ Cell.okC c2 ∧ Cell.okC c3 := by
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> simp_all [lanePat, Cell.okC]

theorem mapAddr_plus (σ : Nat → Int) (a : Addr Lin) (n : Lin) :
    mapAddr σ (a.plus n) = (mapAddr σ a).plus (n.eval σ) := by
  simp [mapAddr, Addr.plus]

theorem mapAddr_plusI (σ : Nat → Int) (a : Addr Lin) (n : Int) :
    mapAddr σ (a.plusI n) = (mapAddr σ a).plusI n := by
  simp [mapAddr, Addr.plusI, Addr.plus]

theorem Lin.eval_lsub (σ : Nat → Int) (a b : Lin) : (a.sub b).eval σ = a.eval σ - b.eval σ := by
  have := Lin.eval_sub σ a b
  exact this

theorem Lin.eval_lasInt (σ : Nat → Int) (a : Lin) (k : Int) (h : a.asInt = some k) : a.eval σ = k :=
  Lin.eval_asInt σ a k h

theorem addrEq_hom (σ : Nat → Int) (a b : Addr Lin) (t : Bool) (h : AddrEq.same a b = some t) :
    AddrEq.same (mapAddr σ a) (mapAddr σ b) = some t := by
  simp only [AddrEq.same, mapAddr] at h ⊢
  by_cases hr : a.region = b.region
  · simp only [hr, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
    simp only [hr, beq_self_eq_true, Bool.true_and, Option.some.injEq]
    generalize hk : (a.off.sub b.off).asInt = o at h
    have hev := fun k (hk' : o = some k) => Lin.eval_lasInt σ _ k (hk.trans hk')
    rw [Lin.eval_lsub] at hev
    match o, h with
    | some 0, h => cases h; have := hev 0 rfl; simp; omega
    | some (k + 1 : Nat), h => cases h; have := hev _ rfl; simp; omega
    | some (Int.negSucc k), h => cases h; have := hev _ rfl; simp; omega
  · have : (a.region != b.region) = true := by simpa using hr
    simp only [this, ite_true, Option.some.injEq] at h
    subst h
    simp [hr]

theorem lookup_hom (env : Key → W32) (σ : Nat → Int) (a : Addr Lin) :
    ∀ (log : List (Addr Lin × Cell E Lin)) (r : Option (Cell E Lin)), lookup a log = .ok r →
      lookup (mapAddr σ a) (log.map (fun p => (mapAddr σ p.1, mapCell env σ p.2))) = .ok (r.map (mapCell env σ))
  | [], r, h => by simp [lookup] at h ⊢; exact h.symm ▸ rfl
  | (b, c) :: rest, r, h => by
    simp only [lookup] at h
    simp only [List.map, lookup]
    split at h
    · rename_i hab; cases h; rw [addrEq_hom σ a b true hab]; rfl
    · rename_i hab; rw [addrEq_hom σ a b false hab]; exact lookup_hom env σ a rest r h
    · cases h

/-! ## Memory -/

section Mem
variable (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin) (mem0c : Addr Int → Cell W32 Int)

theorem readCell_hom (h0 : Mem0Rel env σ mem0s mem0c) (s : State E Lin) (a : Addr Lin) (c : Cell E Lin)
    (h : readCell mem0s s a = .ok c) (hc : Cell.okC c) :
    readCell mem0c (mapState env σ s) (mapAddr σ a) = .ok (mapCell env σ c) := by
  simp only [readCell] at h ⊢
  cases hl : lookup a s.mem with
  | error e => rw [hl] at h; cases h
  | ok r =>
    rw [hl] at h
    have := lookup_hom env σ a s.mem r hl
    simp only [mapState]
    rw [this]
    cases r with
    | some c' => simp only [Except.ok.injEq] at h; subst h; rfl
    | none => simp only [Except.ok.injEq] at h; subst h; simp only [Option.map, h0 a hc]

/-- Four bytes of one value reassemble to it. -/
theorem bytes_reassemble (x : W32) :
    (((x >>> 0) &&& 0xff) ||| ((x >>> 8) &&& 0xff) <<< 8) ||| ((((x >>> 16) &&& 0xff) <<< 16) |||
      (((x >>> 24) &&& 0xff) <<< 24)) = x := by bv_decide

theorem cellData_hom (c : Cell E Lin) (x : E) (h : cellData c = .ok x) :
    cellData (mapCell env σ c) = .ok (x.eval env) := by
  cases c with
  | dat y k => simp only [cellData, Except.ok.injEq] at h; subst h; simp [mapCell, cellData, eval_byteOf]
  | pb _ _ => simp [cellData] at h

theorem lanePat_hom (c0 c1 c2 c3 : Cell E Lin) :
    lanePat (mapCell env σ c0) (mapCell env σ c1) (mapCell env σ c2) (mapCell env σ c3) =
      (lanePat c0 c1 c2 c3).map (fun q => (q.1.eval env, q.2.1.eval env, q.2.2.1.eval env, q.2.2.2.eval env)) := by
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> simp only [mapCell, lanePat] <;> (try split) <;> rfl

theorem ok_bind {ε β δ : Type} (x : β) (f : β → Except ε δ) : (Except.ok x >>= f) = f x := rfl

theorem loadLane_hom (h0 : Mem0Rel env σ mem0s mem0c) (s : State E Lin) (a : Addr Lin) (x : E)
    (h : loadLane mem0s s a = .ok x) : loadLane mem0c (mapState env σ s) (mapAddr σ a) = .ok (x.eval env) := by
  unfold loadLane at h ⊢
  cases r0 : readCell mem0s s a with
  | error e => rw [r0] at h; cases h
  | ok c0 =>
  cases r1 : readCell mem0s s (a.plusI 1) with
  | error e => rw [r0, ok_bind, r1] at h; cases h
  | ok c1 =>
  cases r2 : readCell mem0s s (a.plusI 2) with
  | error e => rw [r0, ok_bind, r1, ok_bind, r2] at h; cases h
  | ok c2 =>
  cases r3 : readCell mem0s s (a.plusI 3) with
  | error e => rw [r0, ok_bind, r1, ok_bind, r2, ok_bind, r3] at h; cases h
  | ok c3 =>
  rw [r0, ok_bind, r1, ok_bind, r2, ok_bind, r3, ok_bind] at h
  cases hp : lanePat c0 c1 c2 c3 with
  | some q =>
    obtain ⟨k0, k1, k2, k3⟩ := okC_of_lanePat c0 c1 c2 c3 q hp
    rw [readCell_hom env σ mem0s mem0c h0 s a c0 r0 k0, ok_bind,
      ← mapAddr_plusI, readCell_hom env σ mem0s mem0c h0 s _ c1 r1 k1, ok_bind,
      ← mapAddr_plusI, readCell_hom env σ mem0s mem0c h0 s _ c2 r2 k2, ok_bind,
      ← mapAddr_plusI, readCell_hom env σ mem0s mem0c h0 s _ c3 r3 k3, ok_bind, lanePat_hom, hp]
    obtain ⟨x0, y0, z0, w0⟩ := q
    rw [hp] at h
    dsimp only at h
    simp only [Option.map]
    simp only [W32_same, Bool.false_and, Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq]
    by_cases hs : (Lane.same x0 y0 && Lane.same x0 z0 && Lane.same x0 w0) = true
    · rw [if_pos hs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hs
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      rw [← eval_same env _ _ h1, ← eval_same env _ _ h2, ← eval_same env _ _ h3]
      simp only [byteOf, W32_and, W32_shr, W32_shl, W32_or, W32_const]
      generalize E.eval env x0 = v
      bv_decide
    · rw [if_neg hs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [eval_byteOf]
  | none =>
    rw [hp] at h
    dsimp only at h
    cases d0 : cellData c0 with
    | error e => rw [d0] at h; cases h
    | ok b0 =>
    cases d1 : cellData c1 with
    | error e => rw [d0, ok_bind, d1] at h; cases h
    | ok b1 =>
    cases d2 : cellData c2 with
    | error e => rw [d0, ok_bind, d1, ok_bind, d2] at h; cases h
    | ok b2 =>
    cases d3 : cellData c3 with
    | error e => rw [d0, ok_bind, d1, ok_bind, d2, ok_bind, d3] at h; cases h
    | ok b3 =>
    rw [readCell_hom env σ mem0s mem0c h0 s a c0 r0 (okC_of_cellData c0 b0 d0), ok_bind,
      ← mapAddr_plusI, readCell_hom env σ mem0s mem0c h0 s _ c1 r1 (okC_of_cellData c1 b1 d1), ok_bind,
      ← mapAddr_plusI, readCell_hom env σ mem0s mem0c h0 s _ c2 r2 (okC_of_cellData c2 b2 d2), ok_bind,
      ← mapAddr_plusI, readCell_hom env σ mem0s mem0c h0 s _ c3 r3 (okC_of_cellData c3 b3 d3), ok_bind, lanePat_hom]
    rw [hp]
    rw [d0, ok_bind, d1, ok_bind, d2, ok_bind, d3, ok_bind] at h
    cases h
    simp only [Option.map]
    rw [cellData_hom env σ c0 b0 d0, ok_bind, cellData_hom env σ c1 b1 d1, ok_bind,
      cellData_hom env σ c2 b2 d2, ok_bind, cellData_hom env σ c3 b3 d3, ok_bind]
    simp [pure, Except.pure]

theorem loadLanes_hom (h0 : Mem0Rel env σ mem0s mem0c) (s : State E Lin) :
    ∀ (n : Nat) (a : Addr Lin) (xs : List E), loadLanes mem0s s a n = .ok xs →
      loadLanes mem0c (mapState env σ s) (mapAddr σ a) n = .ok (xs.map (E.eval env))
  | 0, a, xs, h => by simp only [loadLanes, pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; rfl
  | n + 1, a, xs, h => by
    simp only [loadLanes] at h ⊢
    cases r : loadLane mem0s s a with
    | error e => rw [r] at h; cases h
    | ok x =>
    rw [r, ok_bind] at h
    cases r' : loadLanes mem0s s (a.plusI 4) n with
    | error e => rw [r'] at h; cases h
    | ok ys =>
    rw [r', ok_bind] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [loadLane_hom env σ mem0s mem0c h0 s a x r, ok_bind, ← mapAddr_plusI,
      loadLanes_hom h0 s n _ ys r', ok_bind]
    rfl

theorem isPb_hom (p : Addr Lin) (k : Nat) (c : Cell E Lin) (h : isPb p k c = true) :
    isPb (mapAddr σ p) k (mapCell env σ c) = true := by
  cases c with
  | dat _ _ => simp [isPb] at h
  | pb q j =>
    simp only [isPb, mapCell] at h ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [addrEq_hom σ p q true h.1]
    simp [h.2]

theorem okC_of_isPb {α γ : Type} [AddrEq γ] (p : Addr γ) (k : Nat) (c : Cell α γ) (hk : k < 8) (h : isPb p k c = true) :
    Cell.okC c := by
  cases c with
  | dat _ _ => trivial
  | pb q j => simp only [isPb, Bool.and_eq_true, beq_iff_eq] at h; simp only [Cell.okC]; omega

theorem pbRest_hom (h0 : Mem0Rel env σ mem0s mem0c) (s : State E Lin) (p a : Addr Lin) :
    ∀ (n k : Nat), n + k ≤ 8 → pbRest mem0s s p a n k = .ok true →
      pbRest mem0c (mapState env σ s) (mapAddr σ p) (mapAddr σ a) n k = .ok true
  | 0, k, _, _ => rfl
  | n + 1, k, hnk, h => by
    simp only [pbRest] at h ⊢
    cases r : readCell mem0s s (a.plusI k) with
    | error e => rw [r] at h; cases h
    | ok c =>
    rw [r, ok_bind] at h
    by_cases hc : isPb p k c = true
    · rw [← mapAddr_plusI, readCell_hom env σ mem0s mem0c h0 s _ c r (okC_of_isPb p k c (by omega) hc), ok_bind]
      rw [if_pos hc] at h
      rw [if_pos (isPb_hom env σ p k c hc)]
      exact pbRest_hom h0 s p a n (k + 1) (by omega) h
    · rw [if_neg hc] at h; simp [pure, Except.pure] at h

theorem loadVal_hom (h0 : Mem0Rel env σ mem0s mem0c) (s : State E Lin) (a : Addr Lin) (v : Val E Lin)
    (h : loadVal mem0s s a = .ok v) : loadVal mem0c (mapState env σ s) (mapAddr σ a) = .ok (mapVal env σ v) := by
  unfold loadVal at h ⊢
  cases r : readCell mem0s s a with
  | error e => rw [r] at h; cases h
  | ok c0 =>
  rw [r, ok_bind] at h
  cases c0 with
  | pb p k =>
    cases k with
    | zero =>
      rw [readCell_hom env σ mem0s mem0c h0 s a _ r (by simp [Cell.okC]), ok_bind]
      simp only [mapCell] at h ⊢
      cases rp : pbRest mem0s s p a 7 1 with
      | error e => rw [rp] at h; cases h
      | ok b =>
      rw [rp, ok_bind] at h
      cases b with
      | false => simp [throw, throwThe, MonadExceptOf.throw] at h
      | true =>
        simp only [ite_true, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rw [pbRest_hom env σ mem0s mem0c h0 s p a 7 1 (by omega) rp, ok_bind]
        rfl
    | succ k =>
      cases rl : loadLane mem0s s a with
      | error e => rw [rl] at h; cases h
      | ok lo =>
      exfalso
      unfold loadLane at rl
      rw [r, ok_bind] at rl
      cases r1 : readCell mem0s s (a.plusI 1) with
      | error e => rw [r1] at rl; cases rl
      | ok c1 =>
      rw [r1, ok_bind] at rl
      cases r2 : readCell mem0s s (a.plusI 2) with
      | error e => rw [r2] at rl; cases rl
      | ok c2 =>
      rw [r2, ok_bind] at rl
      cases r3 : readCell mem0s s (a.plusI 3) with
      | error e => rw [r3] at rl; cases rl
      | ok c3 =>
      rw [r3, ok_bind] at rl
      have hp : lanePat (Cell.pb p (k + 1)) c1 c2 c3 = none := by
        cases c1 <;> cases c2 <;> cases c3 <;> rfl
      rw [hp] at rl
      simp [cellData, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at rl
  | dat x k =>
    rw [readCell_hom env σ mem0s mem0c h0 s a _ r trivial, ok_bind]
    simp only [mapCell] at h ⊢
    cases rl : loadLane mem0s s a with
    | error e => rw [rl] at h; cases h
    | ok lo =>
    rw [rl, ok_bind] at h
    cases rh : loadLane mem0s s (a.plusI 4) with
    | error e => rw [rh] at h; cases h
    | ok hi =>
    rw [rh, ok_bind] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [loadLane_hom env σ mem0s mem0c h0 s a lo rl, ok_bind, ← mapAddr_plusI,
      loadLane_hom env σ mem0s mem0c h0 s _ hi rh, ok_bind]
    rfl

end Mem

/-! ## State updates commute with the map -/

section St
variable (env : Key → W32) (σ : Nat → Int)

theorem storeLane_hom (s : State E Lin) (a : Addr Lin) (x : E) :
    mapState env σ (storeLane s a x) = storeLane (mapState env σ s) (mapAddr σ a) (x.eval env) := by
  simp [storeLane, mapState, mapCell, mapAddr_plusI]

theorem storeLanes_hom : ∀ (xs : List E) (s : State E Lin) (a : Addr Lin),
    mapState env σ (storeLanes s a xs) = storeLanes (mapState env σ s) (mapAddr σ a) (xs.map (E.eval env))
  | [], s, a => rfl
  | x :: xs, s, a => by
    simp only [storeLanes, List.map]
    rw [storeLanes_hom xs, storeLane_hom, mapAddr_plusI]

theorem storeVal_hom (s : State E Lin) (a : Addr Lin) (v : Val E Lin) :
    mapState env σ (storeVal s a v) = storeVal (mapState env σ s) (mapAddr σ a) (mapVal env σ v) := by
  cases v with
  | num lo hi => simp only [storeVal, mapVal]; rw [storeLane_hom, storeLane_hom, mapAddr_plusI]
  | ptr p =>
    simp only [storeVal, mapVal, mapState, List.map_append, List.map_map]
    congr 1
    simp [mapCell, mapAddr_plusI, Function.comp_def]

theorem setG_hom (s : State E Lin) (i : Nat) (v : Val E Lin) :
    mapState env σ (s.setG i v) = (mapState env σ s).setG i (mapVal env σ v) := by
  simp [State.setG, mapState, List.map_set]

theorem setV_hom (s : State E Lin) (i : Nat) (v : List E) :
    mapState env σ (s.setV i v) = (mapState env σ s).setV i (v.map (E.eval env)) := by
  simp [State.setV, mapState, List.map_set]

theorem next_hom (s : State E Lin) : mapState env σ s.next = (mapState env σ s).next := rfl

theorem getG_hom (s : State E Lin) (i : Nat) :
    (mapState env σ s).getG i = mapVal env σ (s.getG i) := by
  simp only [State.getG, mapState, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases s.gpr[i]? <;> rfl

theorem getV_hom (s : State E Lin) (i : Nat) :
    (mapState env σ s).getV i = (s.getV i).map (E.eval env) := by
  simp only [State.getV, mapState, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases s.vr[i]? <;> simp [List.map_replicate]

theorem fail_hom (s : State E Lin) (m : String) : mapState env σ (s.fail m) = (mapState env σ s).fail m := by
  by_cases h : s.err.isSome = true
  · simp only [State.fail, h, ite_true, mapState]
  · simp only [State.fail, h, Bool.false_eq_true, ite_false, mapState]

end St

/-! ## Branches -/

theorem decideC_hom (σ : Nat → Int) : ∀ (c : Cond Lin) (b : Bool), c.decideC = some b →
    (mapCond σ c).decideC = some b
  | .eq a b', t, h => by
    simp only [Cond.decideC, mapCond, Option.map_eq_some_iff] at h ⊢
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by have := Lin.eval_asInt σ _ k hk; rw [Lin.eval_sub] at this; simp [Ctl.sub]; omega, rfl⟩
  | .lt a b', t, h => by
    simp only [Cond.decideC, mapCond, Option.map_eq_some_iff] at h ⊢
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by have := Lin.eval_asInt σ _ k hk; rw [Lin.eval_sub] at this; simp [Ctl.sub]; omega, rfl⟩
  | .le a b', t, h => by
    simp only [Cond.decideC, mapCond, Option.map_eq_some_iff] at h ⊢
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by have := Lin.eval_asInt σ _ k hk; rw [Lin.eval_sub] at this; simp [Ctl.sub]; omega, rfl⟩
  | .not c, t, h => by
    simp only [Cond.decideC, mapCond, Option.map_eq_some_iff] at h ⊢
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, decideC_hom σ c k hk, rfl⟩
  | .tt, t, h => by simpa [Cond.decideC, mapCond] using h

/-- A branch: the concrete machine goes where the symbolic run went, if the recorded
condition (when there is one) holds. -/
theorem branch_hom (env : Key → W32) (σ : Nat → Int) (orc orcC : Nat → Bool) (s : State E Lin)
    (c : Cond Lin) (t : Nat) (hA : AssumeOk σ (s.branch orc c t)) :
    (mapState env σ s).branch orcC (mapCond σ c) t = mapState env σ (s.branch orc c t) := by
  simp only [State.branch] at hA ⊢
  cases hd : c.decideC with
  | some b =>
    rw [decideC_hom σ c b hd]
    simp only [Option.isNone_some, Bool.false_eq_true, ite_false]
    cases b <;> rfl
  | none =>
    simp only [hd, Option.isNone_none, ite_true] at hA ⊢
    have hm := hA (c, orc s.pc) (by
      split <;> simp [State.next])
    simp only at hm
    rw [hm]
    simp only [Option.isNone_some, Bool.false_eq_true, ite_false]
    cases orc s.pc <;> rfl

end Hashtree.Asm
