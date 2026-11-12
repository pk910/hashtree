import Hashtree.Asm.Riscv
import Hashtree.Asm.Hom

/-!
# Soundness of the symbolic RV64 model: the helpers

Every helper of `exec` (lane-pair arithmetic, register access, operand conversion, effective
addresses, comparisons, jumps) commutes with evaluation.  `RiscvExec.lean` assembles them into
`exec_hom`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Asm.Riscv
open Hashtree.Asm

/-! ## Lane-level helpers -/

section Pure
variable (env : Key → W32)

local notation "ev" => E.eval env

@[simp] theorem lanesOfInt_ev1 (k : Int) : ((lanesOfInt k : E × E).1).eval env = (lanesOfInt k : W32 × W32).1 := rfl
@[simp] theorem lanesOfInt_ev2 (k : Int) : ((lanesOfInt k : E × E).2).eval env = (lanesOfInt k : W32 × W32).2 := rfl

theorem bop_hom (op : BOp) (a b : E) : ev (bop op a b) = bop op (ev a) (ev b) := by
  cases op <;> simp [bop]

theorem add64_hom (a b : E × E) :
    (ev (add64 a b).1, ev (add64 a b).2) = add64 (ev a.1, ev a.2) (ev b.1, ev b.2) := by
  simp [add64]

theorem shl64_hom (x : E × E) (n : Nat) :
    (ev (shl64 x n).1, ev (shl64 x n).2) = shl64 (ev x.1, ev x.2) n := by
  by_cases h1 : n = 0
  · simp [shl64, h1]
  · by_cases h2 : n < 32
    · simp [shl64, h1, h2]
    · by_cases h3 : n = 32
      · simp [shl64, h3]
      · simp [shl64, h1, h2, h3]

theorem sra64_hom (x : E × E) (n : Nat) :
    (ev (sra64 x n).1, ev (sra64 x n).2) = sra64 (ev x.1, ev x.2) n := by
  by_cases h1 : n = 0
  · simp [sra64, h1]
  · by_cases h2 : n < 32
    · simp [sra64, h1, h2]
    · by_cases h3 : n = 32
      · simp [sra64, h3]
      · simp [sra64, h1, h2, h3]

theorem bswap32_hom (x : E) : ev (bswap32 x) = bswap32 (ev x) := by
  simp [bswap32, byteOf]

theorem wop_hom (op : WOp) (x : E) (n : Nat) : ev (wop op x n) = wop op (ev x) n := by
  cases op <;> simp [wop]

theorem shaF_hom (op : ShaOp) (x : E) : ev (shaF op x) = shaF op (ev x) := by
  cases op <;> simp [shaF]

end Pure

/-! ## Registers, operands, addresses -/

section St
variable (env : Key → W32) (σ : Nat → Int)

local notation "ev" => E.eval env

theorem sext_hom (r : E) : mapVal env σ (sext r : Val E Lin) = sext (ev r) := by
  simp [sext, mapVal]

theorem zeroV_hom : mapVal env σ (zeroV : Val E Lin) = zeroV := rfl

theorem rget_hom (s : State E Lin) (i : Nat) : rget (mapState env σ s) i = mapVal env σ (rget s i) := by
  unfold rget
  split
  · rfl
  · exact getG_hom env σ s i

theorem rset_hom (s : State E Lin) (i : Nat) (v : Val E Lin) :
    mapState env σ (rset s i v) = rset (mapState env σ s) i (mapVal env σ v) := by
  unfold rset
  split
  · rfl
  · exact setG_hom env σ s i v

theorem target_hom (pe : Env) (t : Target) (a : Addr Lin) (h : pe.target t = .ok a) :
    (pe.target t : Except String (Addr Int)) = .ok (mapAddr σ a) := by
  cases t with
  | ro o =>
    simp only [Env.target, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; simp [mapAddr]
  | got k =>
    simp only [Env.target, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; simp [mapAddr]
  | sym n o =>
    simp only [Env.target] at h ⊢
    cases hf : pe.syms.find? (·.1 = n) with
    | none => rw [hf] at h; cases h
    | some p =>
      obtain ⟨_, r⟩ := p
      rw [hf] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
      subst h; simp [mapAddr]

theorem dataOf_hom (v : Val E Lin) (x : E × E) (h : dataOf v = .ok x) :
    dataOf (mapVal env σ v) = .ok (ev x.1, ev x.2) := by
  cases v with
  | num lo hi =>
    simp only [dataOf, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | ptr a =>
    obtain ⟨r, n⟩ := a
    cases r with
    | zero =>
      simp only [mapVal, mapAddr]
      simp only [dataOf] at h ⊢
      cases hn : (Ctl.asInt n : Option Int) with
      | none => rw [hn] at h; cases h
      | some k =>
        rw [hn] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Int_asInt, Lin.eval_asInt σ n k hn, pure, Except.pure, lanesOfInt_ev1, lanesOfInt_ev2]
    | succ m => simp [dataOf, throw, throwThe, MonadExceptOf.throw] at h

theorem ctlOf_hom (v : Val E Lin) (a : Addr Lin) (h : ctlOf v = .ok a) :
    ctlOf (mapVal env σ v) = .ok (mapAddr σ a) := by
  cases v with
  | ptr q =>
    simp only [ctlOf, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | num lo hi =>
    simp only [ctlOf] at h
    simp only [mapVal, ctlOf]
    cases hl : (Lane.asConst lo : Option W32) with
    | none => rw [hl] at h; cases h
    | some l =>
      cases hh : (Lane.asConst hi : Option W32) with
      | none => rw [hl, hh] at h; cases h
      | some hv =>
        rw [hl, hh] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have e1 : (Lane.asConst (ev lo) : Option W32) = some l := by rw [eval_asConst env lo l hl]; rfl
        have e2 : (Lane.asConst (ev hi) : Option W32) = some hv := by rw [eval_asConst env hi hv hh]; rfl
        rw [e1, e2]
        dsimp only
        unfold mapAddr
        rw [Lin.eval_ofInt, Int_ofInt]
        rfl

theorem addVal_hom (a b : Val E Lin) (v : Val E Lin) (h : addVal a b = .ok v) :
    addVal (mapVal env σ a) (mapVal env σ b) = .ok (mapVal env σ v) := by
  cases a with
  | ptr p =>
    cases b with
    | ptr q =>
      simp only [addVal, mapVal] at h ⊢
      by_cases hq : q.region = rNum
      · rw [if_pos hq] at h
        rw [if_pos (show (mapAddr σ q).region = rNum from hq)]
        simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
        subst h; simp [mapVal, mapAddr, Addr.plus, Lin.eval_add]
      · rw [if_neg hq] at h
        rw [if_neg (show ¬ (mapAddr σ q).region = rNum from hq)]
        by_cases hp : p.region = rNum
        · rw [if_pos hp] at h
          rw [if_pos (show (mapAddr σ p).region = rNum from hp)]
          simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
          subst h; simp [mapVal, mapAddr, Addr.plus, Lin.eval_add]
        · rw [if_neg hp] at h; cases h
    | num lo hi =>
      simp only [addVal] at h
      cases hq : ctlOf (Val.num lo hi : Val E Lin) with
      | error e => rw [hq] at h; cases h
      | ok q =>
        rw [hq, ok_bind] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hc := ctlOf_hom env σ _ q hq
        simp only [mapVal] at hc ⊢
        simp only [addVal]
        rw [hc, ok_bind]
        simp [pure, Except.pure, mapVal, mapAddr, Addr.plus, Lin.eval_add]
  | num lo hi =>
    cases b with
    | ptr q =>
      simp only [addVal] at h
      cases hp : ctlOf (Val.num lo hi : Val E Lin) with
      | error e => rw [hp] at h; cases h
      | ok p =>
        rw [hp, ok_bind] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hc := ctlOf_hom env σ _ p hp
        simp only [mapVal] at hc ⊢
        simp only [addVal]
        rw [hc, ok_bind]
        simp [pure, Except.pure, mapVal, mapAddr, Addr.plus, Lin.eval_add]
    | num lo' hi' =>
      simp only [addVal] at h
      cases hx : dataOf (Val.num lo hi : Val E Lin) with
      | error e => rw [hx] at h; cases h
      | ok x =>
        rw [hx, ok_bind] at h
        cases hy : dataOf (Val.num lo' hi' : Val E Lin) with
        | error e => rw [hy] at h; cases h
        | ok y =>
          rw [hy, ok_bind] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hcx := dataOf_hom env σ _ x hx
          have hcy := dataOf_hom env σ _ y hy
          simp only [mapVal] at hcx hcy ⊢
          simp only [addVal]
          rw [hcx, ok_bind, hcy, ok_bind]
          simp only [pure, Except.pure, Except.ok.injEq]
          rw [← add64_hom env x y]

theorem ea_hom (s : State E Lin) (b : Nat) (off : Int) (a : Addr Lin) (h : ea s b off = .ok a) :
    ea (mapState env σ s) b off = .ok (mapAddr σ a) := by
  simp only [ea, rget_hom] at h ⊢
  cases hg : rget s b with
  | num _ _ => rw [hg] at h; cases h
  | ptr q =>
    rw [hg] at h
    dsimp only at h
    simp only [mapVal]
    by_cases hr : q.region = rNum
    · rw [if_pos hr] at h; cases h
    · rw [if_neg hr] at h
      rw [if_neg (show ¬ (mapAddr σ q).region = rNum from hr)]
      simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
      subst h
      rw [mapAddr_plusI]

theorem checkWritable_hom (pe : Env) (a : Addr Lin) (u : Unit) (h : checkWritable pe a = .ok u) :
    checkWritable pe (mapAddr σ a) = .ok () := by
  simp only [checkWritable] at h ⊢
  by_cases hr : a.region = pe.ro ∨ a.region = pe.got
  · rw [if_pos hr] at h; cases h
  · rw [if_neg (show ¬ ((mapAddr σ a).region = pe.ro ∨ (mapAddr σ a).region = pe.got) from hr)]; rfl

theorem isNullA_hom (a : Addr Lin) (h : isNullA a) : isNullA (mapAddr σ a) := by
  simp only [isNullA, mapAddr, Int_asInt] at h ⊢
  exact ⟨h.1, by rw [Lin.eval_asInt σ _ 0 h.2]⟩

theorem eqCond_hom (x y : Addr Lin) (c : Cond Lin) (h : eqCond x y = .ok c) :
    eqCond (mapAddr σ x) (mapAddr σ y) = .ok (mapCond σ c) := by
  simp only [eqCond] at h ⊢
  by_cases hr : x.region = y.region
  · rw [if_pos hr] at h
    rw [if_pos (show (mapAddr σ x).region = (mapAddr σ y).region from hr)]
    simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; rfl
  · rw [if_neg hr] at h
    rw [if_neg (show ¬ (mapAddr σ x).region = (mapAddr σ y).region from hr)]
    by_cases hn : (isNullA x ∧ y.region ≠ rNum) ∨ (isNullA y ∧ x.region ≠ rNum)
    · rw [if_pos hn] at h
      have hn' : (isNullA (mapAddr σ x) ∧ (mapAddr σ y).region ≠ rNum) ∨
          (isNullA (mapAddr σ y) ∧ (mapAddr σ x).region ≠ rNum) := by
        rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨isNullA_hom σ x h1, h2⟩
        · exact Or.inr ⟨isNullA_hom σ y h1, h2⟩
      rw [if_pos hn']
      simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
      subst h; rfl
    · rw [if_neg hn] at h; cases h

/-! ## Named state updates -/

theorem halt_hom (s : State E Lin) : mapState env σ (halt s) = halt (mapState env σ s) := rfl
theorem setPc_hom (s : State E Lin) (k : Nat) : mapState env σ (setPc s k) = setPc (mapState env σ s) k := rfl
theorem haltTail_hom (s : State E Lin) (n : String) :
    mapState env σ (haltTail s n) = haltTail (mapState env σ s) n := rfl
theorem callOut_hom (s : State E Lin) (pc : Nat) (n : String) :
    mapState env σ (callOut s pc n) = callOut (mapState env σ s) pc n := rfl
theorem assumeC_hom (s : State E Lin) (cs : List (Cond Lin × Bool)) :
    mapState env σ (assumeC s cs) = mapState env σ s := rfl

theorem link_hom (pe : Env) (s : State E Lin) (d : Nat) :
    mapState env σ (link pe s d) = link pe (mapState env σ s) d := by
  unfold link
  rw [rset_hom]
  simp [mapVal, mapAddr]
  rfl

theorem jumpTo_hom (pe : Env) (s : State E Lin) (d : Nat) (t : Addr Lin) (s' : State E Lin)
    (h : jumpTo pe s d t = .ok s') : jumpTo pe (mapState env σ s) d (mapAddr σ t) = .ok (mapState env σ s') := by
  unfold jumpTo at h ⊢
  have hreg : (mapAddr σ t).region = t.region := rfl
  have hoff : (Ctl.asInt (mapAddr σ t).off : Option Int) = some (t.off.eval σ) := rfl
  rw [hreg, hoff]
  by_cases hr : t.region = rRet
  · rw [if_pos hr] at h ⊢
    by_cases hd : d = 0
    · rw [if_pos hd] at h ⊢
      simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
      subst h; rfl
    · rw [if_neg hd] at h; cases h
  · rw [if_neg hr] at h ⊢
    by_cases hc : t.region = pe.code
    · rw [if_pos hc] at h ⊢
      cases hk : (Ctl.asInt t.off : Option Int) with
      | none => rw [hk] at h; cases h
      | some k =>
        rw [hk] at h
        dsimp only at h ⊢
        rw [Lin.eval_asInt σ _ k hk]
        by_cases hk0 : k ≥ 0
        · rw [if_pos hk0] at h; rw [if_pos hk0]
          simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
          subst h
          rw [setPc_hom, link_hom]
        · rw [if_neg hk0] at h; cases h
    · rw [if_neg hc] at h ⊢
      cases hn : pe.nameOf t.region with
      | none => rw [hn] at h; cases h
      | some name =>
        cases hk : (Ctl.asInt t.off : Option Int) with
        | none => rw [hn, hk] at h; cases h
        | some k =>
          rw [hn, hk] at h
          dsimp only at h ⊢
          rw [Lin.eval_asInt σ _ k hk]
          by_cases hk0 : k = 0
          · rw [if_pos hk0] at h; rw [if_pos hk0]
            by_cases hd : d = 0
            · rw [if_pos hd] at h; rw [if_pos hd]
              simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
              subst h; rfl
            · rw [if_neg hd] at h; rw [if_neg hd]
              simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
              subst h
              rw [callOut_hom, link_hom]
              rfl
          · rw [if_neg hk0] at h; cases h

@[simp] theorem rset_assume {α γ : Type} [Lane α] [Ctl γ] [Inhabited α] [Inhabited γ]
    (s : State α γ) (i : Nat) (v : Val α γ) : (rset s i v).assume = s.assume := by
  unfold rset; split <;> rfl
@[simp] theorem rset_err {α γ : Type} [Lane α] [Ctl γ] [Inhabited α] [Inhabited γ]
    (s : State α γ) (i : Nat) (v : Val α γ) : (rset s i v).err = s.err := by
  unfold rset; split <;> rfl

theorem slliV_hom (s : State E Lin) (d : Nat) (v : Val E Lin) (n : Nat) (s' : State E Lin)
    (h : slliV s d v n = .ok s') (hA : AssumeOk σ s') :
    slliV (mapState env σ s) d (mapVal env σ v) n = .ok (mapState env σ s') := by
  cases v with
  | num lo hi =>
    simp only [slliV, mapVal, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h
    rw [next_hom, rset_hom]
    simp only [mapVal]
    rw [← shl64_hom env (lo, hi) n]
  | ptr a =>
    obtain ⟨r, k⟩ := a
    cases r with
    | succ m => simp [slliV, throw, throwThe, MonadExceptOf.throw] at h
    | zero =>
      simp only [mapVal, mapAddr]
      simp only [slliV] at h ⊢
      have hev : (Ctl.smul (2 ^ n) k : Lin).eval σ = 2 ^ n * k.eval σ := Lin.eval_smul σ _ _
      simp only [Int_smul, Int_asInt]
      cases hr : (Ctl.asInt (Ctl.smul (2 ^ n) k : Lin) : Option Int) with
      | some v =>
        rw [hr] at h
        dsimp only at h
        have hv := Lin.eval_asInt σ _ v hr
        rw [hev] at hv
        rw [hv]
        by_cases ho : v ≥ 2 ^ 63 ∨ v < -(2 ^ 63)
        · rw [if_pos ho] at h; cases h
        · rw [if_neg ho] at h; rw [if_neg ho]
          simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
          subst h
          rw [next_hom, rset_hom]
          simp only [mapVal, mapAddr, hev, hv]
      | none =>
        rw [hr] at h
        dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have h1 := hA (Cond.lt (Ctl.smul (2 ^ n) k) (Ctl.ofInt (2 ^ 63)), true)
          (by simp [State.next, assumeC, noWrap])
        have h2 := hA (Cond.le (Ctl.ofInt (-(2 ^ 63))) (Ctl.smul (2 ^ n) k), true)
          (by simp [State.next, assumeC, noWrap])
        simp only [mapCond, Cond.decideC, Ctl.sub, Int_smul, Int_add, Int_asInt, Lin.eval_ofInt, hev,
          Option.map_some, Option.some.injEq, decide_eq_true_eq] at h1 h2
        have ho : ¬ (2 ^ n * k.eval σ ≥ 2 ^ 63 ∨ 2 ^ n * k.eval σ < -(2 ^ 63)) := by omega
        rw [if_neg ho]
        simp only [pure, Except.pure, Except.ok.injEq]
        rw [next_hom, rset_hom, assumeC_hom]
        simp only [mapVal, mapAddr, hev]

end St

end Hashtree.Asm.Riscv
