import Hashtree.Asm.RegionTags
import Hashtree.Proofs.FrameLift

/-!
# R5: soundness of the region certificate (`Asm/RegionTags`)

`RegRel R u`: every register with a known region in `R` holds a value of that region (a pointer
of the region, or data for `rNum`).  `regStep_sound`: one instruction keeps the relation at the
stepped table; `region_run`: along an error-free run of a certified stream; `regionOk_of_regs`:
the lift's region side condition (`FrameLift.RegionOk`) at every state of such a run.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Hashtree.Proofs.RegionLift

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.BodyReads Hashtree.Asm.RspMap Hashtree.Asm.RegionTags
open Hashtree.Asm.RunExit
open Hashtree.Proofs.FrameLift (CS M0 effAddr_region exec_mov_reg exec_push exec_pop exec_pop_err exec_ret_rsp
  run_succ' run_halted' nexts_eq_succs getG_setG_self' getG_setG_ne' ptr_mk_eq)

/-- The region of a value: a pointer's region, `rNum` for data. -/
def regionVal : Val W32 Int → Region
  | .ptr p => p.region
  | .num _ _ => rNum

/-- The relation: every known region is the register's. -/
def RegRel (R : RTags) (u : CS) : Prop := ∀ r ρ, regOf R r = some ρ → regionVal (u.getG r) = ρ

section Regs

theorem regOf_set_self (R : RTags) (d : Nat) (v : Option Region) (hd : d < R.length) : regOf (R.set d v) d = v := by
  simp [regOf, List.getD_eq_getElem?_getD, List.getElem?_set_self hd]

theorem regOf_set_ne (R : RTags) (d r : Nat) (v : Option Region) (h : r ≠ d) : regOf (R.set d v) r = regOf R r := by
  simp [regOf, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem regOf_set_none (R : RTags) (d : Nat) : regOf (R.set d none) d = none := by
  by_cases hd : d < R.length
  · exact regOf_set_self R d none hd
  · have : (R.set d none)[d]? = none := List.getElem?_eq_none (by rw [List.length_set]; omega)
    simp [regOf, List.getD_eq_getElem?_getD, this]

theorem regOf_clearAll (i : Instr) (R : RTags) (r : Nat) :
    regOf (clearAll i R) r = if r ∈ dsts i then none else regOf R r := by
  unfold clearAll
  generalize dsts i = D
  induction D generalizing R with
  | nil => simp
  | cons d D ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases hr : r = d
    · subst hr; simp [clearReg, regOf_set_none]
    · simp [hr, clearReg, regOf_set_ne R d r none hr]

theorem length_set' (R : RTags) (d : Nat) (v : Option Region) : (R.set d v).length = R.length := List.length_set ..

theorem length_clearAll (i : Instr) (R : RTags) : (clearAll i R).length = R.length := by
  unfold clearAll
  generalize dsts i = D
  induction D generalizing R with
  | nil => rfl
  | cons d D ih => simp only [List.foldl_cons]; rw [ih]; exact List.length_set ..

end Regs

section Exec
variable {mem0 : M0} {orc : Nat → Bool} {u : CS} {R : RTags}

theorem gCtl_reg (u : CS) (q : Nat) : ∃ a, gCtl u (.reg q) = .ok a ∧ a.region = regionVal (u.getG q) := by
  cases hg : u.getG q with
  | ptr p => exact ⟨p, by simp [gCtl, hg]; rfl, rfl⟩
  | num lo hi => exact ⟨_, by simp [gCtl, hg, Lane.asConst]; rfl, rfl⟩

theorem gCtl_src (hR : RegRel R u) {src : GSrc} {b : Region} (hb : gsrcReg R src = some b) {a : Addr Int}
    (ha : gCtl u src = .ok a) : a.region = b := by
  cases src with
  | reg q =>
    obtain ⟨a', ha', hr⟩ := gCtl_reg u q
    rw [ha'] at ha; simp only [Except.ok.injEq] at ha; subst ha
    rw [hr]; exact hR q b hb
  | imm v =>
    change Except.ok (⟨rNum, Ctl.ofInt v⟩ : Addr Int) = Except.ok a at ha
    simp only [Except.ok.injEq] at ha; subst ha; simpa [gsrcReg] using hb
  | mem _ => simp [gsrcReg] at hb

theorem exec_mov_imm (d : Nat) (v : Int) (hh : u.halted = false) :
    exec 4 mem0 orc (.mov 64 d (.imm v)) u = (u.setG d (.ptr ⟨rNum, Ctl.ofInt v⟩)).next := by
  unfold exec; simp only [hh, Bool.false_eq_true, ite_false, ite_true]; rfl

theorem exec_xor_idiom (d : Nat) (hh : u.halted = false) :
    exec 4 mem0 orc (.alu .xor 64 d (.reg d)) u = (clearFlags (u.setG d (.ptr ⟨rNum, Ctl.ofInt 0⟩))).next := by
  unfold exec; simp only [hh, Bool.false_eq_true, ite_false, ite_true, and_self]; rfl

theorem exec_lea (d : Nat) (m : MemRef) (hh : u.halted = false) {a : Addr Int} (ha : effAddr 4 u m = .ok a) :
    exec 4 mem0 orc (.lea d m) u = (u.setG d (.ptr a)).next := by
  unfold exec; simp only [hh, Bool.false_eq_true, ite_false, ha, bind, Except.bind]; rfl

theorem exec_lea_ok (d : Nat) (m : MemRef) (hh : u.halted = false) (hok : (exec 4 mem0 orc (.lea d m) u).err = none) :
    ∃ a, effAddr 4 u m = .ok a := by
  unfold exec at hok; simp only [hh, Bool.false_eq_true, ite_false] at hok
  cases ha : effAddr 4 u m with
  | error e => rw [ha] at hok; exact absurd hok (fail_err u e)
  | ok a => exact ⟨a, rfl⟩

/-- 64-bit `add d, src` on a successful step: the written pointer's region. -/
theorem exec_add_region (op : LOp) (hop : op = .add) (d : Nat) (src : GSrc) (hne : ¬ (op = .xor ∧ src = .reg d))
    (hh : u.halted = false) (hok : (exec 4 mem0 orc (.alu op 64 d src) u).err = none) (hd : d < u.gpr.length) :
    ∃ a b, gCtl u (.reg d) = .ok a ∧ gCtl u src = .ok b ∧
      regionVal ((exec 4 mem0 orc (.alu op 64 d src) u).getG d) = (if b.region = rNum then a.region else b.region) := by
  subst hop
  unfold exec at hok ⊢
  simp only [hh, Bool.false_eq_true, ite_false, ite_true, hne] at hok ⊢
  obtain ⟨a, ha, _⟩ := gCtl_reg u d
  rw [ha] at hok ⊢
  cases hb : gCtl u src with
  | error e => simp only [hb, bind, Except.bind] at hok; exact absurd hok (fail_err u e)
  | ok b =>
    simp only [hb, bind, Except.bind] at hok ⊢
    refine ⟨a, b, rfl, rfl, ?_⟩
    split at hok
    · rename_i hc
      simp only [hc, ite_true, okOr, pure, Except.pure, getG_next, getG_setFlags]
      rw [getG_setG_self' _ _ _ hd]; rfl
    · exact absurd hok (fail_err u _)

/-- 64-bit `and d, src` on a successful step keeps the destination's region. -/
theorem exec_and_region (d : Nat) (src : GSrc) (hne : ¬ (LOp.and = .xor ∧ src = .reg d))
    (hh : u.halted = false) (hok : (exec 4 mem0 orc (.alu .and 64 d src) u).err = none) (hd : d < u.gpr.length) :
    regionVal ((exec 4 mem0 orc (.alu .and 64 d src) u).getG d) = regionVal (u.getG d) := by
  unfold exec at hok ⊢
  simp only [hh, Bool.false_eq_true, ite_false, ite_true, hne] at hok ⊢
  obtain ⟨a, ha, hr⟩ := gCtl_reg u d
  rw [ha] at hok ⊢
  cases hb : gCtl u src with
  | error e => simp only [hb, bind, Except.bind] at hok; exact absurd hok (fail_err u e)
  | ok b =>
    simp only [hb, bind, Except.bind] at hok ⊢
    cases hx : Ctl.asInt a.off <;> cases hy : Ctl.asInt b.off <;> simp only [hx, hy] at hok ⊢
    all_goals try exact absurd hok (fail_err u _)
    rename_i x y
    cases hz : andInt x y <;> simp only [hz] at hok ⊢
    · exact absurd hok (fail_err u _)
    · split at hok
      · rename_i hc
        simp only [hc, and_self, ite_true, okOr, pure, Except.pure, getG_next, getG_clearFlags]
        rw [getG_setG_self' _ _ _ hd]; exact hr
      · exact absurd hok (fail_err u _)

/-- 64-bit `sub d, src` on a successful step keeps the destination's region. -/
theorem exec_sub_region (d : Nat) (src : GSrc) (hh : u.halted = false)
    (hok : (exec 4 mem0 orc (.sub 64 d src) u).err = none) (hd : d < u.gpr.length) :
    regionVal ((exec 4 mem0 orc (.sub 64 d src) u).getG d) = regionVal (u.getG d) := by
  unfold exec at hok ⊢
  simp only [hh, Bool.false_eq_true, ite_false, ite_true] at hok ⊢
  obtain ⟨a, ha, hr⟩ := gCtl_reg u d
  rw [ha] at hok ⊢
  cases hb : gCtl u src with
  | error e => simp only [hb, bind, Except.bind] at hok; exact absurd hok (fail_err u e)
  | ok b =>
    simp only [hb, bind, Except.bind] at hok ⊢
    split at hok
    · rename_i hc
      simp only [hc, ite_true, okOr, pure, Except.pure, getG_next, getG_setFlags]
      rw [getG_setG_self' _ _ _ hd]; exact hr
    · exact absurd hok (fail_err u _)

theorem rsp_ptr_of_push (r : Nat) (hh : u.halted = false) (hok : (exec 4 mem0 orc (.push r) u).err = none) :
    ∃ sp, u.getG rsp = .ptr sp := by
  unfold exec at hok; simp only [hh, Bool.false_eq_true, ite_false] at hok
  cases hg : u.getG rsp with
  | ptr sp => exact ⟨sp, rfl⟩
  | num _ _ => rw [hg] at hok; exact absurd hok (fail_err u _)

theorem rsp_ptr_of_pop (r : Nat) (hh : u.halted = false) (hok : (exec 4 mem0 orc (.pop r) u).err = none) :
    ∃ sp, u.getG rsp = .ptr sp := by
  unfold exec at hok; simp only [hh, Bool.false_eq_true, ite_false] at hok
  cases hg : u.getG rsp with
  | ptr sp => exact ⟨sp, rfl⟩
  | num _ _ => rw [hg] at hok; exact absurd hok (fail_err u _)

theorem rsp_ptr_of_ret (hh : u.halted = false) (hok : (exec 4 mem0 orc .ret u).err = none) :
    ∃ sp, u.getG rsp = .ptr sp := by
  unfold exec at hok; simp only [hh, Bool.false_eq_true, ite_false] at hok
  cases hg : u.getG rsp with
  | ptr sp => exact ⟨sp, rfl⟩
  | num _ _ => rw [hg] at hok; exact absurd hok (fail_err u _)

theorem length_regStep (i : Instr) (R : RTags) : (regStep i R).length = R.length := by
  cases i <;> (simp only [regStep]; repeat' split) <;> simp [setReg, List.length_set, length_clearAll]

/-- **One instruction keeps the relation at the stepped table.** -/
theorem regStep_sound (hR : RegRel R u) (hR16 : R.length = 16) (hh : u.halted = false) (hlen : u.gpr.length = 16)
    (i : Instr) (hok : (exec 4 mem0 orc i u).err = none) : RegRel (regStep i R) (exec 4 mem0 orc i u) := by
  intro r ρ hρ
  rcases exec_shape 4 mem0 orc i u hh with ⟨hne, _⟩ | ⟨_, _, hgpr, _, _, _, _⟩
  · exact absurd hok hne
  have hr16 : r < 16 := by
    rcases Nat.lt_or_ge r 16 with h | h
    · exact h
    · exfalso
      have : regOf (regStep i R) r = none := by
        simp only [regOf, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by rw [length_regStep, hR16]; exact h)]; rfl
      rw [this] at hρ; cases hρ
  have hrl : r < R.length := by rw [hR16]; exact hr16
  have hru : r < u.gpr.length := by rw [hlen]; exact hr16
  -- a register the instruction does not write keeps its value
  have keep : regOf (regStep i R) r = regOf R r → r ∉ dsts i → regionVal ((exec 4 mem0 orc i u).getG r) = ρ := by
    intro hk hnd
    rw [hgpr r hnd]; exact hR r ρ (by rw [← hk]; exact hρ)
  cases i with
  | mov w d src =>
    simp only [regStep] at hρ
    split at hρ
    · rename_i hw; subst hw
      by_cases hrd : r = d
      · subst hrd
        cases src with
        | reg s =>
          simp only [setReg] at hρ
          rw [regOf_set_self _ _ _ hrl] at hρ
          rw [exec_mov_reg _ _ hh, getG_next, getG_setG_self' _ _ _ hru]
          exact hR s ρ hρ
        | imm v =>
          simp only [setReg] at hρ
          rw [regOf_set_self _ _ _ hrl] at hρ
          simp only [Option.some.injEq] at hρ; subst hρ
          rw [exec_mov_imm _ _ hh, getG_next, getG_setG_self' _ _ _ hru]; rfl
        | mem m => simp only [setReg] at hρ; rw [regOf_set_self _ _ _ hrl] at hρ; cases hρ
      · apply keep _ (by simp [dsts, hrd])
        cases src <;> simp [regStep, setReg, regOf_set_ne _ _ _ _ hrd]
    · rename_i hw
      rw [regOf_clearAll] at hρ
      split at hρ
      · cases hρ
      · rename_i hnd
        exact keep (by simp only [regStep, hw, ite_false, regOf_clearAll, hnd]) hnd
  | alu op w d src =>
    simp only [regStep] at hρ
    split at hρ
    · rename_i hw; subst hw
      by_cases hrd : r = d
      · subst hrd
        split at hρ
        · rename_i hx
          obtain ⟨rfl, rfl⟩ := hx
          simp only [setReg] at hρ
          rw [regOf_set_self _ _ _ hrl] at hρ
          simp only [Option.some.injEq] at hρ; subst hρ
          rw [exec_xor_idiom _ hh, getG_next, getG_clearFlags, getG_setG_self' _ _ _ hru]; rfl
        · rename_i hx
          split at hρ
          · rename_i hop; subst hop
            split at hρ
            · rename_i a b ha hb
              simp only [setReg] at hρ
              rw [regOf_set_self _ _ _ hrl] at hρ
              simp only [Option.some.injEq] at hρ; subst hρ
              obtain ⟨a', b', ha', hb', hres⟩ := exec_add_region .add rfl r src hx hh hok hru
              rw [hres]
              obtain ⟨a'', ha'', hr'⟩ := gCtl_reg u r
              rw [ha''] at ha'; simp only [Except.ok.injEq] at ha'; subst ha'
              rw [hr', hR r a ha, gCtl_src hR hb hb']
            · simp only [setReg] at hρ; rw [regOf_set_self _ _ _ hrl] at hρ; cases hρ
          · split at hρ
            · rename_i hop; subst hop
              rw [exec_and_region r src hx hh hok hru]; exact hR r ρ hρ
            · simp only [setReg] at hρ; rw [regOf_set_self _ _ _ hrl] at hρ; cases hρ
      · apply keep _ (by simp [dsts, hrd])
        simp only [regStep, ite_true]
        split
        · simp [setReg, regOf_set_ne _ _ _ _ hrd]
        · split
          · split <;> simp [setReg, regOf_set_ne _ _ _ _ hrd]
          · split
            · rfl
            · simp [setReg, regOf_set_ne _ _ _ _ hrd]
    · rename_i hw
      rw [regOf_clearAll] at hρ
      split at hρ
      · cases hρ
      · rename_i hnd
        exact keep (by simp only [regStep, hw, ite_false, regOf_clearAll, hnd]) hnd
  | sub w d src =>
    simp only [regStep] at hρ
    split at hρ
    · rename_i hw; subst hw
      by_cases hrd : r = d
      · subst hrd
        rw [exec_sub_region r src hh hok hru]; exact hR r ρ hρ
      · exact keep (by simp [regStep]) (by simp [dsts, hrd])
    · rename_i hw
      rw [regOf_clearAll] at hρ
      split at hρ
      · cases hρ
      · rename_i hnd
        exact keep (by simp only [regStep, hw, ite_false, regOf_clearAll, hnd]) hnd
  | lea d m =>
    simp only [regStep] at hρ
    by_cases hrd : r = d
    · subst hrd
      simp only [setReg] at hρ
      rw [regOf_set_self _ _ _ hrl] at hρ
      obtain ⟨a, ha⟩ := exec_lea_ok r m hh hok
      rw [exec_lea r m hh ha, getG_next, getG_setG_self' _ _ _ hru]
      show a.region = ρ
      rcases effAddr_region u m ha with ⟨hro, hreg⟩ | ⟨hro, hb, hreg⟩ | ⟨hro, b, p, hb, hp, hreg⟩
      · cases hm : m.ro with
        | none => exact absurd hm hro
        | some o => simp only [memReg, hm, Option.some.injEq] at hρ; rw [hreg, hρ]
      · simp only [memReg, hro, hb, Option.some.injEq] at hρ; rw [hreg, hρ]
      · simp only [memReg, hro, hb] at hρ
        rw [hreg]
        have := hR b ρ hρ
        rw [hp] at this; exact this
    · exact keep (by simp [regStep, setReg, regOf_set_ne _ _ _ _ hrd]) (by simp [dsts, hrd])
  | push q =>
    simp only [regStep] at hρ
    by_cases hr4 : r = 4
    · subst hr4
      obtain ⟨sp, hsp⟩ := rsp_ptr_of_push q hh hok
      rw [exec_push q hh hsp, getG_next, Hashtree.Proofs.FrameLift.getG_setG_rsp _ _ (by rw [Hashtree.Proofs.FrameLift.storeVal_gpr]; exact hru)]
      have := hR 4 ρ hρ
      rw [show u.getG 4 = u.getG rsp from rfl, hsp] at this
      exact this
    · exact keep rfl (by simp only [dsts, List.mem_singleton]; exact hr4)
  | pop q =>
    simp only [regStep] at hρ
    by_cases hrq : r = q
    · subst hrq; simp only [setReg] at hρ; rw [regOf_set_none] at hρ; cases hρ
    · simp only [setReg] at hρ; rw [regOf_set_ne _ _ _ _ hrq] at hρ
      by_cases hr4 : r = 4
      · subst hr4
        obtain ⟨sp, hsp⟩ := rsp_ptr_of_pop q hh hok
        obtain ⟨v, hv⟩ := exec_pop_err q hh hsp hok
        rw [exec_pop q hh hsp hv, getG_next, Hashtree.Proofs.FrameLift.getG_setG_rsp _ _ (by simp [State.setG, hru])]
        have := hR 4 ρ hρ
        rw [show u.getG 4 = u.getG rsp from rfl, hsp] at this
        exact this
      · exact keep (by simp [regStep, setReg, regOf_set_ne _ _ _ _ hrq]) (by simp only [dsts, List.mem_cons, not_or]; exact ⟨hrq, hr4, by simp⟩)
  | ret =>
    simp only [regStep] at hρ
    by_cases hr4 : r = 4
    · subst hr4
      obtain ⟨sp, hsp⟩ := rsp_ptr_of_ret hh hok
      obtain ⟨h4, _⟩ := exec_ret_rsp hh hlen hsp hok
      rw [h4]
      have := hR 4 ρ hρ
      rw [show u.getG 4 = u.getG rsp from rfl, hsp] at this
      exact this
    · exact keep rfl (by simp only [dsts, List.mem_singleton]; exact hr4)
  | _ =>
    simp only [regStep, regOf_clearAll] at hρ
    split at hρ
    · cases hρ
    · rename_i hnd
      exact keep (by simp only [regStep, regOf_clearAll, hnd, ite_false]) hnd

end Exec



/-! ## The run -/

section Run
variable {mem0 : M0} {orc : Nat → Bool}

theorem regAux_at (n : Nat) (RT : RSegs) :
    ∀ (p : Nat) (l : List Instr), regAux n RT p l = true → ∀ j i, l[j]? = some i → regAt n RT (p + j) i = true
  | _, [], _, _, _, h => by simp at h
  | p, i :: rest, h, j, i', hj => by
    simp only [regAux, Bool.and_eq_true] at h
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; simpa using h.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have := regAux_at n RT (p + 1) rest h.2 j i' hj
      rwa [show p + (j + 1) = p + 1 + j by omega]

theorem regCert_at {n : Nat} {prog : Array Instr} {RT : RSegs} {R0 : RTags} (h : regCert n prog RT R0 = true)
    {p : Nat} {i : Instr} (hp : prog[p]? = some i) : regAt n RT p i = true := by
  simp only [regCert, Bool.and_eq_true] at h
  have := regAux_at n RT 0 prog.toList h.2 p i (by rw [Array.getElem?_toList]; exact hp)
  simpa using this

/-- The lift's region side condition at a state whose bases are all known and off the stack. -/
theorem regionOk_of_bases {prog : Array Instr} {R : RTags} {u : CS} (hR : RegRel R u) {i : Instr}
    (hi : prog[u.pc]? = some i) (hb : basesOk R i = true) : Hashtree.Proofs.FrameLift.RegionOk prog u := by
  intro i' hi' m hm hb4 a ha
  rw [hi] at hi'; simp only [Option.some.injEq] at hi'; subst hi'
  rcases effAddr_region u m.1 ha with ⟨_, hr⟩ | ⟨_, _, hr⟩ | ⟨hro, b, p, hbm, hp, hr⟩
  · rw [hr]; decide
  · rw [hr]; decide
  · have hbb : b ∈ baseRegs i := by
      refine List.mem_filterMap.mpr ⟨m, hm, ?_⟩
      simp only [hro, hbm]
      have : b ≠ 4 := fun h => hb4 (by rw [hbm, h])
      simp [this]
    simp only [basesOk, List.all_eq_true] at hb
    have := hb b hbb
    cases hρ : regOf R b with
    | none => rw [hρ] at this; cases this
    | some ρ =>
      rw [hρ] at this
      simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] at this
      have hv := hR b ρ hρ
      rw [hp] at hv
      change p.region = ρ at hv
      rw [hr, hv]; exact this

/-- The run invariant: at a mapped pc with the pc's table, or halted. -/
def RInv (RT : RSegs) (u : CS) : Prop :=
  (u.halted = false ∧ ∃ R, atR RT u.pc = some R ∧ R.length = 16 ∧ RegRel R u) ∨ u.halted = true

/-- `R ⊆ R'` semantically. -/
theorem regRel_mono {R R' : RTags} (hR16 : R.length = 16) (hle : subRegs R R' = true) {u : CS}
    (h : RegRel R' u) : RegRel R u := by
  intro r ρ hρ
  have hr16 : r < 16 := by
    rcases Nat.lt_or_ge r 16 with h' | h'
    · exact h'
    · exfalso
      have : regOf R r = none := by
        simp only [regOf, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by rw [hR16]; exact h')]; rfl
      rw [this] at hρ; cases hρ
  simp only [subRegs, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at hle
  rcases hle r hr16 with h' | h'
  · rw [h'] at hρ; cases hρ
  · exact h r ρ (by rw [← h']; exact hρ)

theorem rinv_step {n : Nat} {prog : Array Instr} {RT : RSegs} {R0 : RTags} (hsz : prog.size = n)
    (hcert : regCert n prog RT R0 = true) {u : CS} (hinv : RInv RT u) {i : Instr} (hi : prog[u.pc]? = some i)
    (hh : u.halted = false) (hlen : u.gpr.length = 16) (hok : (exec 4 mem0 orc i u).err = none) :
    RInv RT (exec 4 mem0 orc i u) := by
  rcases hinv with ⟨_, R, hR, hR16, hrel⟩ | hh'
  · have hat := regCert_at hcert hi
    simp only [regAt, hR, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hat
    obtain ⟨⟨_, _⟩, hsucc⟩ := hat
    have hs := regStep_sound hrel hR16 hh hlen i hok
    rcases exec_shape 4 mem0 orc i u hh with ⟨hne, _⟩ | ⟨_, _, _, _, _, _, hpc⟩
    · exact absurd hok hne
    by_cases hhl : (exec 4 mem0 orc i u).halted = true
    · exact Or.inr hhl
    · left
      refine ⟨by simpa using hhl, ?_⟩
      rcases hpc with hq | hq
      · rw [← nexts_eq_succs] at hq
        obtain ⟨hqn, hRq⟩ := hsucc _ hq
        split at hRq
        · rename_i Rq hRq'
          have hq16 : Rq.length = 16 := by
            have hi' : ∃ i', prog[(exec 4 mem0 orc i u).pc]? = some i' := by
              have : (exec 4 mem0 orc i u).pc < prog.size := by rw [hsz]; exact hqn
              exact ⟨_, Array.getElem?_eq_getElem this⟩
            obtain ⟨i', hi'⟩ := hi'
            have := regCert_at hcert hi'
            simp only [regAt, hRq', Bool.and_eq_true, beq_iff_eq] at this
            exact this.1.1
          exact ⟨Rq, hRq', hq16, regRel_mono hq16 hRq hs⟩
        · cases hRq
      · exact absurd hq hhl
  · rw [hh'] at hh; cases hh

theorem region_run {n : Nat} {prog : Array Instr} {RT : RSegs} {R0 : RTags} (hsz : prog.size = n)
    (hcert : regCert n prog RT R0 = true) :
    ∀ (k : Nat) (u : CS), RInv RT u → u.gpr.length = 16 → (run prog 4 mem0 orc k u).err = none →
      RInv RT (run prog 4 mem0 orc k u)
  | 0, u, hinv, _, _ => hinv
  | k + 1, u, hinv, hlen, hok => by
    by_cases hh : u.halted = true
    · rw [run_halted' prog _ u hh]; exact hinv
    · have hh0 : u.halted = false := by simpa using hh
      cases hi : prog[u.pc]? with
      | none =>
        exfalso
        have : (run prog 4 mem0 orc (k + 1) u).err ≠ none := by
          simp only [run, hh0, Bool.false_eq_true, ite_false, hi]
          exact fail_err u _
        exact this hok
      | some i =>
        rw [run_succ' prog k u hh0 hi] at hok ⊢
        have hok1 : (exec 4 mem0 orc i u).err = none := RunExit.run_err_none prog 4 mem0 orc k _ hok 0 (Nat.zero_le _)
        exact region_run hsz hcert k _ (rinv_step hsz hcert hinv hi hh0 hlen hok1)
          (by rw [exec_gpr_len]; exact hlen) hok

/-- **The region side condition of the frame-slot lift**, at every non-halted state of an
error-free run of a certified stream. -/
theorem regionOk_run {n : Nat} {prog : Array Instr} {RT : RSegs} {R0 : RTags} (hsz : prog.size = n)
    (hcert : regCert n prog RT R0 = true) {u0 : CS} (hinv0 : RInv RT u0) (hlen : u0.gpr.length = 16) (k : Nat)
    (hok : (run prog 4 mem0 orc k u0).err = none) :
    ∀ j, j ≤ k → (run prog 4 mem0 orc j u0).halted = false →
      Hashtree.Proofs.FrameLift.RegionOk prog (run prog 4 mem0 orc j u0) := by
  intro j hj hhj
  have hokj := RunExit.run_err_none prog 4 mem0 orc k u0 hok j hj
  rcases region_run hsz hcert j u0 hinv0 hlen hokj with ⟨_, R, hR, hR16, hrel⟩ | hh'
  · intro i hi
    have hat := regCert_at hcert hi
    simp only [regAt, hR, Bool.and_eq_true, beq_iff_eq] at hat
    exact regionOk_of_bases hrel hi hat.1.2 i hi
  · rw [hh'] at hhj; cases hhj

end Run


end Hashtree.Proofs.RegionLift
