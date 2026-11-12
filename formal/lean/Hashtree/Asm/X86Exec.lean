import Hashtree.Asm.X86Hom

/-!
# `exec_hom`: every x86 instruction commutes with evaluation

If the symbolic step does not fail (`err = none`) and the branch conditions it recorded hold
under `σ`, the concrete machine started in the evaluated state ends in the evaluated result.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Hashtree.Asm.X86
open Hashtree.Asm

section Exec
variable (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin) (mem0c : Addr Int → Cell W32 Int)

/-- The `ok` wrapper of `exec`: a non-failing symbolic result is an `ok` one. -/
theorem ok_wrap (s : State E Lin) (rs : Except String (State E Lin)) (rc : Except String (State W32 Int))
    (hne : (okOr s rs).err = none)
    (hr : ∀ s', rs = .ok s' → rc = .ok (mapState env σ s')) :
    okOr (mapState env σ s) rc = mapState env σ (okOr s rs) := by
  cases rs with
  | ok s' => have := hr s' rfl; subst this; rfl
  | error e =>
    exfalso
    simp only [okOr, State.fail] at hne
    split at hne <;> simp_all

theorem ok_of_pure {β : Type} {x y : β} (h : (pure x : Except String β) = .ok y) : x = y := by
  simpa [pure, Except.pure] using h

theorem pure_ok {β : Type} (x : β) : (pure x : Except String β) = .ok x := rfl

/-- `(do let x ← m; f x) = .ok r` with `m = .ok a`. -/
theorem bind_ok {β δ : Type} {m : Except String β} {f : β → Except String δ} {r : δ} (h : (m >>= f) = .ok r) :
    ∃ a, m = .ok a ∧ f a = .ok r := by
  cases hm : m with
  | error e => rw [hm] at h; cases h
  | ok a => rw [hm] at h; exact ⟨a, rfl, h⟩

theorem clearFlags_hom (s : State E Lin) : mapState env σ (clearFlags s) = clearFlags (mapState env σ s) := rfl
theorem setFlags_hom (s : State E Lin) (a b : Lin) :
    mapState env σ (setFlags s a b) = setFlags (mapState env σ s) (a.eval σ) (b.eval σ) := rfl
theorem halt_hom (s : State E Lin) : mapState env σ (halt s) = halt (mapState env σ s) := rfl
theorem throw_eq {β : Type} (e : String) : (throw e : Except String β) = .error e := rfl

local macro "hom_simp" : tactic => `(tactic| (
  simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, setV_hom, setG_hom, getV_hom, getG_hom,
    setData32_hom, storeLane_hom, storeLanes_hom, storeVal_hom, mapVal, mapAddr_plusI, mapAddr_plus,
    List.map_take, List.map_map, Function.comp_def] <;> rfl))

theorem exec_hom (h0 : Mem0Rel env σ mem0s mem0c) (ro : Region) (orc orcC : Nat → Bool)
    (i : Instr) (s : State E Lin)
    (hne : (exec ro mem0s orc i s).err = none) (hA : AssumeOk σ (exec ro mem0s orc i s)) :
    exec ro mem0c orcC i (mapState env σ s) = mapState env σ (exec ro mem0s orc i s) := by
  unfold exec at hne hA ⊢
  by_cases hh : s.halted = true
  · simp only [hh, ite_true]
    simp only [mapState, hh, ite_true]
  have hh' : (mapState env σ s).halted = false := by simpa [mapState] using hh
  simp only [hh', Bool.false_eq_true, ite_false]
  simp only [hh, Bool.false_eq_true, ite_false] at hne hA ⊢
  cases i with
  | nop => rfl
  | jmp t => rfl
  | jmpTail name => rfl
  | vop op vex w d s1 s2 =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨b, hb, h⟩ := bind_ok h
    rw [readVSrc_hom env σ mem0s mem0c h0 ro s w s2 b hb, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, List.map_take]
    rw [lanes2_hom env (lop op) (lop op) (lop_hom env op)]
    simp only [List.map_take]
  | vshift k vex w d src n =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, List.map_take, List.map_map,
      Function.comp_def, shiftL_hom]
  | vshiftq vex w d src n =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, List.map_take]
    rw [pairs_unpairs_hom env (fun p => shrQ p.1 p.2 n) (fun p => shrQ p.1 p.2 n)
      (fun p => shrQ_hom env p.1 p.2 n)]
    simp only [List.map_take]
  | vror w d src n =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, List.map_take, List.map_map,
      Function.comp_def, eval_ror, W32_ror]
  | vtern w d s1 s2 imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, List.map_take]
    rw [lanes3_hom env (Lane.tern imm) (Lane.tern imm) (fun a b c => by simp)]
    simp only [List.map_take]
  | vload vex w d src =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨v, hv, h⟩ := bind_ok h
    rw [readVSrc_hom env σ mem0s mem0c h0 ro s w src v hv, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom]
  | vstore w m src =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    rw [effAddr_hom env σ ro s m a ha, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, storeLanes_hom, getV_hom, List.map_take]
  | pshufd vex d src imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, List.map_map, Function.comp_def,
      getD_map_ev]
  | pshufb vex w d src mask =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨r, hr, h⟩ := bind_ok h
    have hc := pshufbL_hom env _ _ w r hr
    rw [getV_hom, getV_hom, ← List.map_take, hc, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom]
  | palignr vex d s1 s2 imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, palignrL_hom]
  | pblendw d src imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, pblendwL_hom]
  | shufps w d s1 s2 imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, List.map_map, Function.comp_def]
    congr 2
    apply List.map_congr_left
    intro i _
    split <;> simp [getD_map_ev]
  | perm2f128 d s1 s2 imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, List.map_append]
    congr 3 <;> (split <;> (try split) <;> simp [List.map_take, List.map_drop])
  | inserti128 d s1 m imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨x, hx, h⟩ := bind_ok h
    rw [effAddr_hom env σ ro s m a ha, ok_bind, loadLanes_hom env σ mem0s mem0c h0 s 4 a x hx, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom]
    congr 2; split <;> simp [List.map_append, List.map_take, List.map_drop]
  | inserti64x4 d s1 m imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨x, hx, h⟩ := bind_ok h
    rw [effAddr_hom env σ ro s m a ha, ok_bind, loadLanes_hom env σ mem0s mem0c h0 s 8 a x hx, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom]
    congr 2; split <;> simp [List.map_append, List.map_take, List.map_drop]
  | permi2d d s1 s2 =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨idx, hi, h⟩ := bind_ok h
    rw [getV_hom, ctlLanes_hom env _ 16 idx hi, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, permi2dP_hom]
  | permi2q d s1 s2 =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨idx, hi, h⟩ := bind_ok h
    rw [getV_hom, ctlLanes_hom env _ 16 idx hi, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, permi2qP_hom]
  | sha256rnds2 d src =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, rnds2_hom]
  | sha256msg1 d src =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, msg1_hom]
  | sha256msg2 d src =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h; have := ok_of_pure h; subst this
    simp only [pure_ok, Except.ok.injEq, next_hom, setVec_hom, getV_hom, msg2_hom]
  | mov w d src =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hw : w = 64
    · simp only [hw, ite_true] at h ⊢
      cases src with
      | reg r => have := ok_of_pure h; subst this; simp only [pure_ok, next_hom, setG_hom, getG_hom]
      | imm v => have := ok_of_pure h; subst this; simp [pure_ok, next_hom, setG_hom, mapVal, mapAddr]
      | mem m =>
        dsimp only at h ⊢
        obtain ⟨a, ha, h⟩ := bind_ok h
        obtain ⟨v, hv, h⟩ := bind_ok h
        rw [effAddr_hom env σ ro s m a ha, ok_bind, loadVal_hom env σ mem0s mem0c h0 s a v hv, ok_bind]
        have := ok_of_pure h; subst this
        simp only [pure_ok, next_hom, setG_hom]
    · simp only [hw, ite_false] at h ⊢
      obtain ⟨x, hx, h⟩ := bind_ok h
      rw [gData32_hom env σ mem0s mem0c h0 ro s src x hx, ok_bind]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, setData32_hom]
  | movst w m src =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    rw [effAddr_hom env σ ro s m a ha, ok_bind]
    by_cases hw : w = 64
    · simp only [hw, ite_true] at h ⊢
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, storeVal_hom, getG_hom]
    · simp only [hw, ite_false] at h ⊢
      rw [getG_hom]
      cases hg : s.getG src with
      | num lo hi =>
        rw [hg] at h; dsimp only at h ⊢
        have := ok_of_pure h; subst this
        simp only [mapVal, pure_ok, next_hom, storeLane_hom]
      | ptr _ => rw [hg] at h; cases h
  | lea d m =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    rw [effAddr_hom env σ ro s m a ha, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, next_hom, setG_hom, mapVal]
  | ror w d n =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hw : w = 32
    · simp only [hw, ite_true] at h ⊢
      obtain ⟨a, ha, h⟩ := bind_ok h
      rw [gData32_hom env σ mem0s mem0c h0 ro s _ a ha, ok_bind]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, clearFlags_hom, setData32_hom, eval_ror, W32_ror]
    · simp only [hw, ite_false] at h; cases h
  | shld w d src n =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hw : w = 32
    · simp only [hw, ite_true] at h ⊢
      obtain ⟨a, ha, h⟩ := bind_ok h
      obtain ⟨b, hb, h⟩ := bind_ok h
      rw [gData32_hom env σ mem0s mem0c h0 ro s _ a ha, ok_bind, gData32_hom env σ mem0s mem0c h0 ro s _ b hb, ok_bind]
      have := ok_of_pure h; subst this
      simp only [pure_ok, Except.ok.injEq, next_hom]
      split <;> simp [setData32_hom, clearFlags_hom]
    · simp only [hw, ite_false] at h; cases h
  | bswap w d =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hw : w = 32
    · simp only [hw, ite_true] at h ⊢
      obtain ⟨a, ha, h⟩ := bind_ok h
      rw [gData32_hom env σ mem0s mem0c h0 ro s _ a ha, ok_bind]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, setData32_hom, ofBytes_hom, eval_byteOf]
    · simp only [hw, ite_false] at h; cases h
  | push r =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    rw [getG_hom]
    cases hg : s.getG rsp with
    | ptr sp =>
      rw [hg] at h; dsimp only at h ⊢
      have := ok_of_pure h; subst this
      simp only [mapVal, pure_ok, next_hom, setG_hom, storeVal_hom, getG_hom, mapAddr_plusI]
    | num _ _ => rw [hg] at h; cases h
  | pop r =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    rw [getG_hom]
    cases hg : s.getG rsp with
    | ptr sp =>
      rw [hg] at h; simp only [mapVal]; dsimp only at h ⊢
      obtain ⟨v, hv, h⟩ := bind_ok h
      rw [loadVal_hom env σ mem0s mem0c h0 s sp v hv, ok_bind]
      have := ok_of_pure h; subst this
      simp only [mapVal, pure_ok, next_hom, setG_hom, mapAddr_plusI]
    | num _ _ => rw [hg] at h; cases h
  | jcc c t =>
    dsimp only at hne hA ⊢
    cases hf : s.flags with
    | none =>
      exfalso; rw [hf] at hne; simp only [throw_eq, okOr, State.fail] at hne; split at hne <;> simp_all
    | some p =>
      obtain ⟨a, b⟩ := p
      rw [hf] at hne hA
      dsimp only [okOr] at hne hA ⊢
      have hfc : (mapState env σ s).flags = some (a.eval σ, b.eval σ) := by simp [mapState, hf]
      rw [hfc]
      dsimp only [okOr]
      rw [← ccCond_hom σ c a b]
      exact branch_hom env σ orc orcC s _ t hA
  | alu op w d src =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hw : w = 64
    · simp only [hw, ite_true] at h ⊢
      by_cases hz : op = .xor ∧ src = .reg d
      · rw [if_pos hz] at h; rw [if_pos hz]
        have := ok_of_pure h; subst this
        simp [pure_ok, next_hom, clearFlags_hom, setG_hom, mapVal, mapAddr]
      · rw [if_neg hz] at h; rw [if_neg hz]
        obtain ⟨a, ha, h⟩ := bind_ok h
        obtain ⟨b, hb, h⟩ := bind_ok h
        rw [gCtl_hom env σ s _ a ha, ok_bind, gCtl_hom env σ s _ b hb, ok_bind]
        cases op with
        | add =>
          dsimp only at h ⊢
          by_cases hr : b.region = rNum ∨ a.region = rNum
          · rw [if_pos hr] at h; rw [if_pos (by simpa [mapAddr] using hr)]
            have := ok_of_pure h; subst this
            simp only [pure_ok, next_hom, setFlags_hom, setG_hom, mapVal, mapAddr, Lin.eval_add, Lin.eval_ofInt]
            by_cases hb' : b.region = rNum <;> simp [hb']
          · rw [if_neg hr] at h; simp [throw_eq] at h
        | and =>
          dsimp only at h ⊢
          cases hx : (Ctl.asInt a.off : Option Int) with
          | none => rw [hx] at h; simp [throw_eq] at h
          | some x =>
            cases hy : (Ctl.asInt b.off : Option Int) with
            | none => rw [hx, hy] at h; simp [throw_eq] at h
            | some y =>
              rw [hx, hy] at h
              have ex := Lin.eval_asInt σ _ x hx
              have ey := Lin.eval_asInt σ _ y hy
              simp only [mapAddr, Int_asInt, ex, ey]
              dsimp only at h ⊢
              cases hr : andInt x y with
              | none => rw [hr] at h; simp [throw_eq] at h
              | some r =>
                rw [hr] at h; dsimp only at h ⊢
                by_cases hc : b.region = rNum ∧ (a.region = rNum ∨ (-64 ≤ y ∧ y < 0))
                · rw [if_pos hc] at h; rw [if_pos hc]
                  have := ok_of_pure h; subst this
                  simp [pure_ok, next_hom, clearFlags_hom, setG_hom, mapVal, mapAddr]
                · rw [if_neg hc] at h; simp [throw_eq] at h
        | xor => simp [throw_eq] at h
        | or => simp [throw_eq] at h
    · simp only [hw, ite_false] at h ⊢
      by_cases hz : op = .xor ∧ src = .reg d
      · rw [if_pos hz] at h; rw [if_pos hz]
        have := ok_of_pure h; subst this
        simp [pure_ok, next_hom, clearFlags_hom, setData32_hom]
      · rw [if_neg hz] at h; rw [if_neg hz]
        obtain ⟨a, ha, h⟩ := bind_ok h
        obtain ⟨b, hb, h⟩ := bind_ok h
        rw [gData32_hom env σ mem0s mem0c h0 ro s _ a ha, ok_bind, gData32_hom env σ mem0s mem0c h0 ro s _ b hb, ok_bind]
        have := ok_of_pure h; subst this
        simp only [pure_ok, next_hom, clearFlags_hom, setData32_hom, lop_hom]
  | sub w d src =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hw : w = 64
    · simp only [hw, ite_true] at h ⊢
      obtain ⟨a, ha, h⟩ := bind_ok h
      obtain ⟨b, hb, h⟩ := bind_ok h
      rw [gCtl_hom env σ s _ a ha, ok_bind, gCtl_hom env σ s _ b hb, ok_bind]
      by_cases hr : b.region = rNum
      · rw [if_pos hr] at h; rw [if_pos (by simpa [mapAddr] using hr)]
        have := ok_of_pure h; subst this
        simp [pure_ok, next_hom, setFlags_hom, setG_hom, mapVal, mapAddr, Addr.plus, Lin.eval_smul,
          Lin.eval_add, Int.neg_one_mul]
      · rw [if_neg hr] at h; simp [throw_eq] at h
    · simp only [hw, ite_false] at h; simp [throw_eq] at h
  | shl w d n =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hw : w = 64
    · simp only [hw, ite_true] at h ⊢
      obtain ⟨a, ha, h⟩ := bind_ok h
      rw [gCtl_hom env σ s _ a ha, ok_bind]
      by_cases hr : a.region = rNum
      · rw [if_pos hr] at h; rw [if_pos (by simpa [mapAddr] using hr)]
        have := ok_of_pure h; subst this
        simp [pure_ok, next_hom, clearFlags_hom, setG_hom, mapVal, mapAddr, Lin.eval_smul]
      · rw [if_neg hr] at h; simp [throw_eq] at h
    · simp only [hw, ite_false] at h ⊢
      obtain ⟨a, ha, h⟩ := bind_ok h
      rw [gData32_hom env σ mem0s mem0c h0 ro s _ a ha, ok_bind]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, clearFlags_hom, setData32_hom, shiftL_hom]
  | cmp w a b =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hw : w = 64
    · simp only [hw, ite_true] at h ⊢
      obtain ⟨x, hx, h⟩ := bind_ok h
      obtain ⟨y, hy, h⟩ := bind_ok h
      rw [gCtl_hom env σ s _ x hx, ok_bind, gCtl_hom env σ s _ y hy, ok_bind]
      by_cases hr : y.region = rNum ∨ y.region = x.region
      · rw [if_pos hr] at h; rw [if_pos (by simpa [mapAddr] using hr)]
        have := ok_of_pure h; subst this
        simp [pure_ok, next_hom, setFlags_hom, mapAddr]
      · rw [if_neg hr] at h; simp [throw_eq] at h
    · simp only [hw, ite_false] at h; simp [throw_eq] at h
  | test w a b =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hw : w = 64 ∧ a = b
    · rw [if_pos hw] at h; rw [if_pos hw]
      obtain ⟨x, hx, h⟩ := bind_ok h
      rw [gCtl_hom env σ s _ x hx, ok_bind]
      by_cases hr : x.region = rNum
      · rw [if_pos hr] at h; rw [if_pos (by simpa [mapAddr] using hr)]
        have := ok_of_pure h; subst this
        simp [pure_ok, next_hom, setFlags_hom, mapAddr]
      · rw [if_neg hr] at h; simp [throw_eq] at h
    · rw [if_neg hw] at h; simp [throw_eq] at h
  | jccTail c name =>
    dsimp only at hne hA ⊢
    cases hf : s.flags with
    | none =>
      exfalso; rw [hf] at hne; simp only [throw_eq, okOr, State.fail] at hne; split at hne <;> simp_all
    | some p =>
      obtain ⟨a, b⟩ := p
      rw [hf] at hne hA
      have hfc : (mapState env σ s).flags = some (a.eval σ, b.eval σ) := by simp [mapState, hf]
      rw [hfc]
      dsimp only at hne hA ⊢
      have hpc : ∀ x : State E Lin, (mapState env σ x).pc = x.pc := fun _ => rfl
      by_cases hp : (s.branch orc (ccCond c a b) 1000000000).pc = 1000000000
      · rw [if_pos hp] at hA ⊢
        have hA' : AssumeOk σ (s.branch orc (ccCond c a b) 1000000000) := hA
        have hb := branch_hom env σ orc orcC s _ 1000000000 hA'
        rw [← ccCond_hom σ c a b, hb, hpc, if_pos hp]
        rfl
      · rw [if_neg hp] at hA ⊢
        have hA' : AssumeOk σ (s.branch orc (ccCond c a b) 1000000000) := hA
        have hb := branch_hom env σ orc orcC s _ 1000000000 hA'
        rw [← ccCond_hom σ c a b, hb, hpc, if_neg hp]
        rfl
  | ret =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    rw [getG_hom]
    cases hg : s.getG rsp with
    | ptr sp =>
      rw [hg] at h; simp only [mapVal]; dsimp only at h ⊢
      obtain ⟨v, hv, h⟩ := bind_ok h
      rw [loadVal_hom env σ mem0s mem0c h0 s sp v hv, ok_bind]
      cases v with
      | ptr q =>
        obtain ⟨rq, o⟩ := q
        simp only [mapVal, mapAddr]
        by_cases h5 : rq = 5
        · subst h5
          have := ok_of_pure h; subst this
          simp only [pure_ok, Except.ok.injEq, halt_hom, setG_hom, mapVal, mapAddr_plusI]
          rfl
        · exfalso
          split at h
          · rename_i heq; cases heq; exact h5 rfl
          · simp [throw_eq] at h
      | num _ _ => simp [throw_eq] at h
    | num _ _ => rw [hg] at h; simp [throw_eq] at h

end Exec

end Hashtree.Asm.X86
