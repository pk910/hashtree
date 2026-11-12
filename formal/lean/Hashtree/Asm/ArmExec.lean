import Hashtree.Asm.ArmHom

/-!
# `exec_hom`: every AArch64 instruction commutes with evaluation

If the symbolic step does not fail (`err = none`) and the branch conditions it recorded hold
under `σ`, the concrete machine started in the evaluated state ends in the evaluated result.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Hashtree.Asm.Arm
open Hashtree.Asm

section Exec
variable (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin) (mem0c : Addr Int → Cell W32 Int)

local notation "ev" => E.eval env

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
  | b t => rfl
  | bTail name => rfl
  -- general registers
  | movz d imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hd : d = sp
    · rw [if_pos hd] at h; cases h
    rw [if_neg hd] at h; rw [if_neg hd]
    have := ok_of_pure h; subst this
    simp [pure_ok, next_hom, setG_hom, mapVal, mapAddr]
  | addi d n imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    rw [getC_hom env σ s n a ha, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, next_hom, setG_hom, mapVal, mapAddr_plusI]
  | subi d n imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    rw [getC_hom env σ s n a ha, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, next_hom, setG_hom, mapVal, mapAddr_plusI]
  | addr d n m sh =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hz : d = sp ∨ n = sp ∨ m = sp
    · rw [if_pos hz] at h; cases h
    rw [if_neg hz] at h; rw [if_neg hz]
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    rw [getC_hom env σ s n a ha, ok_bind, getC_hom env σ s m b hb, ok_bind]
    by_cases hr : b.region = rNum
    · rw [if_pos hr] at h; rw [if_pos (show (mapAddr σ b).region = rNum from hr)]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, setG_hom, mapVal, mapAddr_plus, Lin.eval_smul]
      rfl
    · rw [if_neg hr] at h; rw [if_neg (show ¬ (mapAddr σ b).region = rNum from hr)]
      by_cases hr' : a.region = rNum ∧ sh = 0
      · rw [if_pos hr'] at h; rw [if_pos (show (mapAddr σ a).region = rNum ∧ sh = 0 from hr')]
        have := ok_of_pure h; subst this
        simp only [pure_ok, next_hom, setG_hom, mapVal, mapAddr_plus]
        rfl
      · rw [if_neg hr'] at h; cases h
  | adrp d off =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hd : d = sp
    · rw [if_pos hd] at h; cases h
    rw [if_neg hd] at h; rw [if_neg hd]
    have := ok_of_pure h; subst this
    simp [pure_ok, next_hom, setG_hom, mapVal, mapAddr]
  | addLo12 d n off =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    rw [getC_hom env σ s n a ha, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, next_hom, setG_hom, mapVal, mapAddr_plusI]
  | wop op d n m =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hd : d = sp
    · rw [if_pos hd] at h; cases h
    rw [if_neg hd] at h; rw [if_neg hd]
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    rw [getW_hom env σ s n a ha, ok_bind, getW_hom env σ s m b hb, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, next_hom, setW_hom, wop_hom]
  | rorw d n k =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hd : d = sp
    · rw [if_pos hd] at h; cases h
    rw [if_neg hd] at h; rw [if_neg hd]
    obtain ⟨a, ha, h⟩ := bind_ok h
    rw [getW_hom env σ s n a ha, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, next_hom, setW_hom, eval_ror, W32_ror]
  | rev32x d n =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hd : d = sp
    · rw [if_pos hd] at h; cases h
    rw [if_neg hd] at h; rw [if_neg hd]
    obtain ⟨p, hp, h⟩ := bind_ok h
    rw [getX_hom env σ s n p hp, ok_bind]
    have := ok_of_pure h; subst this
    simp only [pure_ok, next_hom, setG_hom, mapVal, bswap_hom]
  | cmpr n m =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hz : n = sp ∨ m = sp
    · rw [if_pos hz] at h; cases h
    rw [if_neg hz] at h; rw [if_neg hz]
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    rw [getC_hom env σ s n a ha, ok_bind, getC_hom env σ s m b hb, ok_bind]
    by_cases hr : a.region = b.region
    · rw [if_pos hr] at h; rw [if_pos (show (mapAddr σ a).region = (mapAddr σ b).region from hr)]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, setFlags_hom]
      rfl
    · rw [if_neg hr] at h; cases h
  | cmpi n imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨a, ha, h⟩ := bind_ok h
    rw [getC_hom env σ s n a ha, ok_bind]
    by_cases hr : a.region = rNum
    · rw [if_pos hr] at h; rw [if_pos (show (mapAddr σ a).region = rNum from hr)]
      have := ok_of_pure h; subst this
      simp [pure_ok, next_hom, setFlags_hom, mapAddr]
    · rw [if_neg hr] at h; cases h
  | bcc c t =>
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
  | ret =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    rw [getG_hom]
    cases hg : s.getG 30 with
    | ptr q =>
      rw [hg] at h
      obtain ⟨rq, o⟩ := q
      simp only [mapVal, mapAddr]
      by_cases h5 : rq = 5
      · subst h5
        have := ok_of_pure h; subst this
        simp only [pure_ok, Except.ok.injEq, halt_hom]
      · exfalso
        split at h
        · rename_i heq; cases heq; exact h5 rfl
        · simp [throw_eq] at h
    | num _ _ => rw [hg] at h; simp [throw_eq] at h
  -- loads / stores
  | ldr sz t n idx =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hc : isGpr sz ∧ idx.wb ∧ t = n
    · rw [if_pos hc] at h; cases h
    rw [if_neg hc] at h; rw [if_neg hc]
    obtain ⟨aw, haw, h⟩ := bind_ok h
    obtain ⟨s1, h1, h⟩ := bind_ok h
    rw [addrWB_hom env σ s n idx aw haw, ok_bind]
    dsimp only
    rw [← writeBack_hom, loadReg_hom env σ mem0s mem0c h0 s _ sz t _ s1 h1, ok_bind]
    have := ok_of_pure h; subst this
    rfl
  | str sz t n idx =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hc : isGpr sz ∧ idx.wb ∧ t = n
    · rw [if_pos hc] at h; cases h
    rw [if_neg hc] at h; rw [if_neg hc]
    obtain ⟨aw, haw, h⟩ := bind_ok h
    obtain ⟨s1, h1, h⟩ := bind_ok h
    rw [addrWB_hom env σ s n idx aw haw, ok_bind]
    dsimp only
    rw [← writeBack_hom, storeReg_hom env σ s _ sz t _ s1 h1, ok_bind]
    have := ok_of_pure h; subst this
    rfl
  | ldp sz t1 t2 n idx =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hc0 : t1 = t2
    · rw [if_pos hc0] at h; cases h
    rw [if_neg hc0] at h; rw [if_neg hc0]
    by_cases hc : isGpr sz ∧ idx.wb ∧ (t1 = n ∨ t2 = n)
    · rw [if_pos hc] at h; cases h
    rw [if_neg hc] at h; rw [if_neg hc]
    obtain ⟨aw, haw, h⟩ := bind_ok h
    obtain ⟨s1, h1, h⟩ := bind_ok h
    obtain ⟨s2, h2, h⟩ := bind_ok h
    rw [addrWB_hom env σ s n idx aw haw, ok_bind]
    dsimp only
    rw [← writeBack_hom, loadReg_hom env σ mem0s mem0c h0 s _ sz t1 _ s1 h1, ok_bind,
      ← mapAddr_plusI, loadReg_hom env σ mem0s mem0c h0 s _ sz t2 _ s2 h2, ok_bind]
    have := ok_of_pure h; subst this
    rfl
  | stp sz t1 t2 n idx =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hc : isGpr sz ∧ idx.wb ∧ (t1 = n ∨ t2 = n)
    · rw [if_pos hc] at h; cases h
    rw [if_neg hc] at h; rw [if_neg hc]
    obtain ⟨aw, haw, h⟩ := bind_ok h
    obtain ⟨s1, h1, h⟩ := bind_ok h
    obtain ⟨s2, h2, h⟩ := bind_ok h
    rw [addrWB_hom env σ s n idx aw haw, ok_bind]
    dsimp only
    rw [← writeBack_hom, storeReg_hom env σ s _ sz t1 _ s1 h1, ok_bind,
      ← mapAddr_plusI, storeReg_hom env σ s _ sz t2 _ s2 h2, ok_bind]
    have := ok_of_pure h; subst this
    rfl
  | ld1 t k n idx =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨aw, haw, h⟩ := bind_ok h
    obtain ⟨s1, h1, h⟩ := bind_ok h
    rw [addrWB_hom env σ s n idx aw haw, ok_bind]
    dsimp only
    rw [← writeBack_hom, foldlM_hom env σ (ld1Step mem0s s aw.1 t)
      (ld1Step mem0c (mapState env σ s) (mapAddr σ aw.1) t)
      (ld1Step_hom env σ mem0s mem0c h0 s aw.1 t) _ _ s1 h1, ok_bind]
    have := ok_of_pure h; subst this
    rfl
  | st1 t k n idx =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    obtain ⟨aw, haw, h⟩ := bind_ok h
    rw [addrWB_hom env σ s n idx aw haw, ok_bind]
    dsimp only at h ⊢
    have := ok_of_pure h; subst this
    rw [← writeBack_hom, ← foldl_hom env σ (st1Step s aw.1 t)
      (st1Step (mapState env σ s) (mapAddr σ aw.1) t) (st1Step_hom env σ s aw.1 t)]
    rfl
  | ld4s t e n idx =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases he : e ≥ 4
    · rw [if_pos he] at h; cases h
    rw [if_neg he] at h; rw [if_neg he]
    obtain ⟨aw, haw, h⟩ := bind_ok h
    obtain ⟨s1, h1, h⟩ := bind_ok h
    rw [addrWB_hom env σ s n idx aw haw, ok_bind]
    dsimp only
    rw [← writeBack_hom, foldlM_hom env σ (ld4Step mem0s s aw.1 t e)
      (ld4Step mem0c (mapState env σ s) (mapAddr σ aw.1) t e)
      (ld4Step_hom env σ mem0s mem0c h0 s aw.1 t e) _ _ s1 h1, ok_bind]
    have := ok_of_pure h; subst this
    rfl
  | st4s t e n idx =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases he : e ≥ 4
    · rw [if_pos he] at h; cases h
    rw [if_neg he] at h; rw [if_neg he]
    obtain ⟨aw, haw, h⟩ := bind_ok h
    rw [addrWB_hom env σ s n idx aw haw, ok_bind]
    dsimp only at h ⊢
    have := ok_of_pure h; subst this
    rw [← writeBack_hom, ← foldl_hom env σ (st4Step s aw.1 t e)
      (st4Step (mapState env σ s) (mapAddr σ aw.1) t e) (st4Step_hom env σ s aw.1 t e)]
    rfl
  -- vector
  | vop op d n m =>
    dsimp only
    rw [next_hom, setQ_hom, getQ_hom, getQ_hom, zipWith_hom env (vop op) (vop op) (vop_hom env op)]
  | movi d imm =>
    dsimp only
    simp only [next_hom, setQ_hom, List.map_cons, List.map_nil, eval_const]
    rfl
  | shl esz d n k =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases h32 : esz = 32
    · rw [if_pos h32] at h; rw [if_pos h32]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, setQ_hom, getQ_hom, List.map_map, Function.comp_def, shl32_hom]
    rw [if_neg h32] at h; rw [if_neg h32]
    by_cases h64 : esz = 64
    · rw [if_pos h64] at h; rw [if_pos h64]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, setQ_hom, getQ_hom, List.map_cons, List.map_nil, shl64_fst, shl64_snd,
        lane_hom]
    · rw [if_neg h64] at h; cases h
  | ushr esz d n k =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases h32 : esz = 32
    · rw [if_pos h32] at h; rw [if_pos h32]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, setQ_hom, getQ_hom, List.map_map, Function.comp_def, shr32_hom]
    rw [if_neg h32] at h; rw [if_neg h32]
    by_cases h64 : esz = 64
    · rw [if_pos h64] at h; rw [if_pos h64]
      have := ok_of_pure h; subst this
      simp only [pure_ok, next_hom, setQ_hom, getQ_hom, List.map_cons, List.map_nil, shr64_fst, shr64_snd,
        lane_hom]
    · rw [if_neg h64] at h; cases h
  | ext d n m imm =>
    dsimp only at hne hA ⊢
    apply ok_wrap env σ s _ _ hne
    intro s' h
    by_cases hi : imm ≥ 16
    · rw [if_pos hi] at h; cases h
    rw [if_neg hi] at h; rw [if_neg hi]
    have := ok_of_pure h; subst this
    simp only [pure_ok, next_hom, setQ_hom, getQ_hom, extL_hom]
  | zip1 d n m =>
    dsimp only
    simp only [next_hom, setQ_hom, getQ_hom, List.map_cons, List.map_nil, lane_hom]
  | zip2 d n m =>
    dsimp only
    simp only [next_hom, setQ_hom, getQ_hom, List.map_cons, List.map_nil, lane_hom]
  | uzp1 d n m =>
    dsimp only
    simp only [next_hom, setQ_hom, getQ_hom, List.map_cons, List.map_nil, lane_hom]
  | xtn d n =>
    dsimp only
    simp only [next_hom, setD_hom, getQ_hom, List.map_cons, List.map_nil, lane_hom]
  | rev32 d n =>
    dsimp only
    simp only [next_hom, setQ_hom, getQ_hom, List.map_map, Function.comp_def, bswap_hom]
  | sha256h d n m =>
    dsimp only
    simp only [next_hom, setQ_hom, getQ_hom, sha256hash_hom]
  | sha256h2 d n m =>
    dsimp only
    simp only [next_hom, setQ_hom, getQ_hom, sha256hash_hom]
  | sha256su0 d n =>
    dsimp only
    simp only [next_hom, setQ_hom, getQ_hom, su0_hom]
  | sha256su1 d n m =>
    dsimp only
    simp only [next_hom, setQ_hom, getQ_hom, su1_hom]

end Exec

end Hashtree.Asm.Arm
