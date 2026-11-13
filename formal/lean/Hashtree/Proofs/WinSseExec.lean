import Hashtree.Proofs.WinSseShift

/-!
## The stack-memory shift, one instruction

`exec_sh` transports a single instruction from the linux state `s` to the shifted windows state
`shSt μ s`, where the ambient memory is related by `mem0w (shAddr μ a) = shCell μ (mem0l a)`.

Unlike the `rsp`-lowering engine of `WinFrameStack`, the shift moves *all* stack addresses and
payloads, so the recorded flags of a 64-bit `alu`/`sub`/`cmp`/`test` would differ if an operand
were a stack pointer (the model stores only the offsets).  The hypothesis `hns` rules this out
for the register file: the only stack pointer is `rsp` itself, and `frameSafe` keeps `rsp` out of
every operand.  (`rsp`-relative *memory* operands are fine: `effAddr_sh` shifts the address and
`loadLane_sh`/`storeLane_sh` shift the payload.)
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Hashtree.Asm.X86
open Hashtree.Asm

/-! ### No stack pointer in the register file -/

/-- A value that is not a pointer into the stack region. -/
def NoStackVal (v : Val W32 Int) : Prop := ∀ a, v = .ptr a → a.region ≠ rStack

theorem shVal_id (μ : Int) (v : Val W32 Int) (h : NoStackVal v) : shVal μ v = v := by
  cases v with
  | num lo hi => rfl
  | ptr a =>
    rw [shVal_ptr]
    have ha : a.region ≠ rStack := h a rfl
    rw [shAddr_of_ne μ a ha]

theorem getG_sh_id (μ : Int) (s : State W32 Int) (j : Nat)
    (hns : ∀ i, i ≠ 4 → NoStackVal (s.getG i)) (hj : j ≠ 4) :
    (shSt μ s).getG j = s.getG j := by
  rw [getG_sh]
  exact shVal_id μ (s.getG j) (hns j hj)

/-- The region of a successful `gCtl` read of a safe operand is not the stack. -/
theorem gCtl_ok_region (s : State W32 Int) (src : GSrc)
    (hns : ∀ i, i ≠ 4 → NoStackVal (s.getG i)) (h : gsSafe src)
    (a : Addr Int) (ha : gCtl s src = .ok a) : a.region ≠ rStack := by
  cases src with
  | reg r =>
    have hr : r ≠ 4 := h
    cases hg : s.getG r with
    | num lo hi =>
      simp only [gCtl, hg] at ha
      cases h1 : Lane.asConst lo with
      | none => exact absurd ha (by simp [h1])
      | some l =>
        cases h2 : Lane.asConst hi with
        | none => exact absurd ha (by simp [h1, h2])
        | some hh =>
          simp only [h1, h2] at ha
          injection ha with he
          subst he
          show (rNum : Region) ≠ rStack
          decide
    | ptr p =>
      have hp : p.region ≠ rStack := hns r hr p hg
      simp only [gCtl, hg] at ha
      injection ha with he
      subst he
      exact hp
  | imm v =>
    simp only [gCtl] at ha
    injection ha with he
    subst he
    show (rNum : Region) ≠ rStack
    decide
  | mem m =>
    simp only [gCtl] at ha
    exact absurd ha (by simp)

/-- `gCtl` commutes with the stack shift for safe operands, under `NoStackVal`. -/
theorem gCtl_sh_id (μ : Int) (s : State W32 Int) (src : GSrc)
    (hns : ∀ i, i ≠ 4 → NoStackVal (s.getG i)) (h : gsSafe src) :
    gCtl (shSt μ s) src = gCtl s src := by
  rw [gCtl_sh]
  cases src with
  | reg r =>
    cases hg : s.getG r with
    | num lo hi =>
      cases h1 : Lane.asConst lo with
      | none => simp only [gCtl, hg, h1, emap_throw]
      | some l =>
        cases h2 : Lane.asConst hi with
        | none => simp only [gCtl, hg, h1, h2, emap_throw]
        | some hh =>
          simp only [gCtl, hg, h1, h2, emap_pure]
          rw [shAddr_of_ne μ _ (show (rNum : Region) ≠ rStack by decide)]
    | ptr p =>
      have hp : p.region ≠ rStack := hns r h p hg
      simp only [gCtl, hg, emap_pure]
      rw [shAddr_of_ne μ p hp]
  | imm v =>
    simp only [gCtl, emap_pure]
    rw [shAddr_of_ne μ _ (show (rNum : Region) ≠ rStack by decide)]
  | mem m => simp only [gCtl, emap_throw]

/-! ### State-field commutation for the shift -/

theorem setVec_sh (μ : Int) (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) :
    setVec (shSt μ s) vex w d v = shSt μ (setVec s vex w d v) := by
  simp only [setVec, getV_sh, setV_sh]

/-- Writing a non-stack pointer is equivariant. -/
theorem setG_ptr_sh (μ : Int) (s : State W32 Int) (d : Nat) (a : Addr Int)
    (ha : a.region ≠ rStack) :
    (shSt μ s).setG d (.ptr a) = shSt μ (s.setG d (.ptr a)) := by
  rw [← setG_sh μ s d (.ptr a), shVal_ptr, shAddr_of_ne μ a ha]

/-! ### `okOr` plumbing -/

theorem okOr_pure_sh (μ : Int) (s : State W32 Int) (X : State W32 Int) :
    okOr (shSt μ s) (pure (shSt μ X)) = shSt μ (okOr s (pure X)) := by
  rw [okOr_pure, okOr_pure]

theorem okOr_bind_sh (μ : Int) (s : State W32 Int) {β : Type} (m : Except String β)
    (f : β → State W32 Int) :
    okOr (shSt μ s) (m >>= fun b => pure (shSt μ (f b)))
      = shSt μ (okOr s (m >>= fun b => pure (f b))) := by
  cases m with
  | error e => simp only [bind_error_eq, okOr_error, fail_sh]
  | ok b => simp only [bind_ok_eq, okOr_pure]

theorem okOr_bind2_sh (μ : Int) (s : State W32 Int) {β γ' : Type} (m : Except String β)
    (n : β → Except String γ') (f : β → γ' → State W32 Int) :
    okOr (shSt μ s) (m >>= fun a => n a >>= fun b => pure (shSt μ (f a b)))
      = shSt μ (okOr s (m >>= fun a => n a >>= fun b => pure (f a b))) := by
  cases m with
  | error e => simp only [bind_error_eq, okOr_error, fail_sh]
  | ok a =>
    simp only [bind_ok_eq]
    exact okOr_bind_sh μ s (n a) (f a)

theorem okOr_throw_sh (μ : Int) (s : State W32 Int) (msg : String) :
    okOr (shSt μ s) (throw msg) = shSt μ (okOr s (throw msg)) := by
  show okOr (shSt μ s) (.error msg) = shSt μ (okOr s (.error msg))
  simp only [okOr_error, fail_sh]

theorem okOr_bind_err_sh (μ : Int) (s : State W32 Int) {β : Type} (m : Except String β)
    (e : String) :
    okOr (shSt μ s) (m >>= fun _ => throw e) = shSt μ (okOr s (m >>= fun _ => throw e)) := by
  cases m with
  | error e' => simp only [bind_error_eq, okOr_error, fail_sh]
  | ok b => simpa only [bind_ok_eq] using okOr_throw_sh μ s e

/-! ### The per-instruction lemma -/

section ExecSh
variable {ro : Region} {mem0w mem0l : Addr Int → Cell W32 Int} {orc : Nat → Bool}

theorem exec_sh (μ : Int) (hro : ro ≠ rStack)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a))
    (i : Instr) (s : State W32 Int)
    (hns : ∀ j, j ≠ 4 → NoStackVal (s.getG j)) (hok : frameSafe i) :
    exec ro mem0w orc i (shSt μ s) = shSt μ (exec ro mem0l orc i s) := by
  cases hs : s.halted with
  | true => simp only [exec, shSt_halted, hs, ite_true]
  | false =>
  simp only [exec, shSt_halted, hs, Bool.false_eq_true, ite_false]
  cases i with
  | nop =>
    dsimp only
    simp only [next_sh]
  | vop op vex w dv s1 s2 =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    rw [readVSrc_sh μ ro hro mem0w mem0l h0 s w s2]
    exact okOr_bind_sh μ s _ _
  | vshift k vex w dv src n =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | vshiftq vex w dv src n =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | vror w dv src n =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | vtern w dv s1 s2 imm =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | vload vex w dv src =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    rw [readVSrc_sh μ ro hro mem0w mem0l h0 s w src]
    exact okOr_bind_sh μ s _ _
  | vstore w m src =>
    dsimp only
    rw [effAddr_sh μ ro hro s m]
    simp only [emap_bind, storeLanes_sh, getV_sh, next_sh]
    exact okOr_bind_sh μ s _ _
  | pshufd vex dv src imm =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | pshufb vex w dv src mask =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_bind_sh μ s _ _
  | palignr vex dv s1 s2 imm =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | pblendw dv src imm =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | shufps w dv s1 s2 imm =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | perm2f128 dv s1 s2 imm =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | inserti128 dv s1 m imm =>
    dsimp only
    rw [effAddr_sh μ ro hro s m]
    simp only [emap_bind, loadLanes_sh μ mem0w mem0l h0, getV_sh, setVec_sh, next_sh]
    exact okOr_bind2_sh μ s _ _ _
  | inserti64x4 dv s1 m imm =>
    dsimp only
    rw [effAddr_sh μ ro hro s m]
    simp only [emap_bind, loadLanes_sh μ mem0w mem0l h0, getV_sh, setVec_sh, next_sh]
    exact okOr_bind2_sh μ s _ _ _
  | permi2d dv s1 s2 =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_bind_sh μ s _ _
  | permi2q dv s1 s2 =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_bind_sh μ s _ _
  | sha256rnds2 dv src =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | sha256msg1 dv src =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | sha256msg2 dv src =>
    dsimp only
    simp only [getV_sh, setVec_sh, next_sh]
    exact okOr_pure_sh μ s _
  | mov w dn src =>
    dsimp only
    obtain ⟨hd, hsok⟩ := hok
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases src with
      | reg r =>
        dsimp only
        simp only [getG_sh]
        rw [setG_sh, next_sh]
        exact okOr_pure_sh μ s _
      | imm v =>
        dsimp only
        rw [setG_ptr_sh μ s dn ⟨rNum, Ctl.ofInt v⟩ (show (rNum : Region) ≠ rStack by decide),
          next_sh]
        exact okOr_pure_sh μ s _
      | mem m =>
        dsimp only
        rw [effAddr_sh μ ro hro s m]
        simp only [emap_bind, loadVal_sh μ mem0w mem0l h0, setG_sh, next_sh]
        exact okOr_bind2_sh μ s _ _ _
    · simp only [if_neg hw]
      rw [gData32_sh μ ro hro mem0w mem0l h0 s src]
      simp only [setData32_sh, next_sh]
      exact okOr_bind_sh μ s _ _
  | movst w m src =>
    dsimp only
    obtain ⟨hm, hsrc⟩ := hok
    rw [effAddr_sh μ ro hro s m]
    by_cases hw : w = 64
    · simp only [if_pos hw, getG_sh]
      simp only [emap_bind, storeVal_sh, next_sh]
      exact okOr_bind_sh μ s _ _
    · simp only [if_neg hw, getG_sh]
      cases hg : s.getG src with
      | num lo hi =>
        simp only [shVal_num]
        simp only [emap_bind, storeLane_sh, next_sh]
        exact okOr_bind_sh μ s _ _
      | ptr q =>
        simp only [shVal_ptr, emap_bind]
        exact okOr_bind_err_sh μ s _ _
  | alu op w dn src =>
    dsimp only
    obtain ⟨hd, hsok⟩ := hok
    by_cases hw : w = 64
    · simp only [if_pos hw]
      by_cases hz : op = .xor ∧ src = .reg dn
      · simp only [if_pos hz]
        rw [setG_ptr_sh μ s dn ⟨rNum, Ctl.ofInt 0⟩ (show (rNum : Region) ≠ rStack by decide),
          clearFlags_sh, next_sh]
        exact okOr_pure_sh μ s _
      · simp only [if_neg hz]
        rw [gCtl_sh_id μ s (.reg dn) hns hd]
        rw [gCtl_sh_id μ s src hns hsok]
        cases ha : gCtl s (.reg dn) with
        | error e => simp only [bind_error_eq, okOr_error, fail_sh]
        | ok a =>
          cases hb : gCtl s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, fail_sh]
          | ok b =>
            simp only [bind_ok_eq]
            cases op with
            | add =>
              dsimp only
              by_cases hc : b.region = rNum ∨ a.region = rNum
              · simp only [if_pos hc]
                have hans : a.region ≠ rStack := gCtl_ok_region s (.reg dn) hns hd a ha
                have hbns : b.region ≠ rStack := gCtl_ok_region s src hns hsok b hb
                have hr : (⟨if b.region = rNum then a.region else b.region,
                    Ctl.add a.off b.off⟩ : Addr Int).region ≠ rStack := by
                  dsimp only
                  split <;> assumption
                rw [setG_ptr_sh μ s dn _ hr, setFlags_sh, next_sh]
                exact okOr_pure_sh μ s _
              · simp only [if_neg hc]
                exact okOr_throw_sh μ s _
            | xor =>
              dsimp only
              exact okOr_throw_sh μ s _
            | and =>
              dsimp only
              cases hx2 : Ctl.asInt a.off with
              | none => exact okOr_throw_sh μ s _
              | some x =>
                cases hy2 : Ctl.asInt b.off with
                | none => exact okOr_throw_sh μ s _
                | some y =>
                  dsimp only
                  cases hr2 : andInt x y with
                  | none => exact okOr_throw_sh μ s _
                  | some r =>
                    by_cases hc : b.region = rNum ∧ (a.region = rNum ∨ (-64 ≤ y ∧ y < 0))
                    · simp only [if_pos hc]
                      have hans : a.region ≠ rStack := gCtl_ok_region s (.reg dn) hns hd a ha
                      have hr : (⟨a.region, Ctl.ofInt r⟩ : Addr Int).region ≠ rStack := hans
                      rw [setG_ptr_sh μ s dn _ hr, clearFlags_sh, next_sh]
                      exact okOr_pure_sh μ s _
                    · simp only [if_neg hc]
                      exact okOr_throw_sh μ s _
            | or =>
              dsimp only
              exact okOr_throw_sh μ s _
    · simp only [if_neg hw]
      by_cases hz : op = .xor ∧ src = .reg dn
      · simp only [if_pos hz]
        rw [setData32_sh, clearFlags_sh, next_sh]
        exact okOr_pure_sh μ s _
      · simp only [if_neg hz]
        rw [gData32_sh μ ro hro mem0w mem0l h0 s src]
        rw [gData32_sh μ ro hro mem0w mem0l h0 s (.reg dn)]
        cases ha : gData32 ro mem0l s (.reg dn) with
        | error e => simp only [bind_error_eq, okOr_error, fail_sh]
        | ok a =>
          cases hb : gData32 ro mem0l s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, fail_sh]
          | ok b =>
            simp only [bind_ok_eq, setData32_sh, clearFlags_sh, next_sh]
            exact okOr_pure_sh μ s _
  | sub w dn src =>
    dsimp only
    obtain ⟨hd, hsok⟩ := hok
    by_cases hw : w = 64
    · simp only [if_pos hw]
      rw [gCtl_sh_id μ s (.reg dn) hns hd]
      rw [gCtl_sh_id μ s src hns hsok]
      cases ha : gCtl s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, fail_sh]
      | ok a =>
        cases hb : gCtl s src with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, fail_sh]
        | ok b =>
          simp only [bind_ok_eq]
          by_cases hc : b.region = rNum
          · simp only [if_pos hc]
            have hans : a.region ≠ rStack := gCtl_ok_region s (.reg dn) hns hd a ha
            have hr : (a.plus (Ctl.smul (-1) b.off)).region ≠ rStack := by
              dsimp only [Addr.plus]
              exact hans
            rw [setG_ptr_sh μ s dn _ hr, setFlags_sh, next_sh]
            exact okOr_pure_sh μ s _
          · simp only [if_neg hc]
            exact okOr_throw_sh μ s _
    · simp only [if_neg hw]
      exact okOr_throw_sh μ s _
  | lea dn m =>
    dsimp only
    obtain ⟨hd, hm⟩ := hok
    rw [effAddr_sh μ ro hro s m]
    simp only [emap_bind, ← shVal_ptr, setG_sh, next_sh]
    exact okOr_bind_sh μ s _ _
  | ror w dn n =>
    dsimp only
    have hd : dn ≠ 4 := hok
    by_cases hw : w = 32
    · simp only [if_pos hw]
      rw [gData32_sh μ ro hro mem0w mem0l h0 s (.reg dn)]
      cases ha : gData32 ro mem0l s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, fail_sh]
      | ok a =>
        simp only [bind_ok_eq, setData32_sh, clearFlags_sh, next_sh]
        exact okOr_pure_sh μ s _
    · simp only [if_neg hw]
      exact okOr_throw_sh μ s _
  | shld w dn src n =>
    dsimp only
    obtain ⟨hd, hs⟩ := hok
    by_cases hw : w = 32
    · simp only [if_pos hw]
      rw [gData32_sh μ ro hro mem0w mem0l h0 s (.reg dn)]
      rw [gData32_sh μ ro hro mem0w mem0l h0 s (.reg src)]
      cases ha : gData32 ro mem0l s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, fail_sh]
      | ok a =>
        cases hb : gData32 ro mem0l s (.reg src) with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, fail_sh]
        | ok b =>
          simp only [bind_ok_eq, setData32_sh, clearFlags_sh, next_sh]
          exact okOr_pure_sh μ s _
    · simp only [if_neg hw]
      exact okOr_throw_sh μ s _
  | shl w dn n =>
    dsimp only
    have hd : dn ≠ 4 := hok
    by_cases hw : w = 64
    · simp only [if_pos hw]
      rw [gCtl_sh_id μ s (.reg dn) hns hd]
      cases ha : gCtl s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, fail_sh]
      | ok a =>
        simp only [bind_ok_eq]
        by_cases hr : a.region = rNum
        · simp only [if_pos hr]
          have hnr : (⟨rNum, Ctl.smul (2 ^ (n % 64)) a.off⟩ : Addr Int).region ≠ rStack :=
            show (rNum : Region) ≠ rStack by decide
          rw [setG_ptr_sh μ s dn _ hnr, clearFlags_sh, next_sh]
          exact okOr_pure_sh μ s _
        · simp only [if_neg hr]
          exact okOr_throw_sh μ s _
    · simp only [if_neg hw]
      rw [gData32_sh μ ro hro mem0w mem0l h0 s (.reg dn)]
      cases ha : gData32 ro mem0l s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, fail_sh]
      | ok a =>
        simp only [bind_ok_eq, setData32_sh, clearFlags_sh, next_sh]
        exact okOr_pure_sh μ s _
  | bswap w dn =>
    dsimp only
    have hd : dn ≠ 4 := hok
    by_cases hw : w = 32
    · simp only [if_pos hw]
      rw [gData32_sh μ ro hro mem0w mem0l h0 s (.reg dn)]
      cases ha : gData32 ro mem0l s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, fail_sh]
      | ok a =>
        simp only [bind_ok_eq, setData32_sh, next_sh]
        exact okOr_pure_sh μ s _
    · simp only [if_neg hw]
      exact okOr_throw_sh μ s _
  | push r =>
    dsimp only
    exact hok.elim
  | pop r =>
    dsimp only
    exact hok.elim
  | cmp w a b =>
    dsimp only
    obtain ⟨ha, hsok⟩ := hok
    by_cases hw : w = 64
    · simp only [if_pos hw]
      rw [gCtl_sh_id μ s (.reg a) hns ha]
      rw [gCtl_sh_id μ s b hns hsok]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, fail_sh]
      | ok x =>
        cases hy : gCtl s b with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, fail_sh]
        | ok y =>
          simp only [bind_ok_eq]
          by_cases hc : y.region = rNum ∨ y.region = x.region
          · simp only [if_pos hc, setFlags_sh, next_sh]
            exact okOr_pure_sh μ s _
          · simp only [if_neg hc]
            exact okOr_throw_sh μ s _
    · simp only [if_neg hw]
      exact okOr_throw_sh μ s _
  | test w a b =>
    dsimp only
    obtain ⟨ha, hb⟩ := hok
    by_cases hc : w = 64 ∧ a = b
    · simp only [if_pos hc]
      rw [gCtl_sh_id μ s (.reg a) hns ha]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, fail_sh]
      | ok x =>
        simp only [bind_ok_eq]
        by_cases hr : x.region = rNum
        · simp only [if_pos hr, setFlags_sh, next_sh]
          exact okOr_pure_sh μ s _
        · simp only [if_neg hr]
          exact okOr_throw_sh μ s _
    · simp only [if_neg hc]
      exact okOr_throw_sh μ s _
  | jcc c t =>
    dsimp only
    simp only [shSt_flags]
    cases hf : s.flags with
    | none => exact okOr_throw_sh μ s _
    | some q =>
      obtain ⟨a, b⟩ := q
      simp only [okOr_pure]
      exact branch_sh μ orc s (ccCond c a b) t
  | jmp t =>
    dsimp only
    rfl
  | jccTail c name =>
    dsimp only
    exact hok.elim
  | jmpTail name =>
    dsimp only
    exact hok.elim
  | ret =>
    dsimp only
    exact hok.elim

end ExecSh

end Hashtree.Asm.X86
