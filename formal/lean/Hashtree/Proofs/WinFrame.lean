import Hashtree.Proofs.Win64

/-!
# R5: the program-counter shift engine for the windows kernels

The windows streams are the linux streams with a Win64 prologue and epilogue and the shared
kernel body moved to a different instruction index: linux body instruction `j` sits at windows
index `p + j`, and every relative jump target is shifted by `p`.  This module proves the
program-counter half of the transfer between the two runs:

* `exec_shiftPc` -- one instruction's execution is equivariant under a pc shift, provided the
  executed instruction is the `shiftTgt p` translation of the linux instruction;
* `run_shift` -- an `n`-step windows run from a pc-shifted state is the pc shift of the `n`-step
  linux run.

The pc shift is orthogonal to the stack frame: none of these proofs looks at `rsp`, at the
displacements of memory operands, or at the initial memory, so this layer composes with the
stack-frame layer.  The single instruction that does not transfer is `jccTail`: its sentinel
target `1000000000` is not shifted, so the sentinel test would compare different program
counters.  `trOk` excludes it; the shared bodies of the shipped kernels contain none (the
tail calls of the larger kernels sit in their prologues, outside the transferred body region).
-/

open Hashtree.Asm Hashtree.Asm.X86
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Hashtree.Asm.X86

/-! ## Shifting the program counter -/

section ShiftState
variable {α γ : Type} [Lane α] [Ctl γ] [AddrEq γ] [Inhabited α] [Inhabited γ]

/-- A state with the program counter shifted by `p`. -/
abbrev shiftPc (p : Nat) (s : State α γ) : State α γ := { s with pc := s.pc + p }

/-! The state projections and constructors commute with the shift.  The lemmas are stated in the
direction the transfer proof uses: a constructor of the shifted state is written as the shift of
the constructor of the original state, so both sides of the execution equation normalise to the
same shape. -/

@[simp] theorem shiftPc_gpr (p : Nat) (s : State α γ) : (shiftPc p s).gpr = s.gpr := rfl
@[simp] theorem shiftPc_vr (p : Nat) (s : State α γ) : (shiftPc p s).vr = s.vr := rfl
@[simp] theorem shiftPc_flags (p : Nat) (s : State α γ) : (shiftPc p s).flags = s.flags := rfl
@[simp] theorem shiftPc_mem (p : Nat) (s : State α γ) : (shiftPc p s).mem = s.mem := rfl
@[simp] theorem shiftPc_pc (p : Nat) (s : State α γ) : (shiftPc p s).pc = s.pc + p := rfl
@[simp] theorem shiftPc_halted (p : Nat) (s : State α γ) : (shiftPc p s).halted = s.halted := rfl
@[simp] theorem shiftPc_tail (p : Nat) (s : State α γ) : (shiftPc p s).tail = s.tail := rfl
@[simp] theorem shiftPc_err (p : Nat) (s : State α γ) : (shiftPc p s).err = s.err := rfl
@[simp] theorem shiftPc_assume (p : Nat) (s : State α γ) : (shiftPc p s).assume = s.assume := rfl
@[simp] theorem shiftPc_getG (p : Nat) (s : State α γ) (i : Nat) : (shiftPc p s).getG i = s.getG i := rfl
@[simp] theorem shiftPc_getV (p : Nat) (s : State α γ) (i : Nat) : (shiftPc p s).getV i = s.getV i := rfl

@[simp] theorem shiftPc_setG (p : Nat) (s : State α γ) (i : Nat) (v : Val α γ) :
    (shiftPc p s).setG i v = shiftPc p (s.setG i v) := rfl
@[simp] theorem shiftPc_setV (p : Nat) (s : State α γ) (i : Nat) (v : List α) :
    (shiftPc p s).setV i v = shiftPc p (s.setV i v) := rfl
@[simp] theorem shiftPc_setVec (p : Nat) (s : State α γ) (vex : Bool) (w d : Nat) (v : List α) :
    setVec (shiftPc p s) vex w d v = shiftPc p (setVec s vex w d v) := by
  simp only [setVec, shiftPc_getV, shiftPc_setV]
@[simp] theorem shiftPc_next (p : Nat) (s : State α γ) : (shiftPc p s).next = shiftPc p s.next := by
  simp only [State.next, shiftPc]
  congr 1
  omega
@[simp] theorem shiftPc_fail (p : Nat) (s : State α γ) (m : String) :
    (shiftPc p s).fail m = shiftPc p (s.fail m) := by
  rw [State.fail, State.fail]
  by_cases h : s.err.isSome <;> simp [shiftPc, h]
@[simp] theorem shiftPc_clearFlags (p : Nat) (s : State α γ) :
    clearFlags (shiftPc p s) = shiftPc p (clearFlags s) := rfl
@[simp] theorem shiftPc_setFlags (p : Nat) (s : State α γ) (a b : γ) :
    setFlags (shiftPc p s) a b = shiftPc p (setFlags s a b) := rfl
@[simp] theorem shiftPc_halt (p : Nat) (s : State α γ) :
    halt (shiftPc p s) = shiftPc p (halt s) := rfl
@[simp] theorem shiftPc_setData32 (p : Nat) (s : State α γ) (d : Nat) (x : α) :
    setData32 (shiftPc p s) d x = shiftPc p (setData32 s d x) := rfl
@[simp] theorem shiftPc_storeLane (p : Nat) (s : State α γ) (a : Addr γ) (x : α) :
    storeLane (shiftPc p s) a x = shiftPc p (storeLane s a x) := rfl
@[simp] theorem shiftPc_storeLanes (p : Nat) (s : State α γ) (a : Addr γ) (v : List α) :
    storeLanes (shiftPc p s) a v = shiftPc p (storeLanes s a v) := by
  induction v generalizing s a with
  | nil => rfl
  | cons x xs ih => simp only [storeLanes]; rw [shiftPc_storeLane, ih]
@[simp] theorem shiftPc_storeVal (p : Nat) (s : State α γ) (a : Addr γ) (v : Val α γ) :
    storeVal (shiftPc p s) a v = shiftPc p (storeVal s a v) := by
  cases v with
  | num lo hi => simp only [storeVal, shiftPc_storeLane]
  | ptr q => rfl

/-- A decided branch commutes with the pc shift; the target moves with the shifted program. -/
theorem shiftPc_branch (p : Nat) (s : State α γ) (orc : Nat → Bool) (c : Cond γ) (t : Nat)
    (hc : c.decideC.isSome = true) :
    shiftPc p (s.branch orc c t) = (shiftPc p s).branch orc c (t + p) := by
  simp only [State.branch, shiftPc]
  simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false, Option.isNone_iff_eq_none]
  cases h : c.decideC with
  | none => rw [h] at hc; simp at hc
  | some b => simp only [h]; split <;> simp [State.next, Nat.add_right_comm]

end ShiftState

/-! ## Operands, addresses and cells are pc-invariant -/

section ShiftOps
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

theorem readCell_shift (p : Nat) (s : State W32 Int) (a : Addr Int) :
    readCell mem0 (shiftPc p s) a = readCell mem0 s a := by
  simp only [readCell, shiftPc_mem]

theorem loadLane_shift (p : Nat) (s : State W32 Int) (a : Addr Int) :
    loadLane mem0 (shiftPc p s) a = loadLane mem0 s a := by
  simp only [loadLane, readCell_shift]

theorem loadLanes_shift : ∀ (p : Nat) (s : State W32 Int) (a : Addr Int) (n : Nat),
    loadLanes mem0 (shiftPc p s) a n = loadLanes mem0 s a n
  | p, s, a, 0 => rfl
  | p, s, a, n + 1 => by
    simp only [loadLanes]
    rw [loadLane_shift, loadLanes_shift p s (a.plusI 4) n]

theorem pbRest_shift : ∀ (p : Nat) (s : State W32 Int) (q a : Addr Int) (n k : Nat),
    pbRest mem0 (shiftPc p s) q a n k = pbRest mem0 s q a n k
  | p, s, q, a, 0, k => rfl
  | p, s, q, a, n + 1, k => by
    simp only [pbRest, readCell_shift, pbRest_shift p s q a n (k + 1)]

theorem loadVal_shift (p : Nat) (s : State W32 Int) (a : Addr Int) :
    loadVal mem0 (shiftPc p s) a = loadVal mem0 s a := by
  simp only [loadVal, readCell_shift, pbRest_shift, loadLane_shift]

theorem baseAddr_shift (p : Nat) (s : State W32 Int) (m : MemRef) :
    baseAddr ro (shiftPc p s) m = baseAddr ro s m := by
  simp only [baseAddr, regPtr, shiftPc_getG]

theorem effAddr_shift (p : Nat) (s : State W32 Int) (m : MemRef) :
    effAddr ro (shiftPc p s) m = effAddr ro s m := by
  simp only [effAddr, baseAddr_shift, shiftPc_getG]

theorem readVSrc_shift (p : Nat) (s : State W32 Int) (w : Nat) (src : VSrc) :
    readVSrc ro mem0 (shiftPc p s) w src = readVSrc ro mem0 s w src := by
  cases src with
  | reg i => simp only [readVSrc, shiftPc_getV]
  | mem m => simp only [readVSrc, effAddr_shift, loadLanes_shift]

theorem gCtl_shift (p : Nat) (s : State W32 Int) (src : GSrc) :
    gCtl (shiftPc p s) src = gCtl s src := by
  cases src with
  | reg i => simp only [gCtl, shiftPc_getG]
  | imm v => rfl
  | mem m => rfl

theorem gData32_shift (p : Nat) (s : State W32 Int) (src : GSrc) :
    gData32 ro mem0 (shiftPc p s) src = gData32 ro mem0 s src := by
  cases src with
  | reg i => simp only [gData32, shiftPc_getG]
  | imm v => rfl
  | mem m => simp only [gData32, effAddr_shift, loadLane_shift]

/-! ### `okOr` helpers -/

theorem okOr_pure_shift (p : Nat) (s : State W32 Int) (X : State W32 Int) :
    okOr (shiftPc p s) (pure (shiftPc p X)) = shiftPc p (okOr s (pure X)) := by
  rw [okOr_pure, okOr_pure]

theorem okOr_bind_shift (p : Nat) (s : State W32 Int) {β : Type} (m : Except String β)
    (f : β → State W32 Int) :
    okOr (shiftPc p s) (m >>= fun b => pure (shiftPc p (f b)))
      = shiftPc p (okOr s (m >>= fun b => pure (f b))) := by
  cases m with
  | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
  | ok b => simp only [bind_ok_eq, okOr_pure]

theorem okOr_bind2_shift (p : Nat) (s : State W32 Int) {β δ : Type} (m : Except String β)
    (n : β → Except String δ) (f : β → δ → State W32 Int) :
    okOr (shiftPc p s) (m >>= fun a => n a >>= fun b => pure (shiftPc p (f a b)))
      = shiftPc p (okOr s (m >>= fun a => n a >>= fun b => pure (f a b))) := by
  cases m with
  | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
  | ok a =>
    simp only [bind_ok_eq]
    exact okOr_bind_shift p s (n a) (f a)

theorem okOr_bind_err_shift (p : Nat) (s : State W32 Int) {β : Type} (m : Except String β)
    (e : String) :
    okOr (shiftPc p s) (m >>= fun _ => (Except.error e : Except String (State W32 Int)))
      = shiftPc p (okOr s (m >>= fun _ => (Except.error e))) := by
  cases m with
  | error e' => simp only [bind_error_eq, okOr_error, shiftPc_fail]
  | ok b => simp only [bind_ok_eq, okOr_error, shiftPc_fail]

theorem okOr_throw_shift (p : Nat) (s : State W32 Int) (msg : String) :
    okOr (shiftPc p s) (throw msg) = shiftPc p (okOr s (throw msg)) := by
  show okOr (shiftPc p s) (.error msg) = shiftPc p (okOr s (.error msg))
  simp only [okOr_error, shiftPc_fail]

/-! ## The instruction translation and the transferred instructions -/

/-- The windows translation of a linux body instruction: relative jump targets move with the
body. -/
def shiftTgt (p : Nat) : Instr → Instr
  | .jcc c t => .jcc c (t + p)
  | .jmp t => .jmp (t + p)
  | i => i

/-- The instructions the pc transfer applies to.  `jccTail` branches to the sentinel
`1000000000` and then restores `pc`, so the sentinel test is not pc-invariant. -/
def trOk : Instr → Prop
  | .jccTail _ _ => False
  | _ => True

/-- Every integer condition is decided, so the oracle is never consulted and the branch
condition is the same under the shift. -/
theorem decideC_ccCond (c : CC) (a b : Int) : (ccCond c a b).decideC.isSome = true := by
  cases c <;> rfl
theorem exec_shiftPc (p : Nat) (i : Instr) (s : State W32 Int) (hok : trOk i) :
    exec ro mem0 orc (shiftTgt p i) (shiftPc p s) = shiftPc p (exec ro mem0 orc i s) := by
  cases hs : s.halted with
  | true => simp only [exec, hs, ite_true, shiftPc_halted]
  | false =>
  simp only [exec, hs, shiftPc_halted, Bool.false_eq_true, ite_false]
  cases i with
  | nop => simp only [shiftTgt, shiftPc_next]
  | vop op vex w d s1 s2 =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    rw [readVSrc_shift p s w s2]
    exact okOr_bind_shift p s _ _
  | vshift k vex w d src n =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | vshiftq vex w d src n =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | vror w d src n =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | vtern w d s1 s2 imm =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | vload vex w d src =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    rw [readVSrc_shift p s w src]
    exact okOr_bind_shift p s _ _
  | vstore w m src =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_next,
      effAddr_shift p s m, shiftPc_storeLanes]
    exact okOr_bind_shift p s _ _
  | pshufd vex d src imm =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | pshufb vex w d src mask =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_bind_shift p s _ _
  | palignr vex d s1 s2 imm =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | pblendw d src imm =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | shufps w d s1 s2 imm =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | perm2f128 d s1 s2 imm =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | inserti128 d s1 m imm =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next,
      effAddr_shift p s m, loadLanes_shift]
    exact okOr_bind2_shift p s _ _ _
  | inserti64x4 d s1 m imm =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next,
      effAddr_shift p s m, loadLanes_shift]
    exact okOr_bind2_shift p s _ _ _
  | permi2d d s1 s2 =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_bind_shift p s _ _
  | permi2q d s1 s2 =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_bind_shift p s _ _
  | sha256rnds2 d src =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | sha256msg1 d src =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | sha256msg2 d src =>
    simp only [shiftTgt, shiftPc_getV, shiftPc_setVec, shiftPc_next]
    exact okOr_pure_shift p s _
  | mov w d src =>
    simp only [shiftTgt]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases src with
      | reg r =>
        simp only [shiftTgt, shiftPc_next, shiftPc_getG, shiftPc_setG]
        exact okOr_pure_shift p s _
      | imm v =>
        simp only [shiftTgt, shiftPc_next, shiftPc_setG]
        exact okOr_pure_shift p s _
      | mem m =>
        simp only [shiftTgt, shiftPc_next, effAddr_shift p s m,
          loadVal_shift, shiftPc_setG]
        exact okOr_bind2_shift p s _ _ _
    · simp only [if_neg hw]
      simp only [shiftTgt, gData32_shift, shiftPc_next,
        shiftPc_setData32, shiftPc_next]
      exact okOr_bind_shift p s _ _
  | movst w m src =>
    simp only [shiftTgt, shiftPc_next, effAddr_shift p s m]
    by_cases hw : w = 64
    · simp only [if_pos hw, shiftPc_getG, shiftPc_storeVal, shiftPc_next]
      exact okOr_bind_shift p s _ _
    · simp only [if_neg hw, shiftPc_getG]
      cases hg : s.getG src with
      | num lo hi =>
        simp only [shiftPc_next, shiftPc_storeLane]
        exact okOr_bind_shift p s _ _
      | ptr q =>
        exact okOr_bind_err_shift p s _ _
  | alu op w d src =>
    simp only [shiftTgt]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      by_cases hz : op = .xor ∧ src = .reg d
      · have hx : op = .xor := hz.1
        have hsd : src = .reg d := hz.2
        simp only [if_pos hz]
        simp only [shiftPc_next, shiftPc_clearFlags, shiftPc_setG]
        exact okOr_pure_shift p s _
      · simp only [if_neg hz]
        simp only [gCtl_shift, gCtl_shift]
        cases ha : gCtl s (.reg d) with
        | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
        | ok a =>
          cases hb : gCtl s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, shiftPc_fail]
          | ok b =>
            simp only [bind_ok_eq]
            cases op with
            | add =>
              dsimp only
              by_cases hc : b.region = rNum ∨ a.region = rNum
              · simp only [if_pos hc]
                simp only [shiftPc_next, shiftPc_setFlags, shiftPc_setG]
                exact okOr_pure_shift p s _
              · simp only [if_neg hc]
                exact okOr_throw_shift p s _
            | xor =>
              dsimp only
              exact okOr_throw_shift p s _
            | and =>
              dsimp only
              cases hx2 : Ctl.asInt a.off with
              | none => exact okOr_throw_shift p s _
              | some x =>
                cases hy2 : Ctl.asInt b.off with
                | none => exact okOr_throw_shift p s _
                | some y =>
                  dsimp only
                  cases hr2 : andInt x y with
                  | none => exact okOr_throw_shift p s _
                  | some r =>
                    by_cases hc : b.region = rNum ∧ (a.region = rNum ∨ (-64 ≤ y ∧ y < 0))
                    · simp only [if_pos hc]
                      simp only [shiftPc_next, shiftPc_clearFlags, shiftPc_setG]
                      exact okOr_pure_shift p s _
                    · simp only [if_neg hc]
                      exact okOr_throw_shift p s _
            | or =>
              dsimp only
              exact okOr_throw_shift p s _
    · simp only [if_neg hw]
      by_cases hz : op = .xor ∧ src = .reg d
      · have hx : op = .xor := hz.1
        have hsd : src = .reg d := hz.2
        simp only [if_pos hz]
        simp only [shiftPc_next, shiftPc_clearFlags, shiftPc_setData32]
        exact okOr_pure_shift p s _
      · simp only [if_neg hz]
        simp only [gData32_shift, gData32_shift]
        cases ha : gData32 ro mem0 s (.reg d) with
        | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
        | ok a =>
          cases hb : gData32 ro mem0 s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, shiftPc_fail]
          | ok b =>
            simp only [bind_ok_eq, shiftPc_next, shiftPc_clearFlags,
              shiftPc_setData32]
            exact okOr_pure_shift p s _
  | sub w d src =>
    simp only [shiftTgt]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      simp only [gCtl_shift, gCtl_shift]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok a =>
        cases hb : gCtl s src with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, shiftPc_fail]
        | ok b =>
          simp only [bind_ok_eq]
          by_cases hc : b.region = rNum
          · simp only [if_pos hc]
            simp only [shiftPc_next, shiftPc_setFlags, shiftPc_setG]
            exact okOr_pure_shift p s _
          · simp only [if_neg hc]
            exact okOr_throw_shift p s _
    · simp only [if_neg hw]
      exact okOr_throw_shift p s _
  | lea d m =>
    simp only [shiftTgt, shiftPc_next, effAddr_shift p s m, shiftPc_setG]
    exact okOr_bind_shift p s _ _
  | ror w d n =>
    simp only [shiftTgt]
    by_cases hw : w = 32
    · simp only [if_pos hw]
      simp only [gData32_shift]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok a =>
        simp only [bind_ok_eq, shiftPc_next, shiftPc_clearFlags,
          shiftPc_setData32]
        exact okOr_pure_shift p s _
    · simp only [if_neg hw]
      exact okOr_throw_shift p s _
  | shld w d src n =>
    simp only [shiftTgt]
    by_cases hw : w = 32
    · simp only [if_pos hw]
      simp only [gData32_shift, gData32_shift]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok a =>
        cases hb : gData32 ro mem0 s (.reg src) with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, shiftPc_fail]
        | ok b =>
          simp only [bind_ok_eq, shiftPc_next, shiftPc_clearFlags,
            shiftPc_setData32]
          exact okOr_pure_shift p s _
    · simp only [if_neg hw]
      exact okOr_throw_shift p s _
  | shl w d n =>
    simp only [shiftTgt]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      simp only [gCtl_shift]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok a =>
        simp only [bind_ok_eq]
        by_cases hr : a.region = rNum
        · simp only [if_pos hr]
          simp only [shiftPc_next, shiftPc_clearFlags, shiftPc_setG]
          exact okOr_pure_shift p s _
        · simp only [if_neg hr]
          exact okOr_throw_shift p s _
    · simp only [if_neg hw]
      simp only [gData32_shift]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok a =>
        simp only [bind_ok_eq, shiftPc_next, shiftPc_clearFlags,
          shiftPc_setData32]
        exact okOr_pure_shift p s _
  | bswap w d =>
    simp only [shiftTgt]
    by_cases hw : w = 32
    · simp only [if_pos hw]
      simp only [gData32_shift]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok a =>
        simp only [bind_ok_eq, shiftPc_next, shiftPc_setData32]
        exact okOr_pure_shift p s _
    · simp only [if_neg hw]
      exact okOr_throw_shift p s _
  | push r =>
    simp only [shiftTgt, shiftPc_getG]
    cases hs2 : s.getG rsp with
    | num lo hi => exact okOr_throw_shift p s _
    | ptr sp =>
      simp only [shiftPc_getG, shiftPc_storeVal, shiftPc_next, shiftPc_setG]
      exact okOr_pure_shift p s _
  | pop r =>
    simp only [shiftTgt, shiftPc_getG]
    cases hs2 : s.getG rsp with
    | num lo hi => exact okOr_throw_shift p s _
    | ptr sp =>
      simp only [loadVal_shift]
      cases hv : loadVal mem0 s sp with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok v =>
        simp only [bind_ok_eq, shiftPc_next, shiftPc_setG]
        exact okOr_pure_shift p s _
  | cmp w a b =>
    simp only [shiftTgt]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      simp only [gCtl_shift, gCtl_shift]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok x =>
        cases hy : gCtl s b with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, shiftPc_fail]
        | ok y =>
          simp only [bind_ok_eq]
          by_cases hc : y.region = rNum ∨ y.region = x.region
          · simp only [if_pos hc]
            simp only [shiftPc_next, shiftPc_setFlags]
            exact okOr_pure_shift p s _
          · simp only [if_neg hc]
            exact okOr_throw_shift p s _
    · simp only [if_neg hw]
      exact okOr_throw_shift p s _
  | test w a b =>
    simp only [shiftTgt]
    by_cases hc : w = 64 ∧ a = b
    · simp only [if_pos hc, gCtl_shift]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok x =>
        simp only [bind_ok_eq]
        by_cases hr : x.region = rNum
        · simp only [if_pos hr, shiftPc_next, shiftPc_setFlags]
          exact okOr_pure_shift p s _
        · simp only [if_neg hr]
          exact okOr_throw_shift p s _
    · simp only [if_neg hc]
      exact okOr_throw_shift p s _
  | jcc c t =>
    simp only [shiftTgt, shiftPc_flags]
    cases hf : s.flags with
    | none => exact okOr_throw_shift p s _
    | some pr =>
      obtain ⟨a, b⟩ := pr
      simp only [okOr_pure]
      exact (shiftPc_branch p s orc (ccCond c a b) t (decideC_ccCond c a b)).symm
  | jmp t => rfl
  | jccTail c name => exact hok.elim
  | jmpTail name => rfl
  | ret =>
    simp only [shiftTgt, shiftPc_getG]
    cases hs2 : s.getG rsp with
    | num lo hi => exact okOr_throw_shift p s _
    | ptr sp =>
      simp only [loadVal_shift]
      cases hv : loadVal mem0 s sp with
      | error e => simp only [bind_error_eq, okOr_error, shiftPc_fail]
      | ok v =>
        simp only [bind_ok_eq]
        cases v with
        | num lo hi => exact okOr_throw_shift p s _
        | ptr q =>
          obtain ⟨reg, off⟩ := q
          split
          · simp only [shiftPc_next, shiftPc_halt, shiftPc_setG]
            exact okOr_pure_shift p s _
          · exact okOr_throw_shift p s _

/-! ## The run-level transfer -/

section Run
variable {prog winProg : Array Instr} {p : Nat}

/-- `n` steps of the windows program from a pc-shifted state are the pc shift of the linux run,
provided (a) each linux instruction sits at windows index `p + j` as its `shiftTgt p` translation
and (b) every instruction the linux run executes is transferable (`trOk`). -/
theorem run_shift
    (hmap : ∀ j, j < prog.size → winProg[p + j]? = (prog[j]?).map (shiftTgt p))
    (hok : ∀ (pc : Nat) (x : Instr), prog[pc]? = some x → trOk x) :
    ∀ (n : Nat) (s : State W32 Int),
      (∀ k, k < n → (run prog ro mem0 orc k s).halted = true ∨ (run prog ro mem0 orc k s).pc < prog.size) →
      run winProg ro mem0 orc n (shiftPc p s) = shiftPc p (run prog ro mem0 orc n s) := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s hcond
    by_cases hh : s.halted = true
    · have hsh : (shiftPc p s).halted = true := by simp [hh]
      rw [run_halted prog ro mem0 orc (n+1) s hh,
          run_halted winProg ro mem0 orc (n+1) (shiftPc p s) hsh]
    · have hf : s.halted = false := by simpa using hh
      have h0 : s.halted = true ∨ s.pc < prog.size := by
        have h := hcond 0 (Nat.zero_lt_succ n)
        simpa only [run] using h
      have hpc : s.pc < prog.size := by
        rcases h0 with h' | h'
        · simp [hf] at h'
        · exact h'
      have hx : prog[s.pc]? = some prog[s.pc] := Array.getElem?_eq_getElem hpc
      have hwx : winProg[(shiftPc p s).pc]? = some (shiftTgt p prog[s.pc]) := by
        rw [shiftPc_pc, Nat.add_comm s.pc p, hmap s.pc hpc, hx]
        rfl
      have hshf : (shiftPc p s).halted = false := by simp [hf]
      have e1 : run winProg ro mem0 orc (n+1) (shiftPc p s)
          = run winProg ro mem0 orc n (exec ro mem0 orc (shiftTgt p prog[s.pc]) (shiftPc p s)) := by
        simp only [run, shiftPc_halted, hf, Bool.false_eq_true, ite_false, hwx]
      have step : ∀ m, run prog ro mem0 orc (m+1) s
          = run prog ro mem0 orc m (exec ro mem0 orc prog[s.pc] s) := by
        intro m; simp only [run, hf, Bool.false_eq_true, ite_false, hx]
      rw [e1, step n, exec_shiftPc p prog[s.pc] s (hok s.pc prog[s.pc] hx)]
      exact ih (exec ro mem0 orc prog[s.pc] s) (fun k hk => by
        have := hcond (k+1) (Nat.succ_lt_succ hk)
        rwa [step k] at this)

end Run

end ShiftOps

end Hashtree.Asm.X86
