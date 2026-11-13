import Hashtree.Proofs.WinSseRun
import Hashtree.Proofs.WinSafeScan
import Hashtree.Proofs.WinScan

/-!
# R5: `NoStackVal` over a body slice

The stack-memory shift of `Proofs.WinSseExec` needs every reachable linux register to hold a value
that is not a pointer into the stack region (`NoStackVal`); `Proofs.WinSseRun` threads that as a
hypothesis through the body run (`run_wx`).  This module discharges it for a concrete body slice:

* `nsSafe` -- a syntactic side condition on an instruction, checked by the kernel scan
  (`nsSafeB`): the instructions of the shared bodies never move `rsp` into a general register and
  never write a stack pointer into one (the only stack pointer in the register file is `rsp`
  itself, which `NoStackVal` excludes by the index `j ≠ 4`).  `sse_x1`/`avx_x1`/`shani_x2` bodies
  are written so that every data register write is a 32-bit write (a `.num`), the only 64-bit
  arithmetic is `add` of a pointer/count with an immediate or a non-`rsp` number, and the only
  `lea` reads its address from the `rip`-relative rodata (`base = index = none`, `ro = some _`):
  `nsSafe` states exactly these facts.
* `exec_ns` -- one safe instruction preserves `NoStackVal` for every register except `rsp`.
* `run_ns` -- hence the whole run of a body slice does, as long as it stays inside the slice (or
  has halted).
* `all_slice_get` -- a kernel-checked `List.all` scan of a slice gives the predicate at every
  index of the slice (the form the scans of the shipped arrays are stated in).
* `run_wx_body` -- `run_wx` with the `NoStackVal` hypothesis discharged by `run_ns`.

Nothing here introduces an axiom: the `Prop` side conditions are mirrored by Boolean scans
(`nsSafeB_iff`), and the scans themselves are `decide +kernel` over chunks of the shipped arrays.
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinScan
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Hashtree.Asm.X86

/-! ## The syntactic side condition -/

/-- A general-register source that is read as a control value (a pointer/count) must not be
`rsp`; immediate and memory sources are read from memory and are handled by `frameSafe`. -/
def gsRegSafe : GSrc → Prop
  | .reg r => r ≠ 4
  | .imm _ => True
  | .mem _ => True

/-- Boolean form of `gsRegSafe`. -/
def gsRegSafeB : GSrc → Bool
  | .reg r => decide (r ≠ 4)
  | .imm _ => true
  | .mem _ => true

theorem gsRegSafeB_iff (src : GSrc) : (gsRegSafeB src = true) ↔ gsRegSafe src := by
  cases src with
  | reg r => simp only [gsRegSafeB, gsRegSafe, decide_eq_true_eq]
  | imm v => simp only [gsRegSafeB, gsRegSafe]
  | mem m => simp only [gsRegSafeB, gsRegSafe]

/-- The instructions of the shared bodies preserve `NoStackVal`: they never write `rsp`, never
write a stack pointer (all data writes are 32-bit, `lea` reads a `rip`-relative address, 64-bit
arithmetic is `add`/`sub` of a non-stack register with a number), and never `push`/`pop`/`ret` or
tail-call. -/
def nsSafe : Instr → Prop
  | .nop => True
  | .vop _ _ _ _ _ _ => True
  | .vshift _ _ _ _ _ _ => True
  | .vshiftq _ _ _ _ _ => True
  | .vror _ _ _ _ => True
  | .vtern _ _ _ _ _ => True
  | .vload _ _ _ _ => True
  | .vstore _ _ _ => True
  | .pshufd _ _ _ _ => True
  | .pshufb _ _ _ _ _ => True
  | .palignr _ _ _ _ _ => True
  | .pblendw _ _ _ => True
  | .shufps _ _ _ _ _ => True
  | .perm2f128 _ _ _ _ => True
  | .inserti128 _ _ _ _ => True
  | .inserti64x4 _ _ _ _ => True
  | .permi2d _ _ _ => True
  | .permi2q _ _ _ => True
  | .sha256rnds2 _ _ => True
  | .sha256msg1 _ _ => True
  | .sha256msg2 _ _ => True
  | .mov w d _ => w = 32 ∧ d < 16 ∧ d ≠ 4
  | .movst _ _ _ => True
  | .alu op w d src => d < 16 ∧ d ≠ 4 ∧ (w = 32 ∨ (w = 64 ∧ op = LOp.add)) ∧ gsRegSafe src
  | .sub _ d src => d < 16 ∧ d ≠ 4 ∧ gsRegSafe src
  | .lea d m => d < 16 ∧ d ≠ 4 ∧ m.base = none ∧ m.index = none ∧ m.ro ≠ none
  | .ror _ d _ => d < 16 ∧ d ≠ 4
  | .shld _ d _ _ => d < 16 ∧ d ≠ 4
  | .shl _ d _ => d < 16 ∧ d ≠ 4
  | .bswap _ d => d < 16 ∧ d ≠ 4
  | .push _ => False
  | .pop _ => False
  | .cmp _ _ _ => True
  | .test _ _ _ => True
  | .jcc _ _ => True
  | .jmp _ => True
  | .jccTail _ _ => False
  | .jmpTail _ => False
  | .ret => False

/-- Boolean, kernel-reducible form of `nsSafe`. -/
def nsSafeB : Instr → Bool
  | .nop => true
  | .vop _ _ _ _ _ _ => true
  | .vshift _ _ _ _ _ _ => true
  | .vshiftq _ _ _ _ _ => true
  | .vror _ _ _ _ => true
  | .vtern _ _ _ _ _ => true
  | .vload _ _ _ _ => true
  | .vstore _ _ _ => true
  | .pshufd _ _ _ _ => true
  | .pshufb _ _ _ _ _ => true
  | .palignr _ _ _ _ _ => true
  | .pblendw _ _ _ => true
  | .shufps _ _ _ _ _ => true
  | .perm2f128 _ _ _ _ => true
  | .inserti128 _ _ _ _ => true
  | .inserti64x4 _ _ _ _ => true
  | .permi2d _ _ _ => true
  | .permi2q _ _ _ => true
  | .sha256rnds2 _ _ => true
  | .sha256msg1 _ _ => true
  | .sha256msg2 _ _ => true
  | .mov w d _ => decide (w = 32) && decide (d < 16) && decide (d ≠ 4)
  | .movst _ _ _ => true
  | .alu op w d src =>
      decide (d < 16) && decide (d ≠ 4) &&
        (decide (w = 32) || (decide (w = 64) && decide (op = LOp.add))) && gsRegSafeB src
  | .sub _ d src => decide (d < 16) && decide (d ≠ 4) && gsRegSafeB src
  | .lea d m => decide (d < 16) && decide (d ≠ 4) && m.base.isNone && m.index.isNone && m.ro.isSome
  | .ror _ d _ => decide (d < 16) && decide (d ≠ 4)
  | .shld _ d _ _ => decide (d < 16) && decide (d ≠ 4)
  | .shl _ d _ => decide (d < 16) && decide (d ≠ 4)
  | .bswap _ d => decide (d < 16) && decide (d ≠ 4)
  | .push _ => false
  | .pop _ => false
  | .cmp _ _ _ => true
  | .test _ _ _ => true
  | .jcc _ _ => true
  | .jmp _ => true
  | .jccTail _ _ => false
  | .jmpTail _ => false
  | .ret => false

theorem option_isSome_iff_ne_none {α : Type} (o : Option α) :
    (o.isSome = true) ↔ o ≠ none := by
  cases o <;> simp

theorem nsSafeB_iff (i : Instr) : (nsSafeB i = true) ↔ nsSafe i := by
  cases i <;>
    simp only [nsSafeB, nsSafe, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      gsRegSafeB_iff, Option.isNone_iff_eq_none, option_isSome_iff_ne_none,
      Bool.false_eq_true]
  all_goals simp only [and_assoc]

/-! ## Reading a general register after a step -/

theorem getG_next (s : State W32 Int) (j : Nat) : s.next.getG j = s.getG j := rfl

theorem getG_clearFlags (s : State W32 Int) (j : Nat) : (clearFlags s).getG j = s.getG j := rfl

theorem getG_setFlags (s : State W32 Int) (a b : Int) (j : Nat) :
    (setFlags s a b).getG j = s.getG j := rfl

theorem getG_halt (s : State W32 Int) (j : Nat) : (halt s).getG j = s.getG j := rfl

theorem getG_setVec (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) (j : Nat) :
    (setVec s vex w d v).getG j = s.getG j := rfl

theorem getG_storeLane (s : State W32 Int) (a : Addr Int) (x : W32) (j : Nat) :
    (storeLane s a x).getG j = s.getG j := rfl

theorem getG_storeLanes (s : State W32 Int) (a : Addr Int) (v : List W32) (j : Nat) :
    (storeLanes s a v).getG j = s.getG j := by
  induction v generalizing s a with
  | nil => rfl
  | cons x xs ih => simp only [storeLanes, getG_storeLane, ih]

theorem getG_storeVal (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) (j : Nat) :
    (storeVal s a v).getG j = s.getG j := by
  cases v with
  | num lo hi => simp only [storeVal, getG_storeLane]
  | ptr q => rfl

theorem getG_fail (s : State W32 Int) (msg : String) (j : Nat) :
    (s.fail msg).getG j = s.getG j := by
  unfold State.fail
  split <;> rfl

theorem getG_branch (s : State W32 Int) (orc : Nat → Bool) (c : Cond Int) (t : Nat) (j : Nat) :
    (s.branch orc c t).getG j = s.getG j := by
  unfold State.branch
  rcases s with ⟨gpr, vr, fl, mem, pc, ha, tl, err, as⟩
  cases hcd : c.decideC <;>
    (simp only [hcd, Option.isNone_none, Option.isNone_some, ite_true, ite_false, State.next,
      State.getG]; split <;> rfl)

theorem getG_setG_self' (s : State W32 Int) (d : Nat) (v : Val W32 Int)
    (h : d < s.gpr.length) : (s.setG d v).getG d = v := by
  simp only [State.setG, State.getG]
  exact getD_set_self s.gpr d h v _

theorem getG_setG_ne' (s : State W32 Int) (d j : Nat) (v : Val W32 Int) (h : j ≠ d) :
    (s.setG d v).getG j = s.getG j := by
  simp only [State.setG, State.getG]
  exact getD_set_ne s.gpr d j (Ne.symm h) v _

theorem getG_setData32_self (s : State W32 Int) (d : Nat) (x : W32)
    (h : d < s.gpr.length) : (setData32 s d x).getG d = .num x (Lane.const 0) :=
  getG_setG_self' s d _ h

theorem getG_setData32_ne (s : State W32 Int) (d j : Nat) (x : W32) (h : j ≠ d) :
    (setData32 s d x).getG j = s.getG j :=
  getG_setG_ne' s d j _ h

/-! ## `NoStackVal` helpers -/

theorem noStack_num (lo hi : W32) : NoStackVal (.num lo hi) := by
  intro a h
  cases h

theorem noStack_ptr {a : Addr Int} (h : a.region ≠ rStack) : NoStackVal (.ptr a) := by
  intro q hq
  injection hq with hq'
  subst hq'
  exact h

theorem noStack_setG_self (s : State W32 Int) (d : Nat) (v : Val W32 Int)
    (hd : d < s.gpr.length) (hv : NoStackVal v) : NoStackVal ((s.setG d v).getG d) := by
  rw [getG_setG_self' s d v hd]
  exact hv

theorem noStack_setG_ne (s : State W32 Int) (d j : Nat) (v : Val W32 Int) (hjd : j ≠ d)
    (hns : NoStackVal (s.getG j)) : NoStackVal ((s.setG d v).getG j) := by
  rw [getG_setG_ne' s d j v hjd]
  exact hns

/-! ## `okOr` plumbing -/

theorem okOr_bind_getG (s : State W32 Int) (j : Nat) {β : Type} (m : Except String β)
    (g : β → Except String (State W32 Int))
    (h : ∀ x, (okOr s (g x)).getG j = s.getG j) :
    (okOr s (m >>= g)).getG j = s.getG j := by
  cases m with
  | error e => simp only [bind_error_eq, okOr_error, getG_fail]
  | ok x => simp only [bind_ok_eq]; exact h x

theorem okOr_bind2_getG (s : State W32 Int) (j : Nat) {β γ' : Type} (m : Except String β)
    (n : β → Except String γ') (g : β → γ' → Except String (State W32 Int))
    (h : ∀ a b, (okOr s (g a b)).getG j = s.getG j) :
    (okOr s (m >>= fun a => n a >>= fun b => g a b)).getG j = s.getG j := by
  cases m with
  | error e => simp only [bind_error_eq, okOr_error, getG_fail]
  | ok a =>
    simp only [bind_ok_eq]
    exact okOr_bind_getG s j (n a) (g a) (h a)

theorem okOr_throw_getG (s : State W32 Int) (j : Nat) (msg : String) :
    (okOr s (throw msg)).getG j = s.getG j := by
  show (okOr s (Except.error msg)).getG j = s.getG j
  simp only [okOr_error, getG_fail]

theorem okOr_bind_getG_ns (s : State W32 Int) (j : Nat) {β : Type} (m : Except String β)
    (g : β → Except String (State W32 Int))
    (h : ∀ x, (okOr s (g x)).getG j = s.getG j) (hns : NoStackVal (s.getG j)) :
    NoStackVal ((okOr s (m >>= g)).getG j) := by
  rw [okOr_bind_getG s j m g h]
  exact hns

theorem okOr_bind2_getG_ns (s : State W32 Int) (j : Nat) {β γ' : Type} (m : Except String β)
    (n : β → Except String γ') (g : β → γ' → Except String (State W32 Int))
    (h : ∀ a b, (okOr s (g a b)).getG j = s.getG j) (hns : NoStackVal (s.getG j)) :
    NoStackVal ((okOr s (m >>= fun a => n a >>= fun b => g a b)).getG j) := by
  rw [okOr_bind2_getG s j m n g h]
  exact hns

/-! ## One instruction -/

/-- The effective address of a `lea` whose operand has no base and no index register and a
`rip`-relative relocation lies in the rodata region (and not on the stack). -/
theorem lea_region {ro : Region} (hro : ro ≠ rStack) (s : State W32 Int) (m : MemRef)
    (hb : m.base = none) (hi : m.index = none) (hr : m.ro ≠ none)
    (a : Addr Int) (ha : effAddr ro s m = .ok a) : a.region ≠ rStack := by
  unfold effAddr baseAddr at ha
  simp only [hb, hi] at ha
  cases hro' : m.ro with
  | none => exact absurd hro' hr
  | some o =>
    simp only [hro'] at ha
    injection ha with ha'
    subst ha'
    exact hro

/-- A safe `gCtl` operand of a `gsRegSafe` source is `gsSafe` (a memory source cannot be read
by `gCtl` at all). -/
theorem gsSafe_of_gCtl_ok {s : State W32 Int} {src : GSrc} {a : Addr Int}
    (hs : gsRegSafe src) (h : gCtl s src = .ok a) : gsSafe src := by
  cases src with
  | reg r => exact hs
  | imm v => trivial
  | mem m =>
    simp only [gCtl] at h
    exact absurd h (by simp)

section ExecNs
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

/-- A safe instruction preserves `NoStackVal` for every general register except `rsp`. -/
theorem exec_ns (hro : ro ≠ rStack) (i : Instr) (s : State W32 Int)
    (hlen : s.gpr.length = 16) (hns : ∀ j, j ≠ 4 → NoStackVal (s.getG j)) (hn : nsSafe i) :
    ∀ j, j ≠ 4 → NoStackVal ((exec ro mem0 orc i s).getG j) := by
  intro j hj
  cases hs : s.halted with
  | true => simp only [exec, hs, ite_true]; exact hns j hj
  | false =>
  simp only [exec, hs, Bool.false_eq_true, ite_false]
  cases i with
  | nop =>
    dsimp only
    simp only [getG_next]
    exact hns j hj
  | vop op vex w dv s1 s2 =>
    dsimp only
    refine okOr_bind_getG_ns s j _ _ (fun b => ?_) (hns j hj)
    simp only [okOr_pure, getG_setVec, getG_next]
  | vshift k vex w dv src n =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | vshiftq vex w dv src n =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | vror w dv src n =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | vtern w dv s1 s2 imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | vload vex w dv src =>
    dsimp only
    refine okOr_bind_getG_ns s j _ _ (fun v => ?_) (hns j hj)
    simp only [okOr_pure, getG_setVec, getG_next]
  | vstore w m src =>
    dsimp only
    refine okOr_bind_getG_ns s j _ _ (fun a => ?_) (hns j hj)
    simp only [okOr_pure, getG_storeLanes, getG_next]
  | pshufd vex dv src imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | pshufb vex w dv src mask =>
    dsimp only
    refine okOr_bind_getG_ns s j _ _ (fun r => ?_) (hns j hj)
    simp only [okOr_pure, getG_setVec, getG_next]
  | palignr vex dv s1 s2 imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | pblendw dv src imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | shufps w dv s1 s2 imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | perm2f128 dv s1 s2 imm =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | inserti128 dv s1 m imm =>
    dsimp only
    refine okOr_bind2_getG_ns s j _ _ _ (fun a x => ?_) (hns j hj)
    simp only [okOr_pure, getG_setVec, getG_next]
  | inserti64x4 dv s1 m imm =>
    dsimp only
    refine okOr_bind2_getG_ns s j _ _ _ (fun a x => ?_) (hns j hj)
    simp only [okOr_pure, getG_setVec, getG_next]
  | permi2d dv s1 s2 =>
    dsimp only
    refine okOr_bind_getG_ns s j _ _ (fun x => ?_) (hns j hj)
    simp only [okOr_pure, getG_setVec, getG_next]
  | permi2q dv s1 s2 =>
    dsimp only
    refine okOr_bind_getG_ns s j _ _ (fun x => ?_) (hns j hj)
    simp only [okOr_pure, getG_setVec, getG_next]
  | sha256rnds2 dv src =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | sha256msg1 dv src =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | sha256msg2 dv src =>
    dsimp only
    simp only [okOr_pure, getG_setVec, getG_next]
    exact hns j hj
  | mov w d src =>
    dsimp only
    obtain ⟨hw32, hd16, hd4⟩ : w = 32 ∧ d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 64
    · exact absurd (hw32.symm.trans hw) (by decide)
    · simp only [if_neg hw]
      cases hm : gData32 ro mem0 s src with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok x =>
        simp only [bind_ok_eq, okOr_pure, getG_next]
        by_cases hjd : j = d
        · rw [hjd, getG_setData32_self s d x (by omega)]
          exact noStack_num x _
        · rw [getG_setData32_ne s d j x hjd]
          exact hns j hj
  | movst w m src =>
    dsimp only
    refine okOr_bind_getG_ns s j _ _ (fun a => ?_) (hns j hj)
    by_cases hw : w = 64
    · simp only [if_pos hw, okOr_pure, getG_storeVal, getG_next]
    · simp only [if_neg hw]
      cases hg : s.getG src with
      | num lo hi => simp only [hg, okOr_pure, getG_storeLane, getG_next]
      | ptr q => exact okOr_throw_getG s j _
  | alu op w d src =>
    dsimp only
    obtain ⟨hd16, hd4, hw, hs⟩ : d < 16 ∧ d ≠ 4 ∧ (w = 32 ∨ (w = 64 ∧ op = LOp.add))
      ∧ gsRegSafe src := hn
    by_cases hw64 : w = 64
    · have hop : op = LOp.add := by
        rcases hw with h32 | ⟨h64, ha⟩
        · exact absurd (h32.symm.trans hw64) (by decide)
        · exact ha
      subst hop
      simp only [if_pos hw64]
      have hz : ¬ (LOp.add = LOp.xor ∧ src = .reg d) := fun h => absurd h.1 (by decide)
      simp only [if_neg hz]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok a =>
        cases hb : gCtl s src with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]; exact hns j hj
        | ok b =>
          by_cases hc : b.region = rNum ∨ a.region = rNum
          · simp only [if_pos hc, bind_ok_eq, okOr_pure, getG_setFlags, getG_next]
            by_cases hjd : j = d
            · rw [hjd, getG_setG_self' s d _ (by omega)]
              refine noStack_ptr ?_
              have ha' : a.region ≠ rStack := gCtl_ok_region s (.reg d) hns hd4 a ha
              have hb' : b.region ≠ rStack :=
                gCtl_ok_region s src hns (gsSafe_of_gCtl_ok hs hb) b hb
              show (if b.region = rNum then a.region else b.region) ≠ rStack
              split <;> assumption
            · rw [getG_setG_ne' s d j _ hjd]
              exact hns j hj
          · simp only [bind_ok_eq, if_neg hc]
            rw [okOr_throw_getG s j]
            exact hns j hj
    · simp only [if_neg hw64]
      by_cases hz : op = .xor ∧ src = .reg d
      · simp only [if_pos hz, okOr_pure, getG_clearFlags, getG_next]
        by_cases hjd : j = d
        · rw [hjd, getG_setData32_self s d (Lane.const 0) (by omega)]
          exact noStack_num _ _
        · rw [getG_setData32_ne s d j (Lane.const 0) hjd]
          exact hns j hj
      · simp only [if_neg hz]
        cases ha : gData32 ro mem0 s (.reg d) with
        | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
        | ok x =>
          cases hb : gData32 ro mem0 s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]; exact hns j hj
          | ok y =>
            simp only [bind_ok_eq, okOr_pure, getG_clearFlags, getG_next]
            by_cases hjd : j = d
            · rw [hjd, getG_setData32_self s d _ (by omega)]
              exact noStack_num _ _
            · rw [getG_setData32_ne s d j _ hjd]
              exact hns j hj
  | sub w d src =>
    dsimp only
    obtain ⟨hd16, hd4, hs⟩ : d < 16 ∧ d ≠ 4 ∧ gsRegSafe src := hn
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok a =>
        cases hb : gCtl s src with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]; exact hns j hj
        | ok b =>
          by_cases hc : b.region = rNum
          · simp only [if_pos hc, bind_ok_eq, okOr_pure, getG_setFlags, getG_next]
            by_cases hjd : j = d
            · rw [hjd, getG_setG_self' s d _ (by omega)]
              refine noStack_ptr ?_
              have ha' : a.region ≠ rStack := gCtl_ok_region s (.reg d) hns hd4 a ha
              show (a.plus (Ctl.smul (-1) b.off)).region ≠ rStack
              simpa only [Addr.plus] using ha'
            · rw [getG_setG_ne' s d j _ hjd]
              exact hns j hj
          · simp only [bind_ok_eq, if_neg hc]
            rw [okOr_throw_getG s j]
            exact hns j hj
    · simp only [if_neg hw]
      rw [okOr_throw_getG s j]
      exact hns j hj
  | lea d m =>
    dsimp only
    obtain ⟨hd16, hd4, hb, hi, hr⟩ : d < 16 ∧ d ≠ 4 ∧ m.base = none ∧ m.index = none
      ∧ m.ro ≠ none := hn
    cases he : effAddr ro s m with
    | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
    | ok a =>
      simp only [bind_ok_eq, okOr_pure, getG_next]
      by_cases hjd : j = d
      · rw [hjd, getG_setG_self' s d _ (by omega)]
        exact noStack_ptr (lea_region hro s m hb hi hr a he)
      · rw [getG_setG_ne' s d j _ hjd]
        exact hns j hj
  | ror w d n =>
    dsimp only
    obtain ⟨hd16, hd4⟩ : d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 32
    · simp only [if_pos hw]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok x =>
        simp only [bind_ok_eq, okOr_pure, getG_clearFlags, getG_next]
        by_cases hjd : j = d
        · rw [hjd, getG_setData32_self s d _ (by omega)]
          exact noStack_num _ _
        · rw [getG_setData32_ne s d j _ hjd]
          exact hns j hj
    · simp only [if_neg hw]
      rw [okOr_throw_getG s j]
      exact hns j hj
  | shld w d src n =>
    dsimp only
    obtain ⟨hd16, hd4⟩ : d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 32
    · simp only [if_pos hw]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok x =>
        cases hb : gData32 ro mem0 s (.reg src) with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]; exact hns j hj
        | ok y =>
          simp only [bind_ok_eq, okOr_pure, getG_clearFlags, getG_next]
          by_cases hjd : j = d
          · rw [hjd, getG_setData32_self s d _ (by omega)]
            exact noStack_num _ _
          · rw [getG_setData32_ne s d j _ hjd]
            exact hns j hj
    · simp only [if_neg hw]
      rw [okOr_throw_getG s j]
      exact hns j hj
  | shl w d n =>
    dsimp only
    obtain ⟨hd16, hd4⟩ : d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases ha : gCtl s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok a =>
        simp only [bind_ok_eq]
        by_cases hr : a.region = rNum
        · simp only [if_pos hr, okOr_pure, getG_clearFlags, getG_next]
          by_cases hjd : j = d
          · rw [hjd, getG_setG_self' s d _ (by omega)]
            refine noStack_ptr ?_
            show (rNum : Region) ≠ rStack
            decide
          · rw [getG_setG_ne' s d j _ hjd]
            exact hns j hj
        · simp only [bind_ok_eq, if_neg hr]
          rw [okOr_throw_getG s j]
          exact hns j hj
    · simp only [if_neg hw]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok x =>
        simp only [bind_ok_eq, okOr_pure, getG_clearFlags, getG_next]
        by_cases hjd : j = d
        · rw [hjd, getG_setData32_self s d _ (by omega)]
          exact noStack_num _ _
        · rw [getG_setData32_ne s d j _ hjd]
          exact hns j hj
  | bswap w d =>
    dsimp only
    obtain ⟨hd16, hd4⟩ : d < 16 ∧ d ≠ 4 := hn
    by_cases hw : w = 32
    · simp only [if_pos hw]
      cases ha : gData32 ro mem0 s (.reg d) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok x =>
        simp only [bind_ok_eq, okOr_pure, getG_next]
        by_cases hjd : j = d
        · rw [hjd, getG_setData32_self s d _ (by omega)]
          exact noStack_num _ _
        · rw [getG_setData32_ne s d j _ hjd]
          exact hns j hj
    · simp only [if_neg hw]
      rw [okOr_throw_getG s j]
      exact hns j hj
  | push r => exact hn.elim
  | pop r => exact hn.elim
  | cmp w a b =>
    dsimp only
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok x =>
        cases hy : gCtl s b with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, getG_fail]; exact hns j hj
        | ok y =>
          by_cases hc : y.region = rNum ∨ y.region = x.region
          · simp only [if_pos hc, bind_ok_eq, okOr_pure, getG_setFlags, getG_next]
            exact hns j hj
          · simp only [bind_ok_eq, if_neg hc]
            rw [okOr_throw_getG s j]
            exact hns j hj
    · simp only [if_neg hw]
      rw [okOr_throw_getG s j]
      exact hns j hj
  | test w a b =>
    dsimp only
    by_cases hc : w = 64 ∧ a = b
    · simp only [if_pos hc]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, getG_fail]; exact hns j hj
      | ok x =>
        by_cases hr : x.region = rNum
        · simp only [if_pos hr, bind_ok_eq, okOr_pure, getG_setFlags, getG_next]
          exact hns j hj
        · simp only [bind_ok_eq, if_neg hr]
          rw [okOr_throw_getG s j]
          exact hns j hj
    · simp only [if_neg hc]
      rw [okOr_throw_getG s j]
      exact hns j hj
  | jcc c t =>
    dsimp only
    cases hf : s.flags with
    | none =>
      rw [okOr_throw_getG s j]
      exact hns j hj
    | some q =>
      obtain ⟨x, y⟩ := q
      dsimp only
      simp only [okOr_pure, getG_branch]
      exact hns j hj
  | jmp t =>
    dsimp only
    exact hns j hj
  | jccTail c name => exact hn.elim
  | jmpTail name => exact hn.elim
  | ret => exact hn.elim

end ExecNs

/-! ## A whole slice -/

/-- A Boolean `List.all` scan over a slice gives the predicate at every concrete index of the
slice. -/
theorem all_slice_get {α : Type} (l : List α) (o n : Nat) (f : α → Bool)
    (hz : ((l.drop o).take n).all f = true) :
    ∀ j, j < n → ∀ x, l[o + j]? = some x → f x = true := by
  intro j hj x hx
  have hmem : x ∈ (l.drop o).take n := by
    rw [List.mem_iff_getElem?]
    refine ⟨j, ?_⟩
    rw [List.getElem?_take_of_lt hj, getElem?_drop, hx]
  exact List.all_eq_true.mp hz x hmem

section RunNs
variable {ro : Region} {prog : Array Instr} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

/-- `n` steps of a body slice keep every general register except `rsp` free of stack pointers,
provided the starting state does, every instruction of the slice is `nsSafe`, and the run stays
inside the slice (or has halted). -/
theorem run_ns (hro : ro ≠ rStack) {base L : Nat}
    (hnsI : ∀ pc i, base ≤ pc → pc < base + L → prog[pc]? = some i → nsSafe i)
    (hL : base + L ≤ prog.size) :
    ∀ (n : Nat) (s : State W32 Int), s.gpr.length = 16 →
    (∀ j, j ≠ 4 → NoStackVal (s.getG j)) →
    (∀ k, k < n → (run prog ro mem0 orc k s).halted = true ∨
      (base ≤ (run prog ro mem0 orc k s).pc ∧
        (run prog ro mem0 orc k s).pc < base + L)) →
    (∀ k, k ≤ n → ∀ j, j ≠ 4 → NoStackVal ((run prog ro mem0 orc k s).getG j)) := by
  intro n
  induction n with
  | zero =>
    intro s hlen h0 hcond k hk j hj
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    exact h0 j hj
  | succ n ih =>
    intro s hlen h0 hcond k hk j hj
    rcases Nat.lt_or_ge k (n + 1) with hklt | hkge
    · exact ih s hlen h0
        (fun k' hk' => hcond k' (Nat.lt_trans hk' (Nat.lt_succ_self n)))
        k (by omega) j hj
    · have hkeq : k = n + 1 := by omega
      subst hkeq
      by_cases hh : s.halted = true
      · rw [run_halted prog ro mem0 orc (n + 1) s hh]
        exact h0 j hj
      · have hf : s.halted = false := by simpa using hh
        have h0c := hcond 0 (Nat.zero_lt_succ n)
        have hpc : base ≤ s.pc ∧ s.pc < base + L := by
          rcases h0c with h' | h'
          · exact absurd h' (by
              rw [show run prog ro mem0 orc 0 s = s from rfl]
              simp [hf])
          · exact h'
        have hlt : s.pc < prog.size := by omega
        have hx : prog[s.pc]? = some prog[s.pc] := Array.getElem?_eq_getElem hlt
        have step : ∀ m, run prog ro mem0 orc (m + 1) s
            = run prog ro mem0 orc m (exec ro mem0 orc prog[s.pc] s) := by
          intro m
          simp only [run, hf, Bool.false_eq_true, ite_false, hx]
        have hlen' : (exec ro mem0 orc prog[s.pc] s).gpr.length = 16 := by
          rw [exec_gpr_len]
          exact hlen
        have hns0' : ∀ j, j ≠ 4 →
            NoStackVal ((exec ro mem0 orc prog[s.pc] s).getG j) :=
          exec_ns hro prog[s.pc] s hlen h0 (hnsI s.pc _ hpc.1 hpc.2 hx)
        have hcond' : ∀ k', k' < n →
            (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).halted = true ∨
            (base ≤ (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).pc ∧
              (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).pc < base + L) := by
          intro k' hk'
          have h1 := hcond (k' + 1) (Nat.succ_lt_succ hk')
          rwa [step k'] at h1
        rw [step n]
        exact ih (exec ro mem0 orc prog[s.pc] s) hlen' hns0' hcond'
          n (Nat.le_refl n) j hj

end RunNs

/-! ## `run_wx` with the side condition discharged -/

section RunWxBody
variable {F G : Nat → Nat} {linuxProg winProg : Array Instr} {p base L : Nat}
variable {ro : Region} {mem0w mem0l : Addr Int → Cell W32 Int} {orc : Nat → Bool}

/-- `run_wx` with `NoStackVal` discharged over the linux body slice by `run_ns`. -/
theorem run_wx_body (μ : Int) (hFG : RenPerm F G) (hG4 : ∀ j, j < 16 → j ≠ 4 → G j ≠ 4)
    (hro : ro ≠ rStack) (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a))
    (hmap : ∀ pc i, base ≤ pc → pc < base + L → linuxProg[pc]? = some i →
      winProg[pc + p]? = some (shiftTgt p (rlI F i)))
    (hokI : ∀ pc i, base ≤ pc → pc < base + L → linuxProg[pc]? = some i → okI i)
    (hframe : ∀ pc i, base ≤ pc → pc < base + L → linuxProg[pc]? = some i →
      frameSafe (rlI F i))
    (hnsI : ∀ pc i, base ≤ pc → pc < base + L → linuxProg[pc]? = some i → nsSafe i)
    (hLsize : base + L ≤ linuxProg.size) :
    ∀ (n : Nat) (s : State W32 Int), s.gpr.length = 16 →
    (∀ j, j ≠ 4 → NoStackVal (s.getG j)) →
    (∀ k, k < n → (run linuxProg ro mem0l orc k s).halted = true ∨
      (base ≤ (run linuxProg ro mem0l orc k s).pc ∧
        (run linuxProg ro mem0l orc k s).pc < base + L)) →
    run winProg ro mem0w orc n (winSt F G μ p s)
      = winSt F G μ p (run linuxProg ro mem0l orc n s) := by
  intro n s hlen hns0 hcond
  exact run_wx μ hFG hG4 hro h0 hmap hokI hframe hLsize n s hlen hcond
    (fun k hk j hj =>
      run_ns hro hnsI hLsize k s hlen hns0
        (fun k' hk' => hcond k' (Nat.lt_trans hk' hk)) k (Nat.le_refl k) j hj)

end RunWxBody

end Hashtree.Asm.X86
