import Hashtree.Proofs.Win64
import Hashtree.Proofs.WinFrame
import Hashtree.Proofs.WinShani

/-!
# R5: the stack-frame layer of the windows kernel transfer

The windows kernels reserve a deeper frame than their linux twins and reach the same stack slots
through larger displacements.  For `shani_x2` the numbers are `sub rsp, 248` (windows) against
`sub rsp, 88` (linux), and every `rsp`-relative displacement of the body is `160` larger on
windows, so both streams touch the *same* stack addresses (`δ = -160`, `d = 160`, `δ + d = 0`).

This module proves the stack half of that transfer for a body run that starts after the
prologues:

* `spSt δ` lowers `rsp` by `δ` and leaves every other register, the flags and the whole write
  log unchanged;
* `effAddr_mv` -- for a memory operand whose displacement has been shifted by `d` (as the
  windows streams are, see `Proofs.WinShani.mv`/`addDisp`), the effective address computed in the
  `δ`-lowered state is the **same address**, whenever the operand is `rsp`-relative with no index
  or rebased on a register other than `rsp` (`mSafe`);
* `exec_frame` -- every instruction that never uses `rsp` as a value (`frameSafe`: no
  `push`/`pop`/`ret`/tail call, no register operand `rsp`, no `rsp` index) executes on the
  translated stream in the lowered state exactly as the linux instruction does on the linux
  state;
* `exec_comb`, `run_comb` -- the three layers (`addDisp` displacement shift, register renaming
  `rlI`, program-counter shift `shiftTgt`) compose into one instruction/run transfer over a
  *slice* of the two programs (the shared body), with the side conditions collected as
  `okI ∧ frameSafe`.

The hypotheses of `run_comb` are exactly what the shipped-stream scans provide: the body slice
correspondence (`*_body_correspondence`), `okI` on the body, `frameSafe` on the body, and the
fact that the linux run stays inside the body slice until it halts or returns.
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinShani (mv vs gs addDisp bodyI)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Hashtree.Asm.X86

/-! ## Lowering the stack pointer -/

/-- Lower a stack pointer by `δ`; every other value is unchanged. -/
def spVal (δ : Int) : Val W32 Int → Val W32 Int
  | .ptr a => .ptr (a.plusI δ)
  | .num l h => .num l h

/-- The windows body state belonging to the linux body state `s`: `rsp` (register `4`) is `δ`
lower, every other register, the vector registers, the flags, the memory and the whole write log
are unchanged. -/
def spSt (δ : Int) (s : State W32 Int) : State W32 Int :=
  { s with gpr := s.gpr.set 4 (spVal δ (s.getG 4)) }

@[simp] theorem spSt_gpr (δ : Int) (s : State W32 Int) :
    (spSt δ s).gpr = s.gpr.set 4 (spVal δ (s.getG 4)) := rfl
@[simp] theorem spSt_vr (δ : Int) (s : State W32 Int) : (spSt δ s).vr = s.vr := rfl
@[simp] theorem spSt_flags (δ : Int) (s : State W32 Int) : (spSt δ s).flags = s.flags := rfl
@[simp] theorem spSt_mem (δ : Int) (s : State W32 Int) : (spSt δ s).mem = s.mem := rfl
@[simp] theorem spSt_pc (δ : Int) (s : State W32 Int) : (spSt δ s).pc = s.pc := rfl
@[simp] theorem spSt_halted (δ : Int) (s : State W32 Int) : (spSt δ s).halted = s.halted := rfl
@[simp] theorem spSt_tail (δ : Int) (s : State W32 Int) : (spSt δ s).tail = s.tail := rfl
@[simp] theorem spSt_err (δ : Int) (s : State W32 Int) : (spSt δ s).err = s.err := rfl
@[simp] theorem spSt_assume (δ : Int) (s : State W32 Int) : (spSt δ s).assume = s.assume := rfl
@[simp] theorem spSt_getV (δ : Int) (s : State W32 Int) (i : Nat) :
    (spSt δ s).getV i = s.getV i := rfl

theorem spSt_gpr_len (δ : Int) (s : State W32 Int) : (spSt δ s).gpr.length = s.gpr.length := by
  simp only [spSt, List.length_set]

theorem getD_set_ne {α : Type} (l : List α) (i j : Nat) (h : i ≠ j) (a d : α) :
    (l.set i a).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set, if_neg h]

theorem getD_set_self {α : Type} (l : List α) (i : Nat) (hi : i < l.length) (a d : α) :
    (l.set i a).getD i d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
  rfl

theorem spSt_getG_self (δ : Int) (s : State W32 Int) (h4 : 4 < s.gpr.length) :
    (spSt δ s).getG 4 = spVal δ (s.getG 4) := by
  simp only [spSt, State.getG, getD_set_self _ _ h4]

theorem spSt_getG_ne (δ : Int) (s : State W32 Int) (j : Nat) (hj : j ≠ 4) :
    (spSt δ s).getG j = s.getG j := by
  simp only [spSt, State.getG]
  exact getD_set_ne s.gpr 4 j (Ne.symm hj) _ _

theorem spSt_setG (δ : Int) (s : State W32 Int) (j : Nat)
    (hj : j ≠ 4) (v : Val W32 Int) :
    (spSt δ s).setG j v = spSt δ (s.setG j v) := by
  simp only [spSt, State.setG, State.getG]
  rw [List.set_comm _ _ (Ne.symm hj), getD_set_ne s.gpr j 4 hj]

@[simp] theorem spSt_next (δ : Int) (s : State W32 Int) : (spSt δ s).next = spSt δ s.next := rfl

@[simp] theorem spSt_setV (δ : Int) (s : State W32 Int) (i : Nat) (v : List W32) :
    (spSt δ s).setV i v = spSt δ (s.setV i v) := rfl

@[simp] theorem spSt_setVec (δ : Int) (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) :
    setVec (spSt δ s) vex w d v = spSt δ (setVec s vex w d v) := by
  simp only [setVec, spSt_setV, spSt_getV]

@[simp] theorem spSt_clearFlags (δ : Int) (s : State W32 Int) :
    clearFlags (spSt δ s) = spSt δ (clearFlags s) := rfl

@[simp] theorem spSt_setFlags (δ : Int) (s : State W32 Int) (a b : Int) :
    setFlags (spSt δ s) a b = spSt δ (setFlags s a b) := rfl

@[simp] theorem spSt_halt (δ : Int) (s : State W32 Int) :
    halt (spSt δ s) = spSt δ (halt s) := by
  rcases s with ⟨gpr, vr, fl, mem, pc, ha, tl, err, as⟩
  rfl

@[simp] theorem spSt_fail (δ : Int) (s : State W32 Int) (m : String) :
    (spSt δ s).fail m = spSt δ (s.fail m) := by
  rcases s with ⟨gpr, vr, fl, mem, pc, ha, tl, err, as⟩
  cases err <;> rfl

@[simp] theorem spSt_setData32 (δ : Int) (s : State W32 Int) (dn : Nat)
    (hd : dn ≠ 4) (x : W32) :
    setData32 (spSt δ s) dn x = spSt δ (setData32 s dn x) := by
  simp only [setData32, spSt, State.setG, State.getG]
  rw [List.set_comm _ _ (Ne.symm hd), getD_set_ne s.gpr dn 4 hd]

@[simp] theorem spSt_storeLane (δ : Int) (s : State W32 Int) (a : Addr Int) (x : W32) :
    storeLane (spSt δ s) a x = spSt δ (storeLane s a x) := rfl

@[simp] theorem spSt_storeLanes (δ : Int) (s : State W32 Int) (a : Addr Int) (v : List W32) :
    storeLanes (spSt δ s) a v = spSt δ (storeLanes s a v) := by
  induction v generalizing s a with
  | nil => rfl
  | cons x xs ih => simp only [storeLanes]; rw [spSt_storeLane, ih]

@[simp] theorem spSt_storeVal (δ : Int) (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) :
    storeVal (spSt δ s) a v = spSt δ (storeVal s a v) := by
  cases v with
  | num lo hi => simp only [storeVal, spSt_storeLane]
  | ptr q => rfl

theorem spSt_branch (δ : Int) (s : State W32 Int) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    spSt δ (s.branch orc c t) = (spSt δ s).branch orc c t := by
  unfold State.branch
  rcases s with ⟨gpr, vr, fl, mem, pc, ha, tl, err, as⟩
  cases hcd : c.decideC <;>
    (simp only [hcd, Option.isNone_none, Option.isNone_some, ite_true, ite_false, State.next,
      State.getG, spSt]; split <;> rfl)

/-! ## Operands, addresses and cells are invariant under the lowering -/

section SpOps
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

theorem readCell_sp (δ : Int) (s : State W32 Int) (a : Addr Int) :
    readCell mem0 (spSt δ s) a = readCell mem0 s a := by
  simp only [readCell, spSt_mem]

theorem loadLane_sp (δ : Int) (s : State W32 Int) (a : Addr Int) :
    loadLane mem0 (spSt δ s) a = loadLane mem0 s a := by
  simp only [loadLane, readCell_sp]

theorem loadLanes_sp : ∀ (δ : Int) (s : State W32 Int) (a : Addr Int) (n : Nat),
    loadLanes mem0 (spSt δ s) a n = loadLanes mem0 s a n
  | δ, s, a, 0 => rfl
  | δ, s, a, n + 1 => by
    simp only [loadLanes]
    rw [loadLane_sp, loadLanes_sp δ s (a.plusI 4) n]

theorem pbRest_sp : ∀ (δ : Int) (s : State W32 Int) (q a : Addr Int) (n k : Nat),
    pbRest mem0 (spSt δ s) q a n k = pbRest mem0 s q a n k
  | δ, s, q, a, 0, k => rfl
  | δ, s, q, a, n + 1, k => by
    simp only [pbRest, readCell_sp, pbRest_sp δ s q a n (k + 1)]

theorem loadVal_sp (δ : Int) (s : State W32 Int) (a : Addr Int) :
    loadVal mem0 (spSt δ s) a = loadVal mem0 s a := by
  simp only [loadVal, readCell_sp, pbRest_sp, loadLane_sp]

theorem regPtr_sp_self (δ : Int) (s : State W32 Int) (h4 : 4 < s.gpr.length) :
    regPtr (spSt δ s) 4 = (regPtr s 4).map (fun a => a.plusI δ) := by
  simp only [regPtr, spSt_getG_self δ s h4]
  cases s.getG 4 with
  | ptr a => rfl
  | num l h => rfl

theorem regPtr_sp_ne (δ : Int) (s : State W32 Int) (r : Nat) (hr : r ≠ 4) :
    regPtr (spSt δ s) r = regPtr s r := by
  simp only [regPtr, spSt_getG_ne δ s r hr]

/-- A memory operand the frame transfer can handle: an `rsp`-relative operand has no index and no
`rip` relocation, and any index register is not `rsp`. -/
def mSafe (m : MemRef) : Prop :=
  (match m.index with
    | none => True
    | some i => i ≠ 4) ∧ (m.base = some (4 : Nat) → m.ro = none ∧ m.index = none)

instance instDecMSafe (m : MemRef) : Decidable (mSafe m) := by
  unfold mSafe
  cases m.index with
  | none => simp only; infer_instance
  | some i => simp only; infer_instance

/-- Safe general-register operands: never `rsp`. -/
def gsSafe : GSrc → Prop
  | .reg r => r ≠ 4
  | .imm _ => True
  | .mem m => mSafe m

/-- Safe vector operands. -/
def vsSafe : VSrc → Prop
  | .reg _ => True
  | .mem m => mSafe m

instance instDecGSafe (s : GSrc) : Decidable (gsSafe s) := by
  cases s with
  | reg r => simp only [gsSafe]; infer_instance
  | imm v => simp only [gsSafe]; infer_instance
  | mem m => simp only [gsSafe]; infer_instance

instance instDecVSafe (s : VSrc) : Decidable (vsSafe s) := by
  cases s with
  | reg i => simp only [vsSafe]; infer_instance
  | mem m => simp only [vsSafe]; infer_instance

/-- Re-associating the two address offsets: lowering by `δ` and then adding `x + d` is adding
`x`, when `δ + d = 0`. -/
theorem plusI_plusI_add (a : Addr Int) (δ d x : Int) (h : δ + d = 0) :
    (a.plusI δ).plusI (x + d) = a.plusI x := by
  cases a with
  | mk r o =>
    have hoff : (o + δ) + (x + d) = o + x := by omega
    simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq, hoff]

/-- The effective address of a displacement-shifted operand in the `δ`-lowered state is the linux
effective address, provided `δ + d = 0` and the operand is not `rsp`-indexed. -/
theorem effAddr_mv (δ d : Int) (hδ : δ + d = 0) (s : State W32 Int) (m : MemRef)
    (hlen : s.gpr.length = 16) (hm : mSafe m) :
    effAddr ro (spSt δ s) (mv d m) = effAddr ro s m := by
  obtain ⟨hidx, hro⟩ := hm
  cases hro2 : m.ro with
  | some o =>
    have hb : ¬ m.base = some (4 : Nat) := fun h => by
      have h' := (hro h).1
      rw [hro2] at h'
      exact absurd h' (by simp)
    have hmv : mv d m = m := by
      unfold mv
      rw [if_neg hb]
    simp only [effAddr, hmv, hro2, baseAddr]
    cases hidx2 : m.index with
    | none => rfl
    | some i =>
      rw [hidx2] at hidx
      simp only [spSt_getG_ne δ s i hidx]
  | none =>
    by_cases hb : m.base = some (4 : Nat)
    · obtain ⟨-, hidx'⟩ := hro hb
      have hmv : mv d m = { m with disp := m.disp + d } := by
        unfold mv
        rw [hb, if_pos rfl]
      simp only [effAddr, hmv, hro2, hidx', baseAddr, hb]
      rw [regPtr_sp_self δ s (by omega)]
      cases hr : regPtr s 4 with
      | error e => rfl
      | ok a =>
        show Except.ok ((a.plusI δ).plusI (m.disp + d)) = Except.ok (a.plusI m.disp)
        rw [plusI_plusI_add a δ d m.disp hδ]
    · have hmv : mv d m = m := by
        unfold mv
        rw [if_neg hb]
      simp only [effAddr, hmv, hro2, baseAddr]
      cases hmb : m.base with
      | none =>
        cases hidx2 : m.index with
        | none => rfl
        | some i =>
          rw [hidx2] at hidx
          simp only [spSt_getG_ne δ s i hidx]
      | some b =>
        have hbr : b ≠ 4 := fun h => hb (by rw [hmb, h])
        cases hidx2 : m.index with
        | none => simp only [regPtr_sp_ne δ s b hbr]
        | some i =>
          rw [hidx2] at hidx
          simp only [regPtr_sp_ne δ s b hbr, spSt_getG_ne δ s i hidx]

theorem readVSrc_sp (δ d : Int) (hδ : δ + d = 0) (s : State W32 Int) (w : Nat) (src : VSrc)
    (hlen : s.gpr.length = 16) (h : vsSafe src) :
    readVSrc ro mem0 (spSt δ s) w (vs d src) = readVSrc ro mem0 s w src := by
  cases src with
  | reg i => rfl
  | mem m => simp only [vs, readVSrc, effAddr_mv δ d hδ s m hlen h, loadLanes_sp]

theorem gCtl_sp_reg (δ : Int) (s : State W32 Int) (r : Nat) (hr : r ≠ 4) :
    gCtl (spSt δ s) (.reg r) = gCtl s (.reg r) := by
  simp only [gCtl, spSt_getG_ne δ s r hr]

theorem gCtl_sp (δ d : Int) (s : State W32 Int) (src : GSrc) (h : gsSafe src) :
    gCtl (spSt δ s) (gs d src) = gCtl s src := by
  cases src with
  | reg r => exact gCtl_sp_reg δ s r h
  | imm v => rfl
  | mem m => rfl

theorem gData32_sp (δ d : Int) (hδ : δ + d = 0) (s : State W32 Int) (src : GSrc)
    (hlen : s.gpr.length = 16) (h : gsSafe src) :
    gData32 ro mem0 (spSt δ s) (gs d src) = gData32 ro mem0 s src := by
  cases src with
  | reg r => simp only [gs, gData32, spSt_getG_ne δ s r h]
  | imm v => rfl
  | mem m => simp only [gs, gData32, effAddr_mv δ d hδ s m hlen h, loadLane_sp]

/-- Data-operand reads of a direct general register are invariant under the lowering. -/
theorem gData32_sp_reg (δ : Int) (s : State W32 Int) (r : Nat) (hr : r ≠ 4) :
    gData32 ro mem0 (spSt δ s) (.reg r) = gData32 ro mem0 s (.reg r) := by
  simp only [gData32, spSt_getG_ne δ s r hr]

theorem gData32_sp_mem (δ d : Int) (hδ : δ + d = 0) (s : State W32 Int) (m : MemRef)
    (hlen : s.gpr.length = 16) (hm : mSafe m) :
    gData32 ro mem0 (spSt δ s) (.mem (mv d m)) = gData32 ro mem0 s (.mem m) := by
  simp only [gData32, effAddr_mv δ d hδ s m hlen hm, loadLane_sp]

/-! ### `okOr` helpers -/

theorem okOr_pure_sp (δ : Int) (s : State W32 Int) (X : State W32 Int) :
    okOr (spSt δ s) (pure (spSt δ X)) = spSt δ (okOr s (pure X)) := by
  rw [okOr_pure, okOr_pure]

theorem okOr_bind_sp (δ : Int) (s : State W32 Int) {β : Type} (m : Except String β)
    (f : β → State W32 Int) :
    okOr (spSt δ s) (m >>= fun b => pure (spSt δ (f b)))
      = spSt δ (okOr s (m >>= fun b => pure (f b))) := by
  cases m with
  | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
  | ok b => simp only [bind_ok_eq, okOr_pure]

theorem okOr_bind2_sp (δ : Int) (s : State W32 Int) {β γ' : Type} (m : Except String β)
    (n : β → Except String γ') (f : β → γ' → State W32 Int) :
    okOr (spSt δ s) (m >>= fun a => n a >>= fun b => pure (spSt δ (f a b)))
      = spSt δ (okOr s (m >>= fun a => n a >>= fun b => pure (f a b))) := by
  cases m with
  | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
  | ok a =>
    simp only [bind_ok_eq]
    exact okOr_bind_sp δ s (n a) (f a)

theorem okOr_throw_sp (δ : Int) (s : State W32 Int) (msg : String) :
    okOr (spSt δ s) (throw msg) = spSt δ (okOr s (throw msg)) := by
  show okOr (spSt δ s) (.error msg) = spSt δ (okOr s (.error msg))
  simp only [okOr_error, spSt_fail]

theorem okOr_bind_err_sp (δ : Int) (s : State W32 Int) {β : Type} (m : Except String β)
    (e : String) :
    okOr (spSt δ s) (m >>= fun _ => throw e) = spSt δ (okOr s (m >>= fun _ => throw e)) := by
  cases m with
  | error e' => simp only [bind_error_eq, okOr_error, spSt_fail]
  | ok b => simpa only [bind_ok_eq] using okOr_throw_sp δ s e

end SpOps

/-! ## The syntactic side condition: instructions that never use `rsp` as a value -/

/-- The instructions the frame transfer applies to: none of them reads or writes `rsp` except as
the base of a memory operand.  `push`, `pop` and `ret` move `rsp` itself, and the tail calls end
the frame. -/
def frameSafe : Instr → Prop
  | .nop => True
  | .vop _ _ _ _ _ s2 => vsSafe s2
  | .vshift _ _ _ _ _ _ => True
  | .vshiftq _ _ _ _ _ => True
  | .vror _ _ _ _ => True
  | .vtern _ _ _ _ _ => True
  | .vload _ _ _ src => vsSafe src
  | .vstore _ m _ => mSafe m
  | .pshufd _ _ _ _ => True
  | .pshufb _ _ _ _ _ => True
  | .palignr _ _ _ _ _ => True
  | .pblendw _ _ _ => True
  | .shufps _ _ _ _ _ => True
  | .perm2f128 _ _ _ _ => True
  | .inserti128 _ _ m _ => mSafe m
  | .inserti64x4 _ _ m _ => mSafe m
  | .permi2d _ _ _ => True
  | .permi2q _ _ _ => True
  | .sha256rnds2 _ _ => True
  | .sha256msg1 _ _ => True
  | .sha256msg2 _ _ => True
  | .mov _ dn src => dn ≠ 4 ∧ gsSafe src
  | .movst _ m src => mSafe m ∧ src ≠ 4
  | .alu _ _ dn src => dn ≠ 4 ∧ gsSafe src
  | .sub _ dn src => dn ≠ 4 ∧ gsSafe src
  | .lea dn m => dn ≠ 4 ∧ mSafe m
  | .ror _ dn _ => dn ≠ 4
  | .shld _ dn src _ => dn ≠ 4 ∧ src ≠ 4
  | .shl _ dn _ => dn ≠ 4
  | .bswap _ dn => dn ≠ 4
  | .push _ => False
  | .pop _ => False
  | .cmp _ a b => a ≠ 4 ∧ gsSafe b
  | .test _ a b => a ≠ 4 ∧ b ≠ 4
  | .jcc _ _ => True
  | .jmp _ => True
  | .jccTail _ _ => False
  | .jmpTail _ => False
  | .ret => False

instance instDecFrameSafe (i : Instr) : Decidable (frameSafe i) := by
  cases i <;> simp only [frameSafe] <;> infer_instance

/-- `frameSafe` implies `trOk` (it excludes every tail call). -/
theorem frameSafe_trOk (i : Instr) (h : frameSafe i) : trOk i := by
  cases i with
  | jccTail c n => exact h.elim
  | _ => trivial

/-- The register-index bounds only look at `base`/`index`, which the displacement shift leaves
alone. -/
theorem memOk_mv (d : Int) (m : MemRef) : memOk (mv d m) ↔ memOk m := by
  unfold mv
  split <;> rfl

theorem vsrcOk_vs (d : Int) (src : VSrc) : vsrcOk (vs d src) ↔ vsrcOk src := by
  cases src with
  | reg i => rfl
  | mem m => exact memOk_mv d m

theorem gsrcOk_gs (d : Int) (src : GSrc) : gsrcOk (gs d src) ↔ gsrcOk src := by
  cases src with
  | reg i => rfl
  | imm v => rfl
  | mem m => exact memOk_mv d m

/-- `okI` survives the displacement shift (it only constrains register indices). -/
theorem okI_addDisp (d : Int) (i : Instr) (h : okI i) : okI (addDisp d i) := by
  cases i with
  | vop op vex w dd s1 s2 => exact (vsrcOk_vs d s2).2 h
  | vload vex w dd src => exact (vsrcOk_vs d src).2 h
  | vstore w m s => exact (memOk_mv d m).2 h
  | inserti128 dd s1 m imm => exact (memOk_mv d m).2 h
  | inserti64x4 dd s1 m imm => exact (memOk_mv d m).2 h
  | mov w dd s => exact ⟨h.1, (gsrcOk_gs d s).2 h.2⟩
  | movst w m s => exact ⟨(memOk_mv d m).2 h.1, h.2⟩
  | alu op w dd s => exact ⟨h.1, (gsrcOk_gs d s).2 h.2⟩
  | sub w dd s => exact ⟨h.1, (gsrcOk_gs d s).2 h.2⟩
  | lea dd m => exact ⟨h.1, (memOk_mv d m).2 h.2⟩
  | cmp w a b => exact ⟨h.1, (gsrcOk_gs d b).2 h.2⟩
  | _ => exact h

/-- `gs` only maps `.mem` to `.mem`: it never turns a register or immediate operand into a
register operand. -/
theorem gs_eq_reg (d : Int) (src : GSrc) (r : Nat) (h : gs d src = .reg r) : src = .reg r := by
  cases src with
  | reg i => simpa only [gs, GSrc.reg.injEq] using h
  | imm v => simp only [gs] at h; exact absurd h (by simp)
  | mem m => simp only [gs] at h; exact absurd h (by simp)

theorem gs_eq_reg_iff (d : Int) (src : GSrc) (r : Nat) : (gs d src = .reg r) ↔ src = .reg r :=
  ⟨gs_eq_reg d src r, fun h => by rw [h]; rfl⟩

/-- `trOk` is unaffected by the displacement shift and the renaming (neither touches a tail
call). -/
theorem trOk_rlI_addDisp (F : Nat → Nat) (d : Int) (i : Instr) :
    trOk (rlI F (addDisp d i)) ↔ trOk i := by
  cases i <;> simp only [addDisp, rlI, trOk]

/-! ## One instruction of the frame transfer -/

section ExecFrame
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

/-- **The frame transfer, one instruction.**  Executing the displacement-shifted instruction in
the `δ`-lowered state is the same as executing the linux instruction in the linux state and then
lowering -- for every instruction that never uses `rsp` as a value. -/
theorem exec_frame (δ d : Int) (hδ : δ + d = 0) (i : Instr) (s : State W32 Int)
    (hlen : s.gpr.length = 16) (hok : frameSafe i) :
    exec ro mem0 orc (addDisp d i) (spSt δ s) = spSt δ (exec ro mem0 orc i s) := by
  cases hs : s.halted with
  | true => simp only [exec, hs, ite_true, spSt_halted]
  | false =>
  simp only [exec, hs, spSt_halted, Bool.false_eq_true, ite_false]
  cases i with
  | nop => simp only [addDisp, spSt_next]
  | vop op vex w dv s1 s2 =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    rw [readVSrc_sp δ d hδ s w s2 hlen hok]
    exact okOr_bind_sp δ s _ _
  | vshift k vex w dv src n =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | vshiftq vex w dv src n =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | vror w dv src n =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | vtern w dv s1 s2 imm =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | vload vex w dv src =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    rw [readVSrc_sp δ d hδ s w src hlen hok]
    exact okOr_bind_sp δ s _ _
  | vstore w m src =>
    simp only [addDisp, spSt_getV, spSt_next, effAddr_mv δ d hδ s m hlen hok, spSt_storeLanes]
    exact okOr_bind_sp δ s _ _
  | pshufd vex dv src imm =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | pshufb vex w dv src mask =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_bind_sp δ s _ _
  | palignr vex dv s1 s2 imm =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | pblendw dv src imm =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | shufps w dv s1 s2 imm =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | perm2f128 dv s1 s2 imm =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | inserti128 dv s1 m imm =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next, effAddr_mv δ d hδ s m hlen hok,
      loadLanes_sp]
    exact okOr_bind2_sp δ s _ _ _
  | inserti64x4 dv s1 m imm =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next, effAddr_mv δ d hδ s m hlen hok,
      loadLanes_sp]
    exact okOr_bind2_sp δ s _ _ _
  | permi2d dv s1 s2 =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_bind_sp δ s _ _
  | permi2q dv s1 s2 =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_bind_sp δ s _ _
  | sha256rnds2 dv src =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | sha256msg1 dv src =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | sha256msg2 dv src =>
    simp only [addDisp, spSt_getV, spSt_setVec, spSt_next]
    exact okOr_pure_sp δ s _
  | mov w dn src =>
    obtain ⟨hd, hsok⟩ := hok
    simp only [addDisp]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      cases src with
      | reg r =>
        simp only [gs, spSt_next, spSt_getG_ne δ s r hsok, spSt_setG δ s dn hd]
        exact okOr_pure_sp δ s _
      | imm v =>
        simp only [gs, spSt_next, spSt_setG δ s dn hd]
        exact okOr_pure_sp δ s _
      | mem m =>
        simp only [gs, spSt_next, effAddr_mv δ d hδ s m hlen hsok, loadVal_sp,
          spSt_setG δ s dn hd]
        exact okOr_bind2_sp δ s _ _ _
    · simp only [if_neg hw]
      simp only [gData32_sp δ d hδ s src hlen hsok, spSt_next, spSt_setData32 δ s dn hd,
        spSt_setG δ s dn hd]
      exact okOr_bind_sp δ s _ _
  | movst w m src =>
    obtain ⟨hm, hsrc⟩ := hok
    simp only [addDisp, spSt_next, effAddr_mv δ d hδ s m hlen hm]
    by_cases hw : w = 64
    · simp only [if_pos hw, spSt_getG_ne δ s src hsrc, spSt_storeVal, spSt_next]
      exact okOr_bind_sp δ s _ _
    · simp only [if_neg hw, spSt_getG_ne δ s src hsrc]
      cases hg : s.getG src with
      | num lo hi =>
        simp only [spSt_next, spSt_storeLane]
        exact okOr_bind_sp δ s _ _
      | ptr q => exact okOr_bind_err_sp δ s _ _
  | alu op w dn src =>
    obtain ⟨hd, hsok⟩ := hok
    simp only [addDisp]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      by_cases hz : op = .xor ∧ src = .reg dn
      · have hx : op = .xor := hz.1
        have hsd : src = .reg dn := hz.2
        simp only [if_pos hz]
        simp only [if_pos (show op = .xor ∧ (gs d src : GSrc) = .reg dn from
          ⟨hx, by rw [hsd]; rfl⟩)]
        simp only [spSt_next, spSt_clearFlags, spSt_setG δ s dn hd]
        exact okOr_pure_sp δ s _
      · simp only [if_neg hz]
        simp only [if_neg (show ¬(op = .xor ∧ (gs d src : GSrc) = .reg dn) from
          fun hc => hz ⟨hc.1, (gs_eq_reg_iff d src dn).1 hc.2⟩)]
        simp only [gCtl_sp_reg δ s dn hd, gCtl_sp δ d s src hsok]
        cases ha : gCtl s (.reg dn) with
        | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
        | ok a =>
          cases hb : gCtl s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, spSt_fail]
          | ok b =>
            simp only [bind_ok_eq]
            cases op with
            | add =>
              dsimp only
              by_cases hc : b.region = rNum ∨ a.region = rNum
              · simp only [if_pos hc]
                simp only [spSt_next, spSt_setFlags, spSt_setG δ s dn hd]
                exact okOr_pure_sp δ s _
              · simp only [if_neg hc]
                exact okOr_throw_sp δ s _
            | xor =>
              dsimp only
              exact okOr_throw_sp δ s _
            | and =>
              dsimp only
              cases hx2 : Ctl.asInt a.off with
              | none => exact okOr_throw_sp δ s _
              | some x =>
                cases hy2 : Ctl.asInt b.off with
                | none => exact okOr_throw_sp δ s _
                | some y =>
                  dsimp only
                  cases hr2 : andInt x y with
                  | none => exact okOr_throw_sp δ s _
                  | some r =>
                    by_cases hc : b.region = rNum ∧ (a.region = rNum ∨ (-64 ≤ y ∧ y < 0))
                    · simp only [if_pos hc]
                      simp only [spSt_next, spSt_clearFlags, spSt_setG δ s dn hd]
                      exact okOr_pure_sp δ s _
                    · simp only [if_neg hc]
                      exact okOr_throw_sp δ s _
            | or =>
              dsimp only
              exact okOr_throw_sp δ s _
    · simp only [if_neg hw]
      by_cases hz : op = .xor ∧ src = .reg dn
      · have hx : op = .xor := hz.1
        have hsd : src = .reg dn := hz.2
        simp only [if_pos hz]
        simp only [if_pos (show op = .xor ∧ (gs d src : GSrc) = .reg dn from
          ⟨hx, by rw [hsd]; rfl⟩)]
        simp only [spSt_next, spSt_clearFlags, spSt_setData32 δ s dn hd]
        exact okOr_pure_sp δ s _
      · simp only [if_neg hz]
        simp only [if_neg (show ¬(op = .xor ∧ (gs d src : GSrc) = .reg dn) from
          fun hc => hz ⟨hc.1, (gs_eq_reg_iff d src dn).1 hc.2⟩)]
        simp only [gData32_sp δ d hδ s src hlen hsok,
          gData32_sp_reg δ s dn hd]
        cases ha : gData32 ro mem0 s (.reg dn) with
        | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
        | ok a =>
          cases hb : gData32 ro mem0 s src with
          | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, spSt_fail]
          | ok b =>
            simp only [bind_ok_eq, spSt_next, spSt_clearFlags, spSt_setData32 δ s dn hd]
            exact okOr_pure_sp δ s _
  | sub w dn src =>
    obtain ⟨hd, hsok⟩ := hok
    simp only [addDisp]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      simp only [gCtl_sp_reg δ s dn hd, gCtl_sp δ d s src hsok]
      cases ha : gCtl s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
      | ok a =>
        cases hb : gCtl s src with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, spSt_fail]
        | ok b =>
          simp only [bind_ok_eq]
          by_cases hc : b.region = rNum
          · simp only [if_pos hc]
            simp only [spSt_next, spSt_setFlags, spSt_setG δ s dn hd]
            exact okOr_pure_sp δ s _
          · simp only [if_neg hc]
            exact okOr_throw_sp δ s _
    · simp only [if_neg hw]
      exact okOr_throw_sp δ s _
  | lea dn m =>
    obtain ⟨hd, hm⟩ := hok
    simp only [addDisp, spSt_next, effAddr_mv δ d hδ s m hlen hm, spSt_setG δ s dn hd]
    exact okOr_bind_sp δ s _ _
  | ror w dn n =>
    have hd : dn ≠ 4 := hok
    simp only [addDisp]
    by_cases hw : w = 32
    · simp only [if_pos hw]
      simp only [gData32_sp_reg δ s dn hd]
      cases ha : gData32 ro mem0 s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
      | ok a =>
        simp only [bind_ok_eq, spSt_next, spSt_clearFlags, spSt_setData32 δ s dn hd]
        exact okOr_pure_sp δ s _
    · simp only [if_neg hw]
      exact okOr_throw_sp δ s _
  | shld w dn src n =>
    obtain ⟨hd, hs⟩ := hok
    simp only [addDisp]
    by_cases hw : w = 32
    · simp only [if_pos hw]
      simp only [gData32_sp_reg δ s dn hd,
        gData32_sp_reg δ s src hs]
      cases ha : gData32 ro mem0 s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
      | ok a =>
        cases hb : gData32 ro mem0 s (.reg src) with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, spSt_fail]
        | ok b =>
          simp only [bind_ok_eq, spSt_next, spSt_clearFlags, spSt_setData32 δ s dn hd]
          exact okOr_pure_sp δ s _
    · simp only [if_neg hw]
      exact okOr_throw_sp δ s _
  | shl w dn n =>
    have hd : dn ≠ 4 := hok
    simp only [addDisp]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      simp only [gCtl_sp_reg δ s dn hd]
      cases ha : gCtl s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
      | ok a =>
        simp only [bind_ok_eq]
        by_cases hr : a.region = rNum
        · simp only [if_pos hr]
          simp only [spSt_next, spSt_clearFlags, spSt_setG δ s dn hd]
          exact okOr_pure_sp δ s _
        · simp only [if_neg hr]
          exact okOr_throw_sp δ s _
    · simp only [if_neg hw]
      simp only [gData32_sp_reg δ s dn hd]
      cases ha : gData32 ro mem0 s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
      | ok a =>
        simp only [bind_ok_eq, spSt_next, spSt_clearFlags, spSt_setData32 δ s dn hd]
        exact okOr_pure_sp δ s _
  | bswap w dn =>
    have hd : dn ≠ 4 := hok
    simp only [addDisp]
    by_cases hw : w = 32
    · simp only [if_pos hw]
      simp only [gData32_sp_reg δ s dn hd]
      cases ha : gData32 ro mem0 s (.reg dn) with
      | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
      | ok a =>
        simp only [bind_ok_eq, spSt_next, spSt_setData32 δ s dn hd]
        exact okOr_pure_sp δ s _
    · simp only [if_neg hw]
      exact okOr_throw_sp δ s _
  | push r => exact hok.elim
  | pop r => exact hok.elim
  | cmp w a b =>
    obtain ⟨ha, hsok⟩ := hok
    simp only [addDisp]
    by_cases hw : w = 64
    · simp only [if_pos hw]
      simp only [gCtl_sp_reg δ s a ha, gCtl_sp δ d s b hsok]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
      | ok x =>
        cases hy : gCtl s b with
        | error e => simp only [bind_ok_eq, bind_error_eq, okOr_error, spSt_fail]
        | ok y =>
          simp only [bind_ok_eq]
          by_cases hc : y.region = rNum ∨ y.region = x.region
          · simp only [if_pos hc]
            simp only [spSt_next, spSt_setFlags]
            exact okOr_pure_sp δ s _
          · simp only [if_neg hc]
            exact okOr_throw_sp δ s _
    · simp only [if_neg hw]
      exact okOr_throw_sp δ s _
  | test w a b =>
    obtain ⟨ha, hb⟩ := hok
    simp only [addDisp]
    by_cases hc : w = 64 ∧ a = b
    · simp only [if_pos hc]
      simp only [gCtl_sp_reg δ s a ha]
      cases hx : gCtl s (.reg a) with
      | error e => simp only [bind_error_eq, okOr_error, spSt_fail]
      | ok x =>
        simp only [bind_ok_eq]
        by_cases hr : x.region = rNum
        · simp only [if_pos hr]
          simp only [spSt_next, spSt_setFlags]
          exact okOr_pure_sp δ s _
        · simp only [if_neg hr]
          exact okOr_throw_sp δ s _
    · simp only [if_neg hc]
      exact okOr_throw_sp δ s _
  | jcc c t =>
    simp only [addDisp, spSt_flags]
    cases hf : s.flags with
    | none => exact okOr_throw_sp δ s _
    | some q =>
      obtain ⟨a, b⟩ := q
      simp only [okOr_pure]
      exact (spSt_branch δ s orc (ccCond c a b) t).symm
  | jmp t => rfl
  | jccTail c name => exact hok.elim
  | jmpTail name => exact hok.elim
  | ret => exact hok.elim

end ExecFrame

/-! ## Composing the three transfers -/

section Comb
variable {F G : Nat → Nat}
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

/-- The windows body correspondence uses its own copy of the target shift; it is the same
function. -/
theorem winShani_shiftTgt (p : Nat) (i : Instr) :
    Hashtree.Proofs.WinShani.shiftTgt p i = shiftTgt p i := by
  cases i <;> rfl

/-- **The composed instruction transfer**: displacement shift (`addDisp d`), register renaming
(`rlI F`) and program-counter shift (`shiftTgt p`) in one step, from the `δ`-lowered stack. -/
theorem exec_comb (hFG : RenPerm F G) (δ d : Int) (p : Nat) (hδ : δ + d = 0) (i : Instr)
    (s : State W32 Int) (hlen : s.gpr.length = 16) (hf : frameSafe i) (hok : okI i)
    (htr : trOk i) :
    exec ro mem0 orc (bodyI F d p i) (shiftPc p (renSt F G (spSt δ s)))
      = shiftPc p (renSt F G (spSt δ (exec ro mem0 orc i s))) := by
  simp only [bodyI, winShani_shiftTgt]
  rw [exec_shiftPc p (rlI F (addDisp d i)) (renSt F G (spSt δ s))
    ((trOk_rlI_addDisp F d i).mpr htr)]
  rw [exec_ren hFG (addDisp d i) (spSt δ s) (by simp only [spSt_gpr_len, hlen])
    (okI_addDisp d i hok)]
  rw [exec_frame δ d hδ i s hlen hf]

section Run
variable {prog winProg : Array Instr} {p : Nat}

/-- **The composed run transfer** over a slice of the two programs: `n` steps of the windows
program from the fully translated state are the translations of the `n` linux steps, provided
each linux instruction sits at windows index `p + j` as its full translation (`hmap`), every
linux instruction of the slice is `frameSafe` and `okI` (`hside`), and the linux run stays inside
the slice until it halts or returns (`hcond`). -/
theorem run_comb (hFG : RenPerm F G) (δ d : Int) (hδ : δ + d = 0)
    (hmap : ∀ j, j < prog.size → winProg[p + j]? = (prog[j]?).map (bodyI F d p))
    (hside : ∀ (pc : Nat) (x : Instr), prog[pc]? = some x → okI x ∧ frameSafe x) :
    ∀ (n : Nat) (s : State W32 Int), s.gpr.length = 16 →
      (∀ k, k < n → (run prog ro mem0 orc k s).halted = true ∨
        (run prog ro mem0 orc k s).pc < prog.size) →
      run winProg ro mem0 orc n (shiftPc p (renSt F G (spSt δ s)))
        = shiftPc p (renSt F G (spSt δ (run prog ro mem0 orc n s))) := by
  intro n
  induction n with
  | zero => intro s _ _; rfl
  | succ n ih =>
    intro s hlen hcond
    by_cases hh : s.halted = true
    · have hsh : (shiftPc p (renSt F G (spSt δ s))).halted = true := by simp [hh]
      rw [run_halted prog ro mem0 orc (n+1) s hh,
          run_halted winProg ro mem0 orc (n+1) (shiftPc p (renSt F G (spSt δ s))) hsh]
    · have hf : s.halted = false := by simpa using hh
      have h0 : s.halted = true ∨ s.pc < prog.size := by
        have h := hcond 0 (Nat.zero_lt_succ n)
        simpa only [run] using h
      have hpc : s.pc < prog.size := by
        rcases h0 with h' | h'
        · simp [hf] at h'
        · exact h'
      have hx : prog[s.pc]? = some prog[s.pc] := Array.getElem?_eq_getElem hpc
      have hside' := hside s.pc prog[s.pc] hx
      have hwx : winProg[(shiftPc p (renSt F G (spSt δ s))).pc]? =
          some (bodyI F d p prog[s.pc]) := by
        rw [shiftPc_pc, renSt_pc, spSt_pc, Nat.add_comm s.pc p, hmap s.pc hpc, hx]
        rfl
      have hshf : (renSt F G (spSt δ s)).halted = false := by simp [hf]
      have e1 : run winProg ro mem0 orc (n+1) (shiftPc p (renSt F G (spSt δ s)))
          = run winProg ro mem0 orc n
              (exec ro mem0 orc (bodyI F d p prog[s.pc])
                (shiftPc p (renSt F G (spSt δ s)))) := by
        simp only [run, hshf, Bool.false_eq_true, ite_false, hwx]
      have step : ∀ m, run prog ro mem0 orc (m+1) s
          = run prog ro mem0 orc m (exec ro mem0 orc prog[s.pc] s) := by
        intro m; simp only [run, hf, Bool.false_eq_true, ite_false, hx]
      have hlen'' : (exec ro mem0 orc prog[s.pc] s).gpr.length = 16 := by
        rw [exec_gpr_len, hlen]
      rw [e1, step n,
        exec_comb (F := F) (G := G) hFG δ d p hδ prog[s.pc] s hlen hside'.2 hside'.1
          (frameSafe_trOk prog[s.pc] hside'.2)]
      exact ih (exec ro mem0 orc prog[s.pc] s) hlen'' (fun k hk => by
        have := hcond (k+1) (Nat.succ_lt_succ hk)
        rwa [step k] at this)

end Run
end Comb

end Hashtree.Asm.X86
