import Hashtree.Proofs.WinShaniTransfer
import Hashtree.Proofs.WinNs
import Hashtree.Proofs.WinShaniEpi
import Hashtree.Proofs.WinShaniFront

/-!
# R5: the stack-write footprint of the windows `shani_x2` body

The epilogue's save-slot readback (`WinShaniEpi`) needs the body's stack image to be
`W ++ saveLog st r 10 tail` with every cell of `W` outside the 160-byte save area
`[r, r + 160)`.  The shipped scans give the ingredient at the instruction level
(`shani_save_slots_untouched`: every `rsp`-based reference of the body has
`disp + width <= 0` or `160 <= disp`), but the *semantic* statement -- a run of the body only
prepends such cells -- is what this module proves.

* `Outside` is `WinShaniEpi.Outside`; `outside_nil`/`outside_app`/`outside_cons` and
  `outside_laneLog` are the log-level lemmas.
* `wSafe` is the per-instruction write condition (only `vstore`; the scan shows the body
  contains no `movst`/`push`/`pop`), mirrored as `wSafeB` for the kernel scan.
* `exec_write_log` -- one step either leaves the write log alone (all non-writing forms,
  `exec_mem_nw`) or prepends a log outside the save area (`exec_wout`, the two writer forms).
* `run_write_log` -- the run-level induction: `n` steps of a body slice prepend a log outside
  the save area, given the step interface (`hstep`), `rsp` and `NoStackVal` facts.
* `win_body_wscan` -- the kernel-checked scan of the shipped 668-instruction body slice, and
  `win_body_wsafe`, its pointwise form.

The hypotheses `hstep`, `hsp`, `hns` are exactly the facts the transfer of `WinShaniCall`
supplies (in-slice pc from `hcond`, `rsp` and `NoStackVal` through `spSt`/`renSt`); they are
kept abstract here so that the memory engine does not depend on the transfer.
-/

open Hashtree.Asm Hashtree.Asm.X86
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Hashtree.Proofs.WinShaniWrite

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Shani.prog

open Hashtree.Proofs.WinShaniEpi (Outside plusI_off plusI_region plusI_zero)
open Hashtree.Proofs.WinShaniFront (laneLog storeLanes_rec mem_storeLanes)

/-! ## Log lemmas -/

theorem outside_nil (r : Addr Int) (w : Int) : Outside r w [] := by
  intro p hp
  cases hp

theorem outside_app (r : Addr Int) (w : Int) {L1 L2 : List (Addr Int × Cell W32 Int)}
    (h1 : Outside r w L1) (h2 : Outside r w L2) : Outside r w (L1 ++ L2) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact h1 p h
  · exact h2 p h

theorem outside_cons (r a : Addr Int) (c : Cell W32 Int)
    (L : List (Addr Int × Cell W32 Int))
    (h : a.region ≠ r.region ∨ a.off < r.off ∨ r.off + 160 ≤ a.off)
    (hL : Outside r 160 L) : Outside r 160 ((a, c) :: L) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | h'
  · rcases h with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact hL p h'

/-- A cell at offset `a + k`, `k < 4 N`, is inside the range lemma's conclusion. -/
theorem cell_cond (r a : Addr Int) (N : Nat) (k : Nat) (hk : k < 4 * N)
    (h : a.region ≠ r.region ∨ a.off + 4 * (N : Int) ≤ r.off ∨ r.off + 160 ≤ a.off) :
    (a.plusI (k : Int)).region ≠ r.region ∨ (a.plusI (k : Int)).off < r.off ∨
      r.off + 160 ≤ (a.plusI (k : Int)).off := by
  rcases h with h | h | h
  · exact Or.inl (by rw [plusI_region]; exact h)
  · refine Or.inr (Or.inl ?_)
    rw [plusI_off]
    have hki : (k : Int) < 4 * (N : Int) := by omega
    omega
  · refine Or.inr (Or.inr ?_)
    rw [plusI_off]
    have hk0 : (0 : Int) ≤ (k : Int) := by omega
    omega

theorem outside_quad (r a : Addr Int) (N : Nat) (hN : 1 ≤ N)
    (c3 c2 c1 c0 : Cell W32 Int)
    (h : a.region ≠ r.region ∨ a.off + 4 * (N : Int) ≤ r.off ∨ r.off + 160 ≤ a.off) :
    Outside r 160 [(a.plusI 3, c3), (a.plusI 2, c2), (a.plusI 1, c1), (a, c0)] := by
  have h3 : 3 < 4 * N := by omega
  have h2 : 2 < 4 * N := by omega
  have h1 : 1 < 4 * N := by omega
  have h0 : 0 < 4 * N := by omega
  apply outside_cons _ _ _ _ (cell_cond r a N 3 h3 h)
  apply outside_cons _ _ _ _ (cell_cond r a N 2 h2 h)
  apply outside_cons _ _ _ _ (cell_cond r a N 1 h1 h)
  have hc0 : a.region ≠ r.region ∨ a.off < r.off ∨ r.off + 160 ≤ a.off := by
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr h)
  apply outside_cons _ _ _ _ hc0
  exact outside_nil r 160

/-- The write log of `laneLog a xs` stays outside `[r, r + 160)` when the store address does. -/
theorem outside_laneLog (r a : Addr Int) (xs : List W32)
    (h : a.region ≠ r.region ∨ a.off + 4 * (xs.length : Int) ≤ r.off ∨
      r.off + 160 ≤ a.off) :
    Outside r 160 (laneLog a xs) := by
  induction xs generalizing a with
  | nil => exact outside_nil r 160
  | cons x xs ih =>
    simp only [laneLog]
    apply outside_app
    · apply ih
      rcases h with h | h | h
      · exact Or.inl (by rw [plusI_region]; exact h)
      · refine Or.inr (Or.inl ?_)
        rw [plusI_off]
        have h' : a.off + 4 + 4 * (xs.length : Int) ≤ r.off := by
          rw [List.length_cons] at h
          omega
        omega
      · refine Or.inr (Or.inr ?_)
        rw [plusI_off]
        omega
    · refine outside_quad r a (xs.length + 1) (by omega) _ _ _ _ ?_
      rcases h with h | h | h
      · exact Or.inl h
      · refine Or.inr (Or.inl ?_)
        rw [List.length_cons] at h
        omega
      · exact Or.inr (Or.inr h)

/-! ## Which instructions write memory -/

/-- The instructions `exec` can use to extend the write log. -/
def writesMemB : Instr → Bool
  | .vstore _ _ _ => true
  | .movst _ _ _ => true
  | .push _ => true
  | .pop _ => true
  | _ => false

/-! ## A step that does not write keeps the log -/

theorem fail_mem (s : State W32 Int) (m : String) : (s.fail m).mem = s.mem := by
  unfold State.fail
  split <;> rfl

theorem okOr_mem (s : State W32 Int) (r : Except String (State W32 Int))
    (h : ∀ s', r = .ok s' → s'.mem = s.mem) : (okOr s r).mem = s.mem := by
  cases r with
  | error e => simp only [okOr, fail_mem]
  | ok s' => exact h s' rfl

/-- A branch only moves the program counter (and records the condition). -/
theorem branch_mem (s : State W32 Int) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    (s.branch orc c t).mem = s.mem := by
  unfold State.branch
  rcases s with ⟨gpr, vr, fl, mem, pc, ha, tl, err, as⟩
  cases hcd : c.decideC <;>
    (simp only [hcd, Option.isNone_none, Option.isNone_some, ite_true, ite_false, State.next]
     split <;> rfl)

local macro "mem_close" : tactic => `(tactic| (
  repeat (first
    | rfl
    | rw [branch_mem]
    | split)))

local macro "mem_tac" : tactic => `(tactic| (
  repeat (first
    | apply EP_bind; intro _
    | apply EP_ite <;> intro _
    | apply EP_throw
    | (apply EP_pure; mem_close)
    | split)))

/-- A step whose instruction is not a memory writer leaves the write log unchanged. -/
theorem exec_mem_nw (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Instr) (s : State W32 Int) (hnw : writesMemB i = false) :
    (exec ro mem0 orc i s).mem = s.mem := by
  unfold exec
  by_cases hh : s.halted = true
  · simp only [hh, ite_true]
  simp only [hh, Bool.false_eq_true, ite_false]
  cases i <;> dsimp only
  case vstore w m src => simp only [writesMemB] at hnw; exact absurd hnw (by decide)
  case movst w m src => simp only [writesMemB] at hnw; exact absurd hnw (by decide)
  case push r => simp only [writesMemB] at hnw; exact absurd hnw (by decide)
  case pop r => simp only [writesMemB] at hnw; exact absurd hnw (by decide)
  all_goals first
    | rfl
    | (apply okOr_mem; mem_tac)

/-! ## Effective addresses of the writer forms -/

theorem effAddr_rsp (ro : Region) (s : State W32 Int) (m : MemRef) (r a : Addr Int)
    (hro : m.ro = none) (hb : m.base = some 4) (hidx : m.index = none)
    (hsp : s.getG 4 = .ptr r) (ha : effAddr ro s m = .ok a) :
    a = r.plusI m.disp := by
  unfold effAddr baseAddr at ha
  simp only [hro, hb, hidx, regPtr, hsp] at ha
  injection ha with h
  exact h.symm

theorem effAddr_reg (ro : Region) (s : State W32 Int) (m : MemRef) (b : Nat) (a : Addr Int)
    (hro : m.ro = none) (hb : m.base = some b)
    (ha : effAddr ro s m = .ok a) :
    ∃ q : Addr Int, s.getG b = .ptr q ∧ a.region = q.region := by
  unfold effAddr baseAddr at ha
  simp only [hro, hb] at ha
  cases hg : s.getG b with
  | num lo hi =>
    simp only [regPtr, hg] at ha
    cases ha
  | ptr q =>
    cases hidx : m.index with
    | none =>
      simp only [regPtr, hg, hidx] at ha
      injection ha with h
      exact ⟨q, rfl, by rw [← h]; rfl⟩
    | some i =>
      cases hgi : s.getG i with
      | num lo hi =>
        simp only [regPtr, hg, hidx, hgi] at ha
        cases ha
      | ptr q' =>
        obtain ⟨reg, off⟩ := q'
        cases reg with
        | zero =>
          simp only [regPtr, hg, hidx, hgi] at ha
          injection ha with h
          exact ⟨q, rfl, by rw [← h]; rfl⟩
        | succ reg =>
          simp only [regPtr, hg, hidx, hgi] at ha
          cases ha

theorem effAddr_abs (ro : Region) (s : State W32 Int) (m : MemRef) (a : Addr Int)
    (hro : m.ro = none) (hb : m.base = none)
    (ha : effAddr ro s m = .ok a) : a.region = rNum := by
  unfold effAddr baseAddr at ha
  simp only [hro, hb] at ha
  cases hidx : m.index with
  | none =>
    simp only [hidx] at ha
    injection ha with h
    rw [← h]
    rfl
  | some i =>
    cases hgi : s.getG i with
    | num lo hi =>
      simp only [hidx, hgi] at ha
      cases ha
    | ptr q =>
      obtain ⟨reg, off⟩ := q
      cases reg with
      | zero =>
        simp only [hidx, hgi] at ha
        injection ha with h
        rw [← h]
        rfl
      | succ reg =>
        simp only [hidx, hgi] at ha
        cases ha

/-! ## The write condition of one instruction -/

/-- `sp0` is the offset of the body's `rsp` from the save-area base `r` (for the linux body of
`shani_x2`, `rsp = r + 160`).  The write condition of the body slice: only `vstore` writes (the
scan shows there is no `movst`/`push`/`pop`), its operand has no `rip` relocation, is `mSafe` (no
`rsp` index, and `rsp`-based operands carry no index and no relocation), and an `rsp`-based store
keeps the `4w` stored bytes clear of the save area: `sp0 + disp + 4w <= 0` (below the area) or
`160 <= sp0 + disp` (above it).  For a store through another base register the region is
supplied by `NoStackVal`. -/
def wSafe (sp0 : Int) (i : Instr) : Prop :=
  match i with
  | .vstore w m _ => m.ro = none ∧ mSafe m ∧
      (m.base = some 4 → sp0 + m.disp + (4 * (w : Int)) ≤ 0 ∨ 160 ≤ sp0 + m.disp)
  | .movst _ _ _ => False
  | .push _ => False
  | .pop _ => False
  | _ => True

/-- Boolean, kernel-reducible form of `wSafe`. -/
def wSafeB (sp0 : Int) : Instr → Bool
  | .vstore w m _ => m.ro.isNone && mSafeB m &&
      (if m.base = some (4 : Nat) then
        (decide (sp0 + m.disp + (4 * (w : Int)) ≤ 0) || decide (160 ≤ sp0 + m.disp))
       else true)
  | .movst _ _ _ => false
  | .push _ => false
  | .pop _ => false
  | _ => true

theorem wSafeB_iff (sp0 : Int) (i : Instr) : (wSafeB sp0 i = true) ↔ wSafe sp0 i := by
  cases i <;>
    simp only [wSafeB, wSafe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true,
      decide_eq_true_eq, beq_iff_eq, Option.isNone_iff_eq_none, mSafeB_iff,
      Bool.false_eq_true]
  case vstore w m src =>
    by_cases hb : m.base = some 4 <;>
      simp [hb, mSafeB_iff, Option.isNone_iff_eq_none, and_assoc]
  all_goals simp

/-! ## One step -/

/-- A body instruction either leaves the write log alone (the non-writer forms) or prepends a log
whose cells all lie outside the 160-byte save area `[r, r + 160)`. -/
theorem exec_write_log (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (i : Instr) (s : State W32 Int) (r : Addr Int) (sp0 : Int)
    (hr : r.region = rStack) (hsp : s.getG 4 = .ptr (r.plusI sp0))
    (hns : ∀ j, j ≠ 4 → NoStackVal (s.getG j)) (hws : wSafe sp0 i) :
    ∃ L, (exec ro mem0 orc i s).mem = L ++ s.mem ∧ Outside r 160 L := by
  cases i
  case vstore w m src =>
    simp only [wSafe] at hws
    obtain ⟨hro, hmsafe, hdisp⟩ := hws
    by_cases hh : s.halted = true
    · exact ⟨[], by simp only [exec, hh, ite_true]; rfl, outside_nil r 160⟩
    · have hhf : s.halted = false := by
        cases hs : s.halted with
        | false => rfl
        | true => exact absurd hs hh
      simp only [exec, hhf, Bool.false_eq_true, ite_false]
      cases he : effAddr ro s m with
      | error e =>
        exact ⟨[], by simp only [bind_error_eq, okOr_error, fail_mem]; rfl, outside_nil r 160⟩
      | ok a =>
        refine ⟨laneLog a ((s.getV src).take w), ?_, ?_⟩
        · rw [bind_ok_eq, okOr_pure]
          simp only [State.next, mem_storeLanes]
        · rcases hmb : m.base with _ | b
          · refine outside_laneLog r a _ (Or.inl ?_)
            rw [effAddr_abs ro s m a hro hmb he, hr]
            intro h
            cases h
          · by_cases hb4 : b = 4
            · subst hb4
              have hidx : m.index = none := (hmsafe.2 hmb).2
              have haeq : a = (r.plusI sp0).plusI m.disp :=
                effAddr_rsp ro s m (r.plusI sp0) a hro hmb hidx hsp he
              rw [haeq]
              apply outside_laneLog
              rw [plusI_off, plusI_off]
              rcases hdisp hmb with h | h
              · refine Or.inr (Or.inl ?_)
                have hlen : (((s.getV src).take w).length : Int) ≤ (w : Int) := by
                  have hle := List.length_take_le (l := s.getV src) (i := w)
                  omega
                omega
              · refine Or.inr (Or.inr ?_)
                omega
            · obtain ⟨q, hq, hqreg⟩ := effAddr_reg ro s m b a hro hmb he
              refine outside_laneLog r a _ (Or.inl ?_)
              rw [hqreg, hr]
              exact hns b hb4 q hq
  case movst w m src =>
    simp only [wSafe] at hws
  case push r' =>
    simp only [wSafe] at hws
  case pop r' =>
    simp only [wSafe] at hws
  all_goals
    refine ⟨[], ?_, outside_nil r 160⟩
    rw [exec_mem_nw ro mem0 orc _ s (by rfl)]
    rfl

/-! ## A run of the body slice -/

section RunWrite
variable {ro : Region} {prog : Array Instr} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

/-- `n` steps of a body slice prepend a log outside the save area, provided every instruction of
the slice is `wSafe`, the run stays inside the slice (or has halted), and `rsp`/`NoStackVal` are
maintained along the run. -/
theorem run_write_log (sp0 : Int) {base L : Nat}
    (hwsI : ∀ pc i, base ≤ pc → pc < base + L → prog[pc]? = some i → wSafe sp0 i)
    (hLsize : base + L ≤ prog.size) :
    ∀ (n : Nat) (s : State W32 Int) (r : Addr Int), r.region = rStack →
    (∀ k, k ≤ n → (run prog ro mem0 orc k s).getG 4 = .ptr (r.plusI sp0)) →
    (∀ k, k ≤ n → ∀ j, j ≠ 4 → NoStackVal ((run prog ro mem0 orc k s).getG j)) →
    (∀ k, k < n → (run prog ro mem0 orc k s).halted = true ∨
      (base ≤ (run prog ro mem0 orc k s).pc ∧
        (run prog ro mem0 orc k s).pc < base + L)) →
    ∃ M, (run prog ro mem0 orc n s).mem = M ++ s.mem ∧ Outside r 160 M := by
  intro n
  induction n with
  | zero =>
    intro s r hr hsp hns hcond
    exact ⟨[], rfl, outside_nil r 160⟩
  | succ n ih =>
    intro s r hr hsp hns hcond
    by_cases hh : s.halted = true
    · rw [run_halted prog ro mem0 orc (n + 1) s hh]
      exact ⟨[], rfl, outside_nil r 160⟩
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
      have hsp' : ∀ k', k' ≤ n →
          (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).getG 4
            = .ptr (r.plusI sp0) := by
        intro k' hk'
        have h1 := hsp (k' + 1) (by omega)
        rwa [step k'] at h1
      have hns' : ∀ k', k' ≤ n → ∀ j, j ≠ 4 →
          NoStackVal ((run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).getG j) := by
        intro k' hk' j hj
        have h1 := hns (k' + 1) (by omega) j hj
        rwa [step k'] at h1
      have hcond' : ∀ k', k' < n →
          (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).halted = true ∨
          (base ≤ (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).pc ∧
            (run prog ro mem0 orc k' (exec ro mem0 orc prog[s.pc] s)).pc < base + L) := by
        intro k' hk'
        have h1 := hcond (k' + 1) (Nat.succ_lt_succ hk')
        rwa [step k'] at h1
      obtain ⟨M, hM, hOut⟩ := ih (exec ro mem0 orc prog[s.pc] s) r hr hsp' hns' hcond'
      obtain ⟨Lw, hLw, hLout⟩ :=
        exec_write_log ro mem0 orc prog[s.pc] s r sp0 hr
          (hsp 0 (Nat.zero_le _)) (fun j hj => hns 0 (Nat.zero_le _) j hj)
          (hwsI s.pc prog[s.pc] hpc.1 hpc.2 hx)
      refine ⟨M ++ Lw, ?_, outside_app r 160 hOut hLout⟩
      rw [step n, hM, hLw, List.append_assoc]

end RunWrite

end Hashtree.Proofs.WinShaniWrite
