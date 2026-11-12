import Hashtree.Asm.Arm
import Hashtree.Asm.ArmSym

/-!
# Frame for the AArch64 model: older memory writes act as initial memory

The AArch64 counterpart of `Hashtree.Asm.X86Frame`: a concrete state whose write log ends in an
older part `M` runs like the state without `M`, over the initial memory seen through `M`
(`view M mem0`), with `M` appended again.  This is what lets a loop proof restart at a loop head:
the writes of earlier iterations become part of the memory the next iteration starts from.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Hashtree.Asm.Arm
open Hashtree.Asm

abbrev CState := State W32 Int
abbrev CLog := List (Addr Int × Cell W32 Int)

/-- Append the older log `M`. -/
def fr (M : CLog) (s : CState) : CState := { s with mem := s.mem ++ M }

/-- The initial memory seen through the log `M`. -/
def view (M : CLog) (mem0 : Addr Int → Cell W32 Int) : Addr Int → Cell W32 Int := fun a =>
  match lookup a M with
  | .ok (some c) => c
  | _ => mem0 a

variable (M : CLog) (mem0 : Addr Int → Cell W32 Int)

theorem lookup_append (a : Addr Int) : ∀ (L : CLog),
    lookup a (L ++ M) = match lookup a L with
      | .ok none => lookup a M
      | r => r
  | [] => rfl
  | (b, c) :: rest => by
    simp only [List.cons_append, lookup]
    cases AddrEq.same a b with
    | none => rfl
    | some t => cases t <;> simp only [lookup_append a rest]

theorem lookup_conc_ok (a : Addr Int) : ∀ (L : CLog), ∃ r, lookup a L = .ok r
  | [] => ⟨none, rfl⟩
  | (b, c) :: rest => by
    simp only [lookup, AddrEq.same]
    cases (a.region == b.region && a.off == b.off)
    · exact lookup_conc_ok a rest
    · exact ⟨_, rfl⟩

theorem readCell_fr (s : CState) (a : Addr Int) : readCell mem0 (fr M s) a = readCell (view M mem0) s a := by
  simp only [readCell, fr, lookup_append]
  obtain ⟨r, hr⟩ := lookup_conc_ok a s.mem
  rw [hr]
  cases r with
  | some c => rfl
  | none =>
    simp only [view]
    obtain ⟨r', hr'⟩ := lookup_conc_ok a M
    rw [hr']
    cases r' <;> rfl

theorem loadLane_fr (s : CState) (a : Addr Int) : loadLane mem0 (fr M s) a = loadLane (view M mem0) s a := by
  simp only [loadLane, readCell_fr]

theorem loadLanes_fr (s : CState) : ∀ (a : Addr Int) (n : Nat),
    loadLanes mem0 (fr M s) a n = loadLanes (view M mem0) s a n
  | _, 0 => rfl
  | a, n + 1 => by simp only [loadLanes, loadLane_fr, loadLanes_fr s _ n]

theorem pbRest_fr (s : CState) (p a : Addr Int) : ∀ (n k : Nat),
    pbRest mem0 (fr M s) p a n k = pbRest (view M mem0) s p a n k
  | 0, _ => rfl
  | n + 1, k => by simp only [pbRest, readCell_fr, pbRest_fr s p a n]

theorem loadVal_fr (s : CState) (a : Addr Int) : loadVal mem0 (fr M s) a = loadVal (view M mem0) s a := by
  simp only [loadVal, readCell_fr, pbRest_fr, loadLane_fr]

@[simp] theorem fr_getG (s : CState) (i : Nat) : (fr M s).getG i = s.getG i := rfl
@[simp] theorem fr_getV (s : CState) (i : Nat) : (fr M s).getV i = s.getV i := rfl
@[simp] theorem fr_flags (s : CState) : (fr M s).flags = s.flags := rfl
@[simp] theorem fr_pc (s : CState) : (fr M s).pc = s.pc := rfl
@[simp] theorem fr_halted (s : CState) : (fr M s).halted = s.halted := rfl
@[simp] theorem fr_err (s : CState) : (fr M s).err = s.err := rfl
@[simp] theorem fr_tail (s : CState) : (fr M s).tail = s.tail := rfl
@[simp] theorem fr_assume (s : CState) : (fr M s).assume = s.assume := rfl

@[simp] theorem fr_getQ (s : CState) (i : Nat) : getQ (fr M s) i = getQ s i := rfl
@[simp] theorem fr_getD (s : CState) (i : Nat) : getD (fr M s) i = getD s i := rfl

theorem getC_fr (s : CState) (i : Nat) : getC (fr M s) i = getC s i := rfl
theorem getW_fr (s : CState) (i : Nat) : getW (fr M s) i = getW s i := rfl
theorem getX_fr (s : CState) (i : Nat) : getX (fr M s) i = getX s i := rfl
theorem baseAddr_fr (s : CState) (n : Nat) : baseAddr (fr M s) n = baseAddr s n := rfl
theorem addrWB_fr (s : CState) (n : Nat) (i : Idx) : addrWB (fr M s) n i = addrWB s n i := rfl
theorem writeBack_fr (s : CState) (n : Nat) (w : Option (Addr Int)) :
    writeBack (fr M s) n w = fr M (writeBack s n w) := by cases w <;> rfl

theorem next_fr (s : CState) : (fr M s).next = fr M s.next := rfl
theorem setG_fr (s : CState) (i : Nat) (v : Val W32 Int) : (fr M s).setG i v = fr M (s.setG i v) := rfl
theorem setV_fr (s : CState) (i : Nat) (v : List W32) : (fr M s).setV i v = fr M (s.setV i v) := rfl
theorem setW_fr (s : CState) (d : Nat) (x : W32) : setW (fr M s) d x = fr M (setW s d x) := rfl
theorem setQ_fr (s : CState) (d : Nat) (v : List W32) : setQ (fr M s) d v = fr M (setQ s d v) := rfl
theorem setD_fr (s : CState) (d : Nat) (v : List W32) : setD (fr M s) d v = fr M (setD s d v) := rfl
theorem setFlags_fr (s : CState) (a b : Int) : setFlags (fr M s) a b = fr M (setFlags s a b) := rfl
theorem halt_fr (s : CState) : halt (fr M s) = fr M (halt s) := rfl
theorem storeLane_fr (s : CState) (a : Addr Int) (x : W32) : storeLane (fr M s) a x = fr M (storeLane s a x) := rfl
theorem storeLanes_fr : ∀ (xs : List W32) (s : CState) (a : Addr Int),
    storeLanes (fr M s) a xs = fr M (storeLanes s a xs)
  | [], _, _ => rfl
  | x :: xs, s, a => by simp only [storeLanes, storeLane_fr, storeLanes_fr xs]
theorem storeVal_fr (s : CState) (a : Addr Int) (v : Val W32 Int) :
    storeVal (fr M s) a v = fr M (storeVal s a v) := by
  cases v with
  | num lo hi => rfl
  | ptr p => simp only [storeVal, fr, List.append_assoc]
theorem branch_fr (orc : Nat → Bool) (s : CState) (c : Cond Int) (t : Nat) :
    (fr M s).branch orc c t = fr M (s.branch orc c t) := by
  simp only [State.branch, fr_pc]
  split <;> (by_cases hc : c.decideC.isNone = true <;> simp only [hc, ite_true, ite_false, Bool.false_eq_true] <;>
    split <;> rfl)
theorem fail_fr (s : CState) (e : String) : (fr M s).fail e = fr M (s.fail e) := by
  simp only [State.fail, fr_err]
  by_cases h : s.err.isSome = true <;> simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> rfl

theorem okOr_fr (s : CState) (r : Except String CState) :
    okOr (fr M s) (r.map (fr M)) = fr M (okOr s r) := by
  cases r with
  | ok s' => rfl
  | error e => simp only [Except.map, okOr, fail_fr]

theorem map_bind' {β : Type} (f : CState → CState) (m : Except String β) (g : β → Except String CState) :
    (m >>= g).map f = m >>= fun x => (g x).map f := by
  cases m <;> rfl
theorem bind_map_left {β : Type} (m : Except String β) (f : β → CState) (g : CState → Except String CState) :
    (m.map f >>= g) = m >>= fun x => g (f x) := by cases m <;> rfl
theorem map_pure' (f : CState → CState) (x : CState) : (pure x : Except String CState).map f = pure (f x) := rfl
theorem map_throw' (f : CState → CState) (e : String) : (throw e : Except String CState).map f = throw e := rfl
theorem map_ite' (f : CState → CState) (c : Prop) [Decidable c] (a b : Except String CState) :
    (if c then a else b).map f = if c then a.map f else b.map f := by
  split <;> rfl

theorem loadReg_fr (s0 s : CState) (sz : Sz) (t : Nat) (a : Addr Int) :
    loadReg mem0 (fr M s0) (fr M s) sz t a = (loadReg (view M mem0) s0 s sz t a).map (fr M) := by
  cases sz <;> simp only [loadReg, loadLane_fr, loadVal_fr, loadLanes_fr, setW_fr, setG_fr,
    setQ_fr, setD_fr, map_bind', map_pure', map_throw', map_ite'] <;> split <;> rfl

theorem storeReg_fr (s0 s : CState) (sz : Sz) (t : Nat) (a : Addr Int) :
    storeReg (fr M s0) (fr M s) sz t a = (storeReg s0 s sz t a).map (fr M) := by
  cases sz <;> simp only [storeReg, getW_fr, fr_getG, fr_getV, storeLane_fr, storeLanes_fr,
    storeVal_fr, fr_getQ, fr_getD, bind_map_left, map_bind', map_pure', map_throw', map_ite']

theorem ld1Step_fr (s st : CState) (a : Addr Int) (t j : Nat) :
    ld1Step mem0 (fr M s) a t (fr M st) j = (ld1Step (view M mem0) s a t st j).map (fr M) := by
  simp only [ld1Step, loadLanes_fr, setQ_fr, map_bind', map_pure']

theorem st1Step_fr (s st : CState) (a : Addr Int) (t j : Nat) :
    st1Step (fr M s) a t (fr M st) j = fr M (st1Step s a t st j) := by
  simp only [st1Step, fr_getQ, storeLanes_fr]

theorem ld4Step_fr (s st : CState) (a : Addr Int) (t e j : Nat) :
    ld4Step mem0 (fr M s) a t e (fr M st) j = (ld4Step (view M mem0) s a t e st j).map (fr M) := by
  simp only [ld4Step, loadLane_fr, fr_getQ, setQ_fr, map_bind', map_pure']

theorem st4Step_fr (s st : CState) (a : Addr Int) (t e j : Nat) :
    st4Step (fr M s) a t e (fr M st) j = fr M (st4Step s a t e st j) := by
  simp only [st4Step, fr_getQ, storeLane_fr]

theorem foldlM_fr {β : Type} (F G : CState → β → Except String CState)
    (h : ∀ s b, F (fr M s) b = (G s b).map (fr M)) :
    ∀ (l : List β) (s : CState), List.foldlM F (fr M s) l = (List.foldlM G s l).map (fr M)
  | [], s => rfl
  | b :: l, s => by
    simp only [List.foldlM]
    rw [h]
    cases G s b with
    | ok s' => exact foldlM_fr F G h l s'
    | error e => rfl

theorem foldl_fr {β : Type} (F G : CState → β → CState)
    (h : ∀ s b, F (fr M s) b = fr M (G s b)) :
    ∀ (l : List β) (s : CState), List.foldl F (fr M s) l = fr M (List.foldl G s l)
  | [], s => rfl
  | b :: l, s => by simp only [List.foldl, h, foldl_fr F G h l]

theorem foldlM_ld1 (s st : CState) (a : Addr Int) (t k : Nat) :
    List.foldlM (ld1Step mem0 (fr M s) a t) (fr M st) (List.range k) =
      (List.foldlM (ld1Step (view M mem0) s a t) st (List.range k)).map (fr M) :=
  foldlM_fr M _ _ (fun st j => ld1Step_fr M mem0 s st a t j) (List.range k) st

theorem foldlM_ld4 (s st : CState) (a : Addr Int) (t e : Nat) :
    List.foldlM (ld4Step mem0 (fr M s) a t e) (fr M st) (List.range 4) =
      (List.foldlM (ld4Step (view M mem0) s a t e) st (List.range 4)).map (fr M) :=
  foldlM_fr M _ _ (fun st j => ld4Step_fr M mem0 s st a t e j) (List.range 4) st

theorem foldl_st1 (s st : CState) (a : Addr Int) (t k : Nat) :
    List.foldl (st1Step (fr M s) a t) (fr M st) (List.range k) =
      fr M (List.foldl (st1Step s a t) st (List.range k)) :=
  foldl_fr M _ _ (fun st j => st1Step_fr M s st a t j) (List.range k) st

theorem foldl_st4 (s st : CState) (a : Addr Int) (t e : Nat) :
    List.foldl (st4Step (fr M s) a t e) (fr M st) (List.range 4) =
      fr M (List.foldl (st4Step s a t e) st (List.range 4)) :=
  foldl_fr M _ _ (fun st j => st4Step_fr M s st a t e j) (List.range 4) st

macro "fr_tac" : tactic => `(tactic| (
  rw [← okOr_fr]; congr 1
  simp only [getC_fr, getW_fr, getX_fr, baseAddr_fr, addrWB_fr, loadLane_fr, loadLanes_fr, loadVal_fr,
    loadReg_fr, storeReg_fr, ld1Step_fr, st1Step_fr, ld4Step_fr, st4Step_fr,
    foldlM_ld1, foldlM_ld4, foldl_st1, foldl_st4, foldlM_fr, foldl_fr,
    writeBack_fr, next_fr, setG_fr, setV_fr, setW_fr, setQ_fr, setD_fr, setFlags_fr, halt_fr,
    storeLane_fr, storeLanes_fr, storeVal_fr, branch_fr, fr_getG, fr_getV, fr_getQ, fr_getD,
    fr_flags, fr_pc,
    bind_map_left, map_bind', map_pure', map_throw', map_ite']
  repeat' (first
    | rfl
    | (simp only [bind_map_left, map_bind', map_pure', map_throw', map_ite']; done)
    | split)
  all_goals (try simp only [bind_map_left, map_bind', map_pure', map_throw', map_ite'] at *)
  all_goals (try (subst_vars; rfl))
  all_goals (try simp_all only [bind_map_left, map_bind', map_pure', map_throw', map_ite'])))

theorem exec_fr (ro : Region) (orc : Nat → Bool) (i : Instr) (s : CState) :
    exec ro mem0 orc i (fr M s) = fr M (exec ro (view M mem0) orc i s) := by
  unfold exec
  by_cases hh : s.halted = true
  · simp only [fr_halted, hh, ite_true]
  simp only [fr_halted, hh, Bool.false_eq_true, ite_false]
  cases i
  all_goals first | rfl | fr_tac
  all_goals
    try (congr 1; funext a; congr 1; funext b; split <;> (try split) <;> (try split) <;> rfl)

theorem run_fr (prog : Array Instr) (ro : Region) (orc : Nat → Bool) :
    ∀ (n : Nat) (s : CState), run prog ro mem0 orc n (fr M s) = fr M (run prog ro (view M mem0) orc n s)
  | 0, _ => rfl
  | n + 1, s => by
    simp only [run, fr_halted, fr_pc]
    by_cases hh : s.halted = true
    · simp only [hh, ite_true]
    · simp only [hh, Bool.false_eq_true, ite_false]
      cases prog[s.pc]? with
      | some i => simp only [exec_fr, run_fr prog ro orc n]
      | none => exact fail_fr M s _

end Hashtree.Asm.Arm
