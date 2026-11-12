import Hashtree.Asm.X86

/-!
# Frame: older memory writes act as initial memory

A concrete state whose write log ends in an older part `M` runs like the state without `M`,
over the initial memory seen through `M` (`view M mem0`), with `M` appended again.  This lets a
proof restart at a loop head: the writes of earlier iterations become part of the memory the
next iteration starts from.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Hashtree.Asm.X86
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

@[simp] theorem fr_getV (s : CState) (i : Nat) : (fr M s).getV i = s.getV i := rfl
@[simp] theorem fr_getG (s : CState) (i : Nat) : (fr M s).getG i = s.getG i := rfl
@[simp] theorem fr_flags (s : CState) : (fr M s).flags = s.flags := rfl
@[simp] theorem fr_pc (s : CState) : (fr M s).pc = s.pc := rfl
@[simp] theorem fr_halted (s : CState) : (fr M s).halted = s.halted := rfl
@[simp] theorem fr_err (s : CState) : (fr M s).err = s.err := rfl
@[simp] theorem fr_tail (s : CState) : (fr M s).tail = s.tail := rfl

theorem readVSrc_fr (ro : Region) (s : CState) (w : Nat) (v : VSrc) :
    readVSrc ro mem0 (fr M s) w v = readVSrc ro (view M mem0) s w v := by
  cases v <;> simp only [readVSrc, fr_getV, effAddr, baseAddr, regPtr, fr_getG, loadLanes_fr]

theorem effAddr_fr (ro : Region) (s : CState) (m : MemRef) : effAddr ro (fr M s) m = effAddr ro s m := rfl

theorem gData32_fr (ro : Region) (s : CState) (g : GSrc) :
    gData32 ro mem0 (fr M s) g = gData32 ro (view M mem0) s g := by
  cases g <;> simp only [gData32, fr_getG, effAddr_fr, loadLane_fr]

theorem gCtl_fr (s : CState) (g : GSrc) : gCtl (fr M s) g = gCtl s g := rfl

theorem next_fr (s : CState) : (fr M s).next = fr M s.next := rfl
theorem setV_fr (s : CState) (i : Nat) (v : List W32) : (fr M s).setV i v = fr M (s.setV i v) := rfl
theorem setG_fr (s : CState) (i : Nat) (v : Val W32 Int) : (fr M s).setG i v = fr M (s.setG i v) := rfl
theorem setVec_fr (s : CState) (vex : Bool) (w d : Nat) (v : List W32) :
    setVec (fr M s) vex w d v = fr M (setVec s vex w d v) := rfl
theorem setData32_fr (s : CState) (d : Nat) (x : W32) : setData32 (fr M s) d x = fr M (setData32 s d x) := rfl
theorem clearFlags_fr (s : CState) : clearFlags (fr M s) = fr M (clearFlags s) := rfl
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
theorem map_pure' (f : CState → CState) (x : CState) : (pure x : Except String CState).map f = pure (f x) := rfl
theorem map_throw' (f : CState → CState) (e : String) : (throw e : Except String CState).map f = throw e := rfl
theorem map_ite' (f : CState → CState) (c : Prop) [Decidable c] (a b : Except String CState) :
    (if c then a else b).map f = if c then a.map f else b.map f := by
  split <;> rfl

theorem map_match_except {β : Type} (f : CState → CState) (m : Except String β) (g : β → Except String CState) :
    (match m with | .error e => .error e | .ok v => g v : Except String CState).map f =
      match m with | .error e => .error e | .ok v => (g v).map f := by
  cases m <;> rfl

macro "fr_tac" : tactic => `(tactic| (
  rw [← okOr_fr]; congr 1
  simp only [readVSrc_fr, loadLanes_fr, loadVal_fr, gData32_fr, effAddr_fr, gCtl_fr, fr_getV, fr_getG,
    fr_flags, fr_pc, next_fr, setV_fr, setG_fr, setVec_fr, setData32_fr, clearFlags_fr, setFlags_fr,
    halt_fr, storeLane_fr, storeLanes_fr, storeVal_fr, branch_fr, map_bind', map_pure', map_throw',
    map_ite']
  repeat' (first
    | rfl
    | (simp only [map_bind', map_pure', map_throw', map_ite', map_match_except]; done)
    | split)
  all_goals (try simp only [map_bind', map_pure', map_throw', map_ite', map_match_except] at *)
  all_goals (try (subst_vars; rfl))
  all_goals (try simp_all only [map_bind', map_pure', map_throw', map_ite', map_match_except])))

theorem exec_fr (ro : Region) (orc : Nat → Bool) (i : Instr) (s : CState) :
    exec ro mem0 orc i (fr M s) = fr M (exec ro (view M mem0) orc i s) := by
  unfold exec
  by_cases hh : s.halted = true
  · simp only [fr_halted, hh, ite_true]
  simp only [fr_halted, hh, Bool.false_eq_true, ite_false]
  cases i
  all_goals first | rfl | fr_tac
  all_goals
    congr 1
    first
    | (congr 1; funext a; congr 1; funext b; split <;> (try split) <;> (try split) <;> rfl)
    | (congr 1; funext a; split <;> rfl)

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

end Hashtree.Asm.X86
