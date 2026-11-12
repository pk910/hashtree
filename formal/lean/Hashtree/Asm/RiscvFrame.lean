import Hashtree.Asm.X86Frame
import Hashtree.Asm.Riscv

/-!
# Frame for RV64 runs: older memory writes act as initial memory

`X86Frame` for `Riscv.exec`/`Riscv.run`: the log-append framing (`fr`, `view`) and the memory
reads are machine independent (`Core`), so only the instruction effects need new lemmas.  Used to
restart a proof at a loop head: the writes of earlier iterations become part of the initial
memory the next iteration runs over.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Hashtree.Asm.Riscv
open Hashtree.Asm Hashtree.Asm.X86

abbrev CState := State W32 Int
abbrev CLog := List (Addr Int × Cell W32 Int)

variable (M : CLog) (mem0 : Addr Int → Cell W32 Int)

theorem okOr_fr (s : CState) (r : Except String CState) :
    okOr (fr M s) (r.map (fr M)) = fr M (okOr s r) := by
  cases r with
  | ok s' => rfl
  | error e => simp only [Except.map, okOr, fail_fr]

@[simp] theorem rget_fr (s : CState) (i : Nat) : rget (fr M s) i = rget s i := by
  simp only [rget, fr_getG]

theorem rset_fr (s : CState) (i : Nat) (v : Val W32 Int) : rset (fr M s) i v = fr M (rset s i v) := by
  simp only [rset]; split <;> rfl

theorem next_fr (s : CState) : (fr M s).next = fr M s.next := rfl
theorem halt_fr (s : CState) : halt (fr M s) = fr M (halt s) := rfl
theorem setPc_fr (s : CState) (k : Nat) : setPc (fr M s) k = fr M (setPc s k) := rfl
theorem haltTail_fr (s : CState) (name : String) : haltTail (fr M s) name = fr M (haltTail s name) := rfl
theorem callOut_fr (s : CState) (pc : Nat) (name : String) :
    callOut (fr M s) pc name = fr M (callOut s pc name) := rfl
theorem assumeC_fr (s : CState) (cs : List (Cond Int × Bool)) :
    assumeC (fr M s) cs = fr M (assumeC s cs) := rfl
theorem link_fr (env : Env) (s : CState) (d : Nat) : link env (fr M s) d = fr M (link env s d) := by
  simp only [link, rset_fr, fr_pc]

theorem ea_fr (s : CState) (b : Nat) (off : Int) : ea (fr M s) b off = ea s b off := by
  simp only [ea, rget_fr]

theorem jumpTo_fr (env : Env) (s : CState) (d : Nat) (t : Addr Int) :
    jumpTo env (fr M s) d t = (jumpTo env s d t).map (fr M) := by
  simp only [jumpTo]
  split <;> (try split) <;> (try split) <;>
    simp only [halt_fr, setPc_fr, haltTail_fr, callOut_fr, link_fr, fr_pc, map_pure', map_throw',
      map_ite']

theorem slliV_fr (s : CState) (d : Nat) (v : Val W32 Int) (n : Nat) :
    slliV (fr M s) d v n = (slliV s d v n).map (fr M) := by
  simp only [slliV]
  split <;> (try split) <;> (try split) <;>
    simp only [rset_fr, next_fr, assumeC_fr, map_pure', map_throw']

macro "fr_tac" : tactic => `(tactic| (
  rw [← okOr_fr]; congr 1
  simp only [rget_fr, rset_fr, next_fr, ea_fr, loadLane_fr, loadVal_fr, storeLane_fr,
    storeVal_fr, branch_fr, jumpTo_fr, slliV_fr, fr_getG, fr_halted]
  repeat' (first
    | rfl
    | (simp only [map_bind', map_pure', map_throw', map_ite', map_match_except]; done)
    | split)
  all_goals (try simp only [map_bind', map_pure', map_throw', map_ite', map_match_except] at *)
  all_goals (try (subst_vars; rfl))
  all_goals (try simp_all only [map_bind', map_pure', map_throw', map_ite', map_match_except])))

theorem exec_fr (env : Env) (orc : Nat → Bool) (i : Instr) (s : CState) :
    exec env mem0 orc i (fr M s) = fr M (exec env (view M mem0) orc i s) := by
  unfold exec
  by_cases hh : s.halted = true
  · simp only [fr_halted, hh, ite_true]
  simp only [fr_halted, hh, Bool.false_eq_true, ite_false]
  cases i
  all_goals first
    | rfl
    | (simp only [rget_fr, rset_fr, next_fr, link_fr, setPc_fr, fr_pc, fail_fr]; done)
    | fr_tac
  all_goals
    congr 1
    first
    | (congr 1; funext a; congr 1; funext b; split <;> (try split) <;> (try split) <;> rfl)
    | (congr 1; funext a; split <;> rfl)

theorem run_fr (prog : Array Instr) (env : Env) (orc : Nat → Bool) :
    ∀ (n : Nat) (s : CState), run prog env mem0 orc n (fr M s) = fr M (run prog env (view M mem0) orc n s)
  | 0, _ => rfl
  | n + 1, s => by
    simp only [run, fr_halted, fr_pc]
    by_cases hh : s.halted = true
    · simp only [hh, ite_true]
    · simp only [hh, Bool.false_eq_true, ite_false]
      cases prog[s.pc]? with
      | some i => simp only [exec_fr, run_fr prog env orc n]
      | none => exact fail_fr M s _

end Hashtree.Asm.Riscv
