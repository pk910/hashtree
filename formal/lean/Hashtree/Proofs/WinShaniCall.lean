import Hashtree.Proofs.WinShaniEpi
import Hashtree.Proofs.WinShaniTransfer
import Hashtree.Proofs.WinShaniFlags

/-!
# R5: the `shani_x2` complete-call composition

This module composes the three pieces proved so far into a single run of the shipped windows
stream:

```
pc 0        sub rsp, 248                     (WinShaniFront.run_prologue, 11 steps)
pc 11..678  668-instruction body             (WinShaniTransfer.shani_body_transfer)
pc 679..690  ten xmm restores, add rsp, 248, ret   (WinShaniEpi.run_epilogue, 12 steps)
```

The prologue lands in `saveSt st a 10`, the windows-flags state.  The linux body certificate
starts from the flags of `sub rsp, 88` (the linux prologue), so `WinShaniFlags.run_flags` first
replaces the entry flags by `some (a.off, 88)`; the resulting state is exactly the translated
linux body-entry state `shiftPc 10 (renSt F G (spSt (-160) (seedSt st a)))`
(`shani_seed_eq`).  The body transfer then carries the 668-instruction body over, and the
epilogue replay finishes the call.

What the composition takes as hypotheses are the body-exit facts (`hpc`, `hnh`, `hrsp` on the
linux state, and the shape `W ++ saveLog ...` with `Outside r 160 W` for the stack image).  These
are the facts a stack-footprint engine over the body slice will supply; the composition itself is
independent of how they are proved.

Axiom accounting is in the `R5: windows amd64` block of `Axioms.lean`.
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinShani (F G)
open Hashtree.Proofs.WinShaniFront
open Hashtree.Proofs.WinShaniEpi
open Hashtree.Proofs.WinShaniTransfer
open Hashtree.Proofs.WinShaniFlags
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Hashtree.Proofs.WinShaniCall

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.Shani.prog
abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Shani.prog

/-! ## The linux body-entry seed -/

/-- The linux body-entry seed belonging to a windows ABI entry state: the register file of `st`
with the roles permuted back (register `j` holds windows register `F j`), `rsp` lowered by `88`
(the linux `sub rsp, 88`), the prologue flags, pc `1` and the windows save log on top of the
linux entry memory. -/
def seedSt (st : State W32 Int) (a : Addr Int) : State W32 Int :=
  { st with
      gpr := (List.range 16).map (fun j =>
        if j = 4 then .ptr (a.plusI (-88)) else st.getG (F j)),
      flags := some (a.off, 88),
      pc := 1,
      mem := saveLog st (a.plusI (-248)) 10 st.mem }

theorem g_lt : ∀ j, j < 16 → G j < 16 := by
  apply Hashtree.Proofs.WinShani.all_fin
  decide

theorem f_lt16 : ∀ j, j < 16 → F j < 16 := Hashtree.Proofs.WinShani.f_lt

theorem fg16 : ∀ j, j < 16 → F (G j) = j := Hashtree.Proofs.WinShani.fg

theorem gf16 : ∀ j, j < 16 → G (F j) = j := Hashtree.Proofs.WinShani.gf

theorem G4 : G 4 = 4 := rfl

theorem F4 : F 4 = 4 := rfl

theorem seedSt_gpr_len (st : State W32 Int) (a : Addr Int) : (seedSt st a).gpr.length = 16 := by
  simp only [seedSt, List.length_map, List.length_range]

theorem seedSt_getG (st : State W32 Int) (a : Addr Int) (j : Nat) (hj : j < 16) :
    (seedSt st a).getG j = if j = 4 then .ptr (a.plusI (-88)) else st.getG (F j) := by
  simp only [seedSt, State.getG, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

/-- Reading register `i` of the renamed state: it holds linux register `G i`. -/
theorem renSt_getG16 (X : State W32 Int) (i : Nat) (hi : i < 16) :
    (renSt F G X).getG i = X.getG (G i) := by
  have hgi : G i < 16 := g_lt i hi
  have h := renSt_getG F G X (G i) (f_lt16 (G i) hgi) (gf16 (G i) hgi)
  rwa [fg16 i hi] at h

/-- Reading register `i` after the windows prologue. -/
theorem saveSt_getG (st : State W32 Int) (a : Addr Int) (hlen : st.gpr.length = 16)
    (i : Nat) (hi : i < 16) :
    (saveSt st a 10).getG i = if i = 4 then .ptr (a.plusI (-248)) else st.getG i := by
  by_cases h4 : i = 4
  · subst h4
    rw [ite_eq_left (show (4 : Nat) = 4 from rfl)]
    show (st.gpr.set 4 (.ptr (a.plusI (-248)))).getD 4
        (Val.num (Lane.const 0) (Lane.const 0)) = .ptr (a.plusI (-248))
    rw [getD_set_self st.gpr 4 (by rw [hlen]; omega)]
  · rw [ite_eq_right h4]
    show (st.gpr.set 4 (.ptr (a.plusI (-248)))).getD i
        (Val.num (Lane.const 0) (Lane.const 0))
      = st.gpr.getD i (Val.num (Lane.const 0) (Lane.const 0))
    rw [getD_set_ne st.gpr 4 i (Ne.symm h4)]

/-- The prologue's result state is the translated linux body-entry seed. -/
theorem shani_seed_eq (st : State W32 Int) (a : Addr Int) (hlen : st.gpr.length = 16) :
    { saveSt st a 10 with flags := some (a.off, 88) }
      = shiftPc 10 (renSt F G (spSt (-160) (seedSt st a))) := by
  have hlenX : (seedSt st a).gpr.length = 16 := seedSt_gpr_len st a
  have hlenS : (saveSt st a 10).gpr.length = 16 := by
    simp only [saveSt, List.length_set, hlen]
  have hgpr : (renSt F G (spSt (-160) (seedSt st a))).gpr = (saveSt st a 10).gpr := by
    apply List.ext_getElem
    · simp only [renSt_gpr_len, hlenS]
    · intro i h1 h2
      rw [List.getElem_eq_getD (l := (renSt F G (spSt (-160) (seedSt st a))).gpr)
            (fallback := (Val.num (Lane.const 0) (Lane.const 0))),
          List.getElem_eq_getD (l := (saveSt st a 10).gpr)
            (fallback := (Val.num (Lane.const 0) (Lane.const 0)))]
      show (renSt F G (spSt (-160) (seedSt st a))).getG i = (saveSt st a 10).getG i
      by_cases hi4 : i = 4
      · subst hi4
        rw [renSt_getG16 _ 4 (by omega), G4]
        rw [spSt_getG_self (-160) (seedSt st a) (by rw [hlenX]; omega)]
        rw [seedSt_getG st a 4 (by omega), ite_eq_left (show (4 : Nat) = 4 from rfl)]
        rw [saveSt_getG st a hlen 4 (by omega), ite_eq_left (show (4 : Nat) = 4 from rfl)]
        show Val.ptr ((a.plusI (-88)).plusI (-160)) = Val.ptr (a.plusI (-248))
        rw [plusI_add]
        rfl
      · rw [renSt_getG16 _ i (by omega)]
        have hg4 : G i ≠ 4 := by
          intro h
          have h1 : F (G i) = F 4 := by rw [h]
          rw [fg16 i (by omega), F4] at h1
          exact hi4 h1
        rw [spSt_getG_ne (-160) (seedSt st a) (G i) hg4]
        rw [seedSt_getG st a (G i) (g_lt i (by omega)), ite_eq_right hg4]
        rw [fg16 i (by omega)]
        rw [saveSt_getG st a hlen i (by omega), ite_eq_right hi4]
  rcases st with ⟨gpr, vr, fl, me, pc0, ha, tl, er, as⟩
  simp only [renSt, spSt, seedSt, State.getG] at hgpr
  simp only [saveSt, shiftPc, renSt, spSt, seedSt, State.getG]
  rw [hgpr]
  rfl

/-! ## The translated body-exit state -/

/-- The windows body-exit state belonging to the linux body-exit state `S`. -/
def bodyExit (S : State W32 Int) : State W32 Int :=
  shiftPc 10 (renSt F G (spSt (-160) S))

theorem bodyExit_halted (S : State W32 Int) : (bodyExit S).halted = S.halted := rfl
theorem bodyExit_pc (S : State W32 Int) : (bodyExit S).pc = S.pc + 10 := rfl
theorem bodyExit_mem (S : State W32 Int) : (bodyExit S).mem = S.mem := rfl
theorem bodyExit_vr (S : State W32 Int) : (bodyExit S).vr = S.vr := rfl

theorem bodyExit_gpr_len (S : State W32 Int) : (bodyExit S).gpr.length = 16 :=
  renSt_gpr_len F G _

theorem bodyExit_vr_len (S : State W32 Int) (h : 16 ≤ S.vr.length) : 16 ≤ (bodyExit S).vr.length :=
  h

theorem bodyExit_getG (S : State W32 Int) (j : Nat) (hj : j < 16) :
    (bodyExit S).getG j = (spSt (-160) S).getG (G j) := by
  rw [bodyExit, shiftPc_getG]
  exact renSt_getG16 _ j hj

/-- The body exit keeps the (windows) stack pointer of the prologue. -/
theorem bodyExit_getG_rsp (S : State W32 Int) (a : Addr Int) (hlen : S.gpr.length = 16)
    (h : S.getG rsp = .ptr (a.plusI (-88))) :
    (bodyExit S).getG rsp = .ptr (a.plusI (-248)) := by
  show (bodyExit S).getG 4 = Val.ptr (a.plusI (-248))
  rw [bodyExit_getG S 4 (by decide), G4]
  rw [spSt_getG_self (-160) S (by rw [hlen]; omega)]
  rw [show S.getG 4 = S.getG rsp from rfl]
  rw [h]
  show Val.ptr ((a.plusI (-88)).plusI (-160)) = Val.ptr (a.plusI (-248))
  rw [plusI_add]
  rfl

/-! ## Lengths are preserved by the run -/

section Lengths
variable {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}

@[simp] theorem vr_len_setG (s : State W32 Int) (i : Nat) (v : Val W32 Int) :
    (s.setG i v).vr.length = s.vr.length := rfl

@[simp] theorem vr_len_setV (s : State W32 Int) (i : Nat) (v : List W32) :
    (s.setV i v).vr.length = s.vr.length := by
  simp only [State.setV, List.length_set]

@[simp] theorem vr_len_next (s : State W32 Int) : s.next.vr.length = s.vr.length := rfl

@[simp] theorem vr_len_branch (s : State W32 Int) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    (s.branch orc c t).vr.length = s.vr.length := by
  unfold State.branch
  dsimp only
  repeat (first | rfl | split)

@[simp] theorem vr_len_clearFlags (s : State W32 Int) :
    (clearFlags s).vr.length = s.vr.length := rfl

@[simp] theorem vr_len_setFlags (s : State W32 Int) (a b : Int) :
    (setFlags s a b).vr.length = s.vr.length := rfl

@[simp] theorem vr_len_halt (s : State W32 Int) : (halt s).vr.length = s.vr.length := rfl

@[simp] theorem vr_len_fail (s : State W32 Int) (m : String) :
    (s.fail m).vr.length = s.vr.length := by
  simp only [State.fail]
  split <;> rfl

@[simp] theorem vr_len_setVec (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) :
    (setVec s vex w d v).vr.length = s.vr.length := by
  simp only [setVec, vr_len_setV]

@[simp] theorem vr_len_setData32 (s : State W32 Int) (d : Nat) (x : W32) :
    (setData32 s d x).vr.length = s.vr.length := by
  simp only [setData32, vr_len_setG]

@[simp] theorem vr_len_storeLane (s : State W32 Int) (a : Addr Int) (x : W32) :
    (storeLane s a x).vr.length = s.vr.length := rfl

@[simp] theorem vr_len_storeLanes : ∀ (v : List W32) (s : State W32 Int) (a : Addr Int),
    (storeLanes s a v).vr.length = s.vr.length
  | [], s, a => rfl
  | x :: xs, s, a => by
    simp only [storeLanes]
    exact vr_len_storeLanes xs (storeLane s a x) (a.plusI 4)

@[simp] theorem vr_len_storeVal (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) :
    (storeVal s a v).vr.length = s.vr.length := by
  cases v with
  | num lo hi => simp only [storeVal, vr_len_storeLane]
  | ptr p => rfl

theorem okOr_vr_len (s : State W32 Int) (r : Except String (State W32 Int))
    (h : EP (fun t : State W32 Int => t.vr.length = s.vr.length) r) :
    (okOr s r).vr.length = s.vr.length := by
  cases r with
  | ok t => exact h t rfl
  | error e => simp only [okOr_error, vr_len_fail]

local macro "vlen_tac" : tactic => `(tactic| (
  repeat (first
    | apply EP_bind; intro _
    | apply EP_throw
    | apply EP_ite <;> intro _
    | (apply EP_pure; simp)
    | split)))

/-- An instruction's execution keeps the vector-register-list length. -/
theorem exec_vr_len (i : Instr) (s : State W32 Int) :
    (exec ro mem0 orc i s).vr.length = s.vr.length := by
  unfold exec
  by_cases hh : s.halted = true
  · simp only [hh, ite_true]
  simp only [hh, Bool.false_eq_true, ite_false]
  cases i <;> dsimp only
  all_goals first
    | rfl
    | (apply okOr_vr_len; vlen_tac)

local macro "glen_tac" : tactic => `(tactic| (
  repeat (first
    | apply EP_bind; intro _
    | apply EP_throw
    | apply EP_ite <;> intro _
    | (apply EP_pure; simp)
    | split)))

/-- An instruction's execution keeps the general-register-list length. -/
theorem exec_gpr_len16 (i : Instr) (s : State W32 Int) :
    (exec ro mem0 orc i s).gpr.length = s.gpr.length := by
  unfold exec
  by_cases hh : s.halted = true
  · simp only [hh, ite_true]
  simp only [hh, Bool.false_eq_true, ite_false]
  cases i <;> dsimp only
  all_goals first
    | rfl
    | (apply okOr_len; glen_tac)

/-- `n` steps keep the vector-register-list length. -/
theorem run_vr_len (prog : Array Instr) (n : Nat) (s : State W32 Int) (h : s.vr.length = 16) :
    (run prog ro mem0 orc n s).vr.length = 16 := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    by_cases hh : s.halted = true
    · rw [run_halted prog ro mem0 orc (n + 1) s hh]; exact h
    · simp only [run, hh, Bool.false_eq_true, ite_false]
      split
      · apply ih
        rw [exec_vr_len, h]
      · rw [vr_len_fail, h]

/-- `n` steps keep the general-register-list length. -/
theorem run_gpr_len (prog : Array Instr) (n : Nat) (s : State W32 Int)
    (h : s.gpr.length = 16) :
    (run prog ro mem0 orc n s).gpr.length = 16 := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    by_cases hh : s.halted = true
    · rw [run_halted prog ro mem0 orc (n + 1) s hh]; exact h
    · simp only [run, hh, Bool.false_eq_true, ite_false]
      split
      · apply ih
        rw [exec_gpr_len16, h]
      · rw [gpr_len_fail, h]

end Lengths

/-! ## The body run -/

/-- **Prologue and body.**  `11 + n` instructions of the shipped windows stream from the ABI
entry state are the translated `n` steps of the linux body from the seed `seedSt`.  The entry
flags of the windows prologue are replaced by the linux ones by `run_flags`, and `shani_seed_eq`
identifies the state from which the linux body certificate starts. -/
theorem shani_call_run {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (st : State W32 Int) (a : Addr Int) (n : Nat)
    (v : List W32) (x : Addr Int)
    (hlen : st.gpr.length = 16) (hh : st.halted = false) (h4 : st.getG rsp = .ptr a)
    (hv : readVSrc ro mem0 (saveSt st a 10) 4 m256 = .ok v)
    (hx : gCtl (saveSt st a 10) (.reg 8) = .ok x)
    (hcond : ∀ k, k < n → (run linuxProg ro mem0 orc k (seedSt st a)).halted = true ∨
      (1 ≤ (run linuxProg ro mem0 orc k (seedSt st a)).pc ∧
        (run linuxProg ro mem0 orc k (seedSt st a)).pc < 669)) :
    run winProg ro mem0 orc (11 + (n + 12)) { st with pc := 0 }
      = run winProg ro mem0 orc 12 (bodyExit (run linuxProg ro mem0 orc n (seedSt st a))) := by
  rw [run_add (a := 11) (b := n + 12)]
  rw [run_prologue ro mem0 orc st a hh h4 hlen]
  rw [run_flags st a (some (a.off, 88)) v x hh hv hx (n + 12) (by omega)]
  rw [run_add (a := n) (b := 12)]
  rw [shani_seed_eq st a hlen]
  rw [shani_body_transfer ro mem0 orc n (seedSt st a) (seedSt_gpr_len st a) hcond]
  rfl

/-! ## The whole call -/

/-- **The `shani_x2` complete call.**  The shipped windows stream (`702` instructions) run from
the ABI entry state `st` (`rsp` holding the return-address pointer `a`) for `11 + n + 12` steps
ends in the epilogue-final state: halted, `rsp = a + 8` (`epiFinal_getG_rsp`), the ten
callee-saved vector registers restored to their entry low four lanes
(`shani_call_getV`).

The hypotheses after `hcond` are the body-exit facts: the linux body reaches pc `669` unhalted
with `rsp` unchanged, and its stack image is `W ++ saveLog st r 10 tail` with `W` outside the
160-byte save area.  `ret` reads the return pointer at `[r + 248] = [a]`. -/
theorem shani_call {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (st : State W32 Int) (a : Addr Int) (n : Nat) (tail W : CLog)
    (v : List W32) (x : Addr Int)
    (hlen : st.gpr.length = 16) (hh : st.halted = false) (h4 : st.getG rsp = .ptr a)
    (hv : readVSrc ro mem0 (saveSt st a 10) 4 m256 = .ok v)
    (hx : gCtl (saveSt st a 10) (.reg 8) = .ok x)
    (hcond : ∀ k, k < n → (run linuxProg ro mem0 orc k (seedSt st a)).halted = true ∨
      (1 ≤ (run linuxProg ro mem0 orc k (seedSt st a)).pc ∧
        (run linuxProg ro mem0 orc k (seedSt st a)).pc < 669))
    (hpc : (run linuxProg ro mem0 orc n (seedSt st a)).pc = 669)
    (hnh : (run linuxProg ro mem0 orc n (seedSt st a)).halted = false)
    (hrsp : (run linuxProg ro mem0 orc n (seedSt st a)).getG rsp = .ptr (a.plusI (-88)))
    (hW : Outside (a.plusI (-248)) 160 W)
    (hmem : (run linuxProg ro mem0 orc n (seedSt st a)).mem
      = W ++ saveLog st (a.plusI (-248)) 10 tail)
    (hvlen : ∀ k, k < 10 → 4 ≤ (st.getV (6 + k)).length)
    (hret : loadVal mem0 (run linuxProg ro mem0 orc n (seedSt st a))
      ((a.plusI (-248)).plusI 248) = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int))) :
    run winProg ro mem0 orc (11 + (n + 12)) { st with pc := 0 }
      = epiFinal (bodyExit (run linuxProg ro mem0 orc n (seedSt st a))) st (a.plusI (-248)) := by
  let S : State W32 Int := run linuxProg ro mem0 orc n (seedSt st a)
  have hhE : (bodyExit S).halted = false := by rw [bodyExit_halted]; exact hnh
  have hpcE : (bodyExit S).pc = 679 := by rw [bodyExit_pc, hpc]
  have hlenS : (run linuxProg ro mem0 orc n (seedSt st a)).gpr.length = 16 :=
    run_gpr_len linuxProg n (seedSt st a) (seedSt_gpr_len st a)
  have hrspE : (bodyExit S).getG rsp = .ptr (a.plusI (-248)) :=
    bodyExit_getG_rsp S a hlenS hrsp
  have hmemE : (bodyExit S).mem = W ++ saveLog st (a.plusI (-248)) 10 tail := by
    rw [bodyExit_mem]; exact hmem
  have hgrE : 5 ≤ (bodyExit S).gpr.length := by rw [bodyExit_gpr_len]; omega
  have hretE : loadVal mem0 (bodyExit S) ((a.plusI (-248)).plusI 248)
      = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int)) := by
    rw [loadVal_mem_eq (s := S) (t := bodyExit S)
      (a := (a.plusI (-248)).plusI 248) (by rw [bodyExit_mem])]
    exact hret
  rw [shani_call_run st a n v x hlen hh h4 hv hx hcond]
  exact run_epilogue (bodyExit S) st (a.plusI (-248)) tail W
    hhE hpcE hrspE hW hmemE hgrE hvlen hretE

/-- The ten callee-saved vector registers come back with their entry low four lanes. -/
theorem shani_call_getV {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (st : State W32 Int) (a : Addr Int) (n : Nat) (tail W : CLog)
    (v : List W32) (x : Addr Int)
    (hlen : st.gpr.length = 16) (hh : st.halted = false) (h4 : st.getG rsp = .ptr a)
    (hv : readVSrc ro mem0 (saveSt st a 10) 4 m256 = .ok v)
    (hx : gCtl (saveSt st a 10) (.reg 8) = .ok x)
    (hcond : ∀ k, k < n → (run linuxProg ro mem0 orc k (seedSt st a)).halted = true ∨
      (1 ≤ (run linuxProg ro mem0 orc k (seedSt st a)).pc ∧
        (run linuxProg ro mem0 orc k (seedSt st a)).pc < 669))
    (hpc : (run linuxProg ro mem0 orc n (seedSt st a)).pc = 669)
    (hnh : (run linuxProg ro mem0 orc n (seedSt st a)).halted = false)
    (hrsp : (run linuxProg ro mem0 orc n (seedSt st a)).getG rsp = .ptr (a.plusI (-88)))
    (hW : Outside (a.plusI (-248)) 160 W)
    (hmem : (run linuxProg ro mem0 orc n (seedSt st a)).mem
      = W ++ saveLog st (a.plusI (-248)) 10 tail)
    (hvr : st.vr.length = 16)
    (hvlen : ∀ k, k < 10 → 4 ≤ (st.getV (6 + k)).length)
    (hret : loadVal mem0 (run linuxProg ro mem0 orc n (seedSt st a))
      ((a.plusI (-248)).plusI 248) = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int)))
    (j : Nat) (hj : j < 10) :
    ((run winProg ro mem0 orc (11 + (n + 12)) { st with pc := 0 }).getV (6 + j)).take 4
      = (st.getV (6 + j)).take 4 := by
  let S : State W32 Int := run linuxProg ro mem0 orc n (seedSt st a)
  have hhE : (bodyExit S).halted = false := by rw [bodyExit_halted]; exact hnh
  have hpcE : (bodyExit S).pc = 679 := by rw [bodyExit_pc, hpc]
  have hlenS : (run linuxProg ro mem0 orc n (seedSt st a)).gpr.length = 16 :=
    run_gpr_len linuxProg n (seedSt st a) (seedSt_gpr_len st a)
  have hrspE : (bodyExit S).getG rsp = .ptr (a.plusI (-248)) :=
    bodyExit_getG_rsp S a hlenS hrsp
  have hmemE : (bodyExit S).mem = W ++ saveLog st (a.plusI (-248)) 10 tail := by
    rw [bodyExit_mem]; exact hmem
  have hvrS : (run linuxProg ro mem0 orc n (seedSt st a)).vr.length = 16 :=
    run_vr_len linuxProg n (seedSt st a) hvr
  have hvrE : 16 ≤ (bodyExit S).vr.length :=
    bodyExit_vr_len S (by rw [show S.vr.length = 16 from hvrS]; omega)
  have hgrE : 5 ≤ (bodyExit S).gpr.length := by rw [bodyExit_gpr_len]; omega
  have hretE : loadVal mem0 (bodyExit S) ((a.plusI (-248)).plusI 248)
      = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int)) := by
    rw [loadVal_mem_eq (s := S) (t := bodyExit S)
      (a := (a.plusI (-248)).plusI 248) (by rw [bodyExit_mem])]
    exact hret
  rw [shani_call_run st a n v x hlen hh h4 hv hx hcond]
  exact run_epilogue_getV (bodyExit S) st (a.plusI (-248)) tail W
    hhE hpcE hrspE hW hmemE hvrE hgrE hvlen hretE j hj

/-- The call returns halted. -/
theorem shani_call_halted {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (st : State W32 Int) (a : Addr Int) (n : Nat) (tail W : CLog)
    (v : List W32) (x : Addr Int)
    (hlen : st.gpr.length = 16) (hh : st.halted = false) (h4 : st.getG rsp = .ptr a)
    (hv : readVSrc ro mem0 (saveSt st a 10) 4 m256 = .ok v)
    (hx : gCtl (saveSt st a 10) (.reg 8) = .ok x)
    (hcond : ∀ k, k < n → (run linuxProg ro mem0 orc k (seedSt st a)).halted = true ∨
      (1 ≤ (run linuxProg ro mem0 orc k (seedSt st a)).pc ∧
        (run linuxProg ro mem0 orc k (seedSt st a)).pc < 669))
    (hpc : (run linuxProg ro mem0 orc n (seedSt st a)).pc = 669)
    (hnh : (run linuxProg ro mem0 orc n (seedSt st a)).halted = false)
    (hrsp : (run linuxProg ro mem0 orc n (seedSt st a)).getG rsp = .ptr (a.plusI (-88)))
    (hW : Outside (a.plusI (-248)) 160 W)
    (hmem : (run linuxProg ro mem0 orc n (seedSt st a)).mem
      = W ++ saveLog st (a.plusI (-248)) 10 tail)
    (hvlen : ∀ k, k < 10 → 4 ≤ (st.getV (6 + k)).length)
    (hret : loadVal mem0 (run linuxProg ro mem0 orc n (seedSt st a))
      ((a.plusI (-248)).plusI 248) = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int))) :
    (run winProg ro mem0 orc (11 + (n + 12)) { st with pc := 0 }).halted = true := by
  rw [shani_call st a n tail W v x hlen hh h4 hv hx hcond hpc hnh hrsp hW hmem hvlen hret]
  exact epiFinal_halted _ _ _

/-- The call returns with `rsp = a + 8` (the return address popped). -/
theorem shani_call_rsp {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (st : State W32 Int) (a : Addr Int) (n : Nat) (tail W : CLog)
    (v : List W32) (x : Addr Int)
    (hlen : st.gpr.length = 16) (hh : st.halted = false) (h4 : st.getG rsp = .ptr a)
    (hv : readVSrc ro mem0 (saveSt st a 10) 4 m256 = .ok v)
    (hx : gCtl (saveSt st a 10) (.reg 8) = .ok x)
    (hcond : ∀ k, k < n → (run linuxProg ro mem0 orc k (seedSt st a)).halted = true ∨
      (1 ≤ (run linuxProg ro mem0 orc k (seedSt st a)).pc ∧
        (run linuxProg ro mem0 orc k (seedSt st a)).pc < 669))
    (hpc : (run linuxProg ro mem0 orc n (seedSt st a)).pc = 669)
    (hnh : (run linuxProg ro mem0 orc n (seedSt st a)).halted = false)
    (hrsp : (run linuxProg ro mem0 orc n (seedSt st a)).getG rsp = .ptr (a.plusI (-88)))
    (hW : Outside (a.plusI (-248)) 160 W)
    (hmem : (run linuxProg ro mem0 orc n (seedSt st a)).mem
      = W ++ saveLog st (a.plusI (-248)) 10 tail)
    (hvlen : ∀ k, k < 10 → 4 ≤ (st.getV (6 + k)).length)
    (hret : loadVal mem0 (run linuxProg ro mem0 orc n (seedSt st a))
      ((a.plusI (-248)).plusI 248) = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int))) :
    (run winProg ro mem0 orc (11 + (n + 12)) { st with pc := 0 }).getG rsp
      = .ptr (a.plusI 8) := by
  let S : State W32 Int := run linuxProg ro mem0 orc n (seedSt st a)
  have hgrE : 5 ≤ (bodyExit S).gpr.length := by rw [bodyExit_gpr_len]; omega
  rw [shani_call st a n tail W v x hlen hh h4 hv hx hcond hpc hnh hrsp hW hmem hvlen hret]
  rw [epiFinal_getG_rsp (bodyExit S) st (a.plusI (-248)) hgrE]
  show Val.ptr ((a.plusI (-248)).plusI 256) = Val.ptr (a.plusI 8)
  rw [plusI_add]
  rfl

end Hashtree.Proofs.WinShaniCall
