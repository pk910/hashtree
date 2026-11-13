import Hashtree.Proofs.RvX1All
import Hashtree.Proofs.RvZbbX1All
import Hashtree.Proofs.RvCryptoAll

/-!
# Register preservation at the RV64 kernel boundary

The three kernels are ordinary LP64D functions: they may clobber temporaries, but the callee-saved
state (`ra`, `sp`, `s0`-`s11`) must be the same on return as on entry.  The kernels never write
`ra`, `sp`, `s0`-`s8` and `s11` (only `s9`/`s10` are used as scratch, and the prologue saves them at
`[-16,0)` and the exit reloads them), so this file proves preservation *statically*: an instruction
that does not name a register cannot change it, and a register that no instruction of the program
names is preserved by every run, whatever the fuel, count, memory and branch directions.

`PRESERVED` is that untouched set: `ra`, `s0`-`s8`, `s11`.  `sp`, `s9` and `s10` are *written* by
the kernel program and are covered by the save/restore argument (see `RvSaved`), which needs the
loop decomposition: the exit's reloads are read from the prologue's save slots, so that part is not
a static property of `exec`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.RvRegs
open Hashtree.Asm Hashtree.Asm.Riscv Hashtree.Asm.RiscvSym

/-- The register an instruction writes (as a destination; `x0` writes are dropped by `rset`, but
`x0` is never a callee-saved register). -/
def destOf : Instr → Option Nat
  | .nop | .unimp | .sw .. | .sd .. | .br .. => none
  | .lui d _ | .auipc d _ | .addi d _ _ | .add d _ _ | .bop _ d _ _ | .bopi _ d _ _
  | .slli d _ _ | .srai d _ _ | .wop _ d _ _ | .addw d _ _ | .rev8 d _ | .sha _ d _
  | .lwu d _ _ | .ld d _ _ | .jal d _ | .jalr d _ _ => some d

/-- Does the instruction name `r` as its destination? -/
def writes (i : Instr) (r : Nat) : Bool := destOf i == some r

/-! ## `getG` round the state updates -/

theorem getG_setG_self (s : State W32 Int) (i : Nat) (v : Val W32 Int) (h : i < s.gpr.length) :
    (s.setG i v).getG i = v := by
  simp [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set_self h]

theorem getG_setG_ne (s : State W32 Int) (i j : Nat) (v : Val W32 Int) (h : i ≠ j) :
    (s.setG j v).getG i = s.getG i := by
  simp [State.getG, State.setG, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem fail_getG (s : State W32 Int) (e : String) (r : Nat) :
    (s.fail e).getG r = s.getG r := by
  simp only [State.fail]; split <;> rfl

theorem next_getG (s : State W32 Int) (r : Nat) : s.next.getG r = s.getG r := rfl

theorem halt_getG (s : State W32 Int) (r : Nat) : (halt s).getG r = s.getG r := rfl

theorem setPc_getG (s : State W32 Int) (k : Nat) (r : Nat) : (setPc s k).getG r = s.getG r := rfl

theorem haltTail_getG (s : State W32 Int) (name : String) (r : Nat) :
    (haltTail s name).getG r = s.getG r := rfl

theorem callOut_getG (s : State W32 Int) (pc : Nat) (name : String) (r : Nat) :
    (callOut s pc name).getG r = s.getG r := rfl

theorem assumeC_getG (s : State W32 Int) (cs : List (Cond Int × Bool)) (r : Nat) :
    (assumeC s cs).getG r = s.getG r := rfl

theorem storeLane_getG (s : State W32 Int) (a : Addr Int) (x : W32) (r : Nat) :
    (storeLane s a x).getG r = s.getG r := rfl

theorem storeVal_getG (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) (r : Nat) :
    (storeVal s a v).getG r = s.getG r := by
  cases v <;> rfl

theorem branch_gpr (s : State W32 Int) (orc : Nat → Bool) (c : Cond Int) (t : Nat) :
    (State.branch orc s c t).gpr = s.gpr := by
  unfold State.branch
  cases hc : c.decideC with
  | none => by_cases ht : orc s.pc = true <;> simp [ht, State.next]
  | some b => cases b <;> simp [State.next]

theorem branch_getG (s : State W32 Int) (orc : Nat → Bool) (c : Cond Int) (t : Nat) (r : Nat) :
    (State.branch orc s c t).getG r = s.getG r := by
  simp only [State.getG, branch_gpr]

theorem rset_getG (s : State W32 Int) (d : Nat) (v : Val W32 Int) (r : Nat) (h : d ≠ r) :
    (rset s d v).getG r = s.getG r := by
  unfold rset
  split
  · rfl
  · exact getG_setG_ne s r d v (Ne.symm h)

theorem link_getG (env : Env) (s : State W32 Int) (d : Nat) (r : Nat) (h : d ≠ r) :
    (link env s d).getG r = s.getG r := by
  simp only [link, rset_getG s d _ r h]

theorem okOr_getG (s : State W32 Int) (res : Except String (State W32 Int)) (r : Nat)
    (hok : ∀ s', res = .ok s' → s'.getG r = s.getG r) :
    (okOr s res).getG r = s.getG r := by
  cases res with
  | ok s' => exact hok s' rfl
  | error e => exact fail_getG s e r

/-- Peel one `>>=` off an `Except` whose result is `ok s'`. -/
theorem bind_ok_of {β σ : Type} (f : Except String β) (k : β → Except String σ) (s' : σ)
    (h : (f >>= k) = .ok s') : ∃ v, f = .ok v ∧ k v = .ok s' := by
  cases f with
  | error e =>
    have h' : (Except.error e : Except String σ) = Except.ok s' := h
    cases h'
  | ok v =>
    have h' : k v = Except.ok s' := h
    exact ⟨v, rfl, h'⟩

/-- A `pure` in `Except` that lands on `ok s'` names `s'`. -/
theorem pure_ok_state {σ : Type} (x s' : σ) (h : (pure x : Except String σ) = .ok s') :
    x = s' := by
  have h' : (Except.ok x : Except String σ) = Except.ok s' := h
  simpa using h'

theorem slliV_getG (s : State W32 Int) (d : Nat) (v : Val W32 Int) (n : Nat) (r : Nat)
    (hw : d ≠ r) (s' : State W32 Int) (h : slliV s d v n = .ok s') :
    s'.getG r = s.getG r := by
  unfold slliV at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · simp at h
      · try dsimp only at h
        have e := pure_ok_state _ s' h
        rw [← e]
        exact (next_getG (rset s d _) r).trans (rset_getG s d _ r hw)
    · try dsimp only at h
      have e := pure_ok_state _ s' h
      rw [← e]
      exact (next_getG (rset (assumeC s _) d _) r).trans
        ((rset_getG (assumeC s _) d _ r hw).trans (assumeC_getG s _ r))
  · simp at h
  · try dsimp only at h
    have e := pure_ok_state _ s' h
    rw [← e]
    exact (next_getG (rset s d _) r).trans (rset_getG s d _ r hw)

theorem jumpTo_getG (env : Env) (s : State W32 Int) (d : Nat) (t : Addr Int) (r : Nat)
    (hd : d ≠ r) (s' : State W32 Int) (h : jumpTo env s d t = .ok s') :
    s'.getG r = s.getG r := by
  unfold jumpTo at h
  split at h
  · split at h
    · try dsimp only at h
      have e := pure_ok_state _ s' h
      rw [← e]
      exact halt_getG s r
    · simp at h
  · split at h
    · split at h
      · split at h
        · try dsimp only at h
          have e := pure_ok_state _ s' h
          rw [← e]
          exact (setPc_getG (link env s d) _ r).trans (link_getG env s d r hd)
        · simp at h
      · simp at h
    · split at h
      · split at h
        · split at h
          · try dsimp only at h
            have e := pure_ok_state _ s' h
            rw [← e]
            exact haltTail_getG s _ r
          · try dsimp only at h
            have e := pure_ok_state _ s' h
            rw [← e]
            exact (callOut_getG (link env s d) _ _ r).trans (link_getG env s d r hd)
        · simp at h
      · simp at h

/-! ## One instruction -/

theorem exec_gpr (env : Env) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (i : Instr)
    (s : State W32 Int) (r : Nat) (hw : writes i r = false) :
    (exec env mem0 orc i s).getG r = s.getG r := by
  cases i with
  | nop =>
    simp only [writes, destOf] at hw
    unfold exec; split
    · rfl
    · exact next_getG s r
  | unimp =>
    simp only [writes, destOf] at hw
    unfold exec; split
    · rfl
    · exact fail_getG s "illegal instruction" r
  | lui d imm20 =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | auipc d t =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨a, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | addi d a imm =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨v, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | add d a b =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      repeat' split at hs
      all_goals
        obtain ⟨v, -, hs⟩ := bind_ok_of _ _ s' hs
        try dsimp only at hs
        have e := pure_ok_state _ s' hs
        rw [← e]
        exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | bop op d a b =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨x, -, hs⟩ := bind_ok_of _ _ s' hs
      obtain ⟨y, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | bopi op d a imm =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨x, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | slli d a n =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      split at hs
      · simp at hs
      · exact slliV_getG s d _ n r (by simpa using hw) s' hs
  | srai d a n =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      split at hs
      · simp at hs
      · obtain ⟨x, -, hs⟩ := bind_ok_of _ _ s' hs
        try dsimp only at hs
        have e := pure_ok_state _ s' hs
        rw [← e]
        first
        | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | wop op d a n =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      split at hs
      · simp at hs
      · obtain ⟨x, -, hs⟩ := bind_ok_of _ _ s' hs
        try dsimp only at hs
        have e := pure_ok_state _ s' hs
        rw [← e]
        first
        | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | addw d a b =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨x, -, hs⟩ := bind_ok_of _ _ s' hs
      obtain ⟨y, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | rev8 d a =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨x, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | sha op d a =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨x, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | lwu d b off =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨a, -, hs⟩ := bind_ok_of _ _ s' hs
      obtain ⟨w, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | ld d b off =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨a, -, hs⟩ := bind_ok_of _ _ s' hs
      obtain ⟨v, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      first
      | exact (next_getG (rset s d _) r).trans (rset_getG s d _ r (by simpa using hw))
  | sw src b off =>
    simp only [writes, destOf] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨a, -, hs⟩ := bind_ok_of _ _ s' hs
      obtain ⟨u, -, hs⟩ := bind_ok_of _ _ s' hs
      obtain ⟨x, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      exact (next_getG (storeLane s a x.1) r).trans (storeLane_getG s a x.1 r)
  | sd src b off =>
    simp only [writes, destOf] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨a, -, hs⟩ := bind_ok_of _ _ s' hs
      obtain ⟨u, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      exact (next_getG (storeVal s a (rget s src)) r).trans
        (storeVal_getG s a (rget s src) r)
  | br c a b t =>
    simp only [writes, destOf] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨x, -, hs⟩ := bind_ok_of _ _ s' hs
      obtain ⟨y, -, hs⟩ := bind_ok_of _ _ s' hs
      obtain ⟨e0, -, hs⟩ := bind_ok_of _ _ s' hs
      try dsimp only at hs
      have e := pure_ok_state _ s' hs
      rw [← e]
      exact branch_getG s orc _ t r
  | jal d t =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · exact (setPc_getG (link env s d) t r).trans (link_getG env s d r (by simpa using hw))
  | jalr d a off =>
    simp only [writes, destOf, beq_eq_false_iff_ne, ne_eq] at hw
    unfold exec; split
    · rfl
    · refine okOr_getG s _ r ?_
      intro s' hs
      obtain ⟨v, -, hs⟩ := bind_ok_of _ _ s' hs
      exact jumpTo_getG env s d _ r (by simpa using hw) s' hs

/-! ## A whole run -/

/-- No instruction in the program writes `r`: every run preserves `r`. -/
theorem run_gpr (prog : Array Instr) (env : Env) (mem0 : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (s : State W32 Int) (r : Nat)
    (hall : prog.toList.all (fun i => !writes i r) = true) :
    ∀ n, (run prog env mem0 orc n s).getG r = s.getG r := by
  intro n
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold run
    split
    · rfl
    · split
      · rename_i i hi
        have hmem : i ∈ prog.toList := by
          rw [Array.mem_toList_iff, Array.mem_iff_getElem]
          obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hi
          exact ⟨s.pc, hlt, heq⟩
        have hw : writes i r = false := by
          have := (List.all_eq_true.mp hall) i hmem
          simpa using this
        exact (ih (exec env mem0 orc i s)).trans (exec_gpr env mem0 orc i s r hw)
      · exact fail_getG s "pc out of program" r

/-- The callee-saved registers the kernels never write (`ra`, `s0`-`s8`, `s11`). -/
def PRESERVED : List Nat := [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 27]

/-- `ra`, `sp`, `s0`-`s11`: the LP64D callee-saved set. -/
def CALLEE_SAVED : List Nat := [1, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem all_of_preserved {prog : Array Instr}
    (h : prog.toList.all (fun i => PRESERVED.all (fun r => !writes i r)) = true)
    {r : Nat} (hr : r ∈ PRESERVED) :
    prog.toList.all (fun i => !writes i r) = true := by
  rw [List.all_eq_true]
  intro i hi
  exact (List.all_eq_true.mp (List.all_eq_true.mp h i hi)) r hr

theorem all_x1 : Hashtree.Kernels.Riscv.X1.prog.toList.all
    (fun i => PRESERVED.all (fun r => !writes i r)) = true := by
  decide +kernel

theorem all_zbb : Hashtree.Kernels.Riscv.ZbbX1.prog.toList.all
    (fun i => PRESERVED.all (fun r => !writes i r)) = true := by
  decide +kernel

theorem all_crypto : Hashtree.Kernels.Riscv.Crypto.prog.toList.all
    (fun i => PRESERVED.all (fun r => !writes i r)) = true := by
  decide +kernel

/-- **`hashtree_sha256_riscv_x1` preserves `ra`, `s0`-`s8`, `s11`.**  The ten untouched
callee-saved registers are equal on return to their entry values, for every count and every
well-formed memory. -/
theorem correct_regs_x1 (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r : Nat) (hr : r ∈ PRESERVED) :
    let fin := Riscv.run Hashtree.Kernels.Riscv.X1.prog Hashtree.Gen.RvX1L.pe mem0c orcC
      (Hashtree.Proofs.RvX1L.steps c) (mapState env0 σ (entryS 0))
    fin.getG r = (mapState env0 σ (entryS 0)).getG r := by
  dsimp only
  exact run_gpr _ _ _ _ _ r (all_of_preserved all_x1 hr) _

theorem correct_regs_zbb (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r : Nat) (hr : r ∈ PRESERVED) :
    let fin := Riscv.run Hashtree.Kernels.Riscv.ZbbX1.prog Hashtree.Gen.RvZbbX1L.pe mem0c orcC
      (Hashtree.Proofs.RvZbbX1L.steps c) (mapState env0 σ (entryS 0))
    fin.getG r = (mapState env0 σ (entryS 0)).getG r := by
  dsimp only
  exact run_gpr _ _ _ _ _ r (all_of_preserved all_zbb hr) _

theorem correct_regs_crypto (c : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r : Nat) (hr : r ∈ PRESERVED) :
    let fin := Riscv.run Hashtree.Kernels.Riscv.Crypto.prog Hashtree.Gen.RvCryptoL.pe mem0c orcC
      (Hashtree.Proofs.RvCryptoL.steps c) (mapState env0 σ (entryS 0))
    fin.getG r = (mapState env0 σ (entryS 0)).getG r := by
  dsimp only
  exact run_gpr _ _ _ _ _ r (all_of_preserved all_crypto hr) _

end Hashtree.Proofs.RvRegs
