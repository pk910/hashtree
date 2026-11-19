import Hashtree.Proofs.AvxX1Entry
import Hashtree.Asm.X86Agree

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# Dead-register hand-off for `hashtree_sha256_avx_x1`

`AvxX1W.correctWAt_entry` states the x1 contract for a state that is the symbolic entry
state (up to its flags).  A chain hands x1 a state that only agrees with it on the registers
x1 does not read before writing them: the caller-saved scratch registers `rax`, `rcx`, `r9`
(and the flags) may still differ.

This file supplies that hand-off.

* `Dsx` is the concrete dead-register analysis from the entry set `{0,1,9,16}`:
  `{0,1,9,16}` on pcs 0–7, `{0,1,9}` on 8–15, `{0,9}` at 16, `{9}` on 17–20, `∅` on the
  loop body 21–4056 and `{0,1,9}` on the zero-count epilogue 4057–4064.  The 29 non-empty
  program points are the prologue and the epilogue; after the prologue nothing is live
  except the zero-count epilogue (`Dsx_entry` / `Dsx_exit` expose the ends).
* `hsound` proves the analysis for the shipped `prog`.  The 21-instruction prologue and the
  8-instruction zero-count epilogue are checked by `decide +kernel`; the 4000-instruction
  loop body follows symbolically, since `Dsx pc = []` makes the read and successor
  conditions vacuous; and the "written registers are not the flag pseudo-index" side
  condition is one kernel pass over `prog.toList` (`decide +kernel`), which is linear in the
  program, unlike the quadratic per-pc array-indexed whole-program check that timed out.
  The analysis table itself is never trusted: every program point is re-checked here.
* `correctWAt_agree` runs `run_agree` from any state that agrees with the flagged entry
  state outside `{0,1,9}` and transfers the x1 postcondition (`halted`, `err`, `tail`,
  `InRange`, `OutOk`, `RegsOk`) to it.

The read/write sets themselves are not trusted either: `execE_agree` (in
`Hashtree.Asm.X86Agree`) proves for every instruction and every pair of states that the
syntactic read set bounds what can affect the result, so a register missing from `readsOf`
would make that kernel-checked theorem false.
-/

namespace Hashtree.Proofs.AvxX1Agree

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Kernels.X86.AvxX1
open Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.AvxX1W (steps InRange correctWAt_entry)
open Hashtree.Proofs.ShaniW (OutOk RegsOk)
open Hashtree.Proofs.WrapperAmd64 (getG_of)
open Hashtree.Spec

/-! ## The analysis table -/

/-- May-differ registers at every pc of `hashtree_sha256_avx_x1`, starting from the entry
set `{rax, rcx, r9, flags}`.  Program points past the last instruction get the epilogue set. -/
def Dsx (pc : Nat) : List Nat :=
  if pc ≤ 7 then [0, 1, 9, 16]
  else if pc ≤ 15 then [0, 1, 9]
  else if pc = 16 then [0, 9]
  else if pc ≤ 20 then [9]
  else if pc ≤ 4056 then []
  else [0, 1, 9]

theorem Dsx_entry : Dsx 0 = [0, 1, 9, 16] := by decide

/-- The analysis set at the `ret` the full run ends in. -/
theorem Dsx_exit : Dsx 4064 = [0, 1, 9] := by decide

theorem Dsx_body {pc : Nat} (h1 : 21 ≤ pc) (h2 : pc ≤ 4056) : Dsx pc = [] := by
  have h7 : ¬ pc ≤ 7 := by omega
  have h15 : ¬ pc ≤ 15 := by omega
  have h16 : ¬ pc = 16 := by omega
  have h20 : ¬ pc ≤ 20 := by omega
  unfold Dsx
  rw [if_neg h7, if_neg h15, if_neg h16, if_neg h20, if_pos h2]

/-- `Dsx` never contains a callee-saved register: those all agree after any run. -/
theorem not_mem_Dsx (i pc : Nat) (hi : i ∈ [3, 4, 5, 12, 13, 14, 15]) : i ∉ Dsx pc := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold Dsx
    by_cases h7 : pc ≤ 7
    · rw [if_pos h7]; decide
    · rw [if_neg h7]
      by_cases h15 : pc ≤ 15
      · rw [if_pos h15]; decide
      · rw [if_neg h15]
        by_cases h16 : pc = 16
        · rw [if_pos h16]; decide
        · rw [if_neg h16]
          by_cases h20 : pc ≤ 20
          · rw [if_pos h20]; decide
          · rw [if_neg h20]
            by_cases h4056 : pc ≤ 4056
            · rw [if_pos h4056]; decide
            · rw [if_neg h4056]; decide

theorem eraseAll_nil : ∀ ws : List Nat, eraseAll ([] : List Nat) ws = [] := by
  intro ws
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [eraseAll]
    simpa only [eraseReg, List.filter_nil] using ih

/-! ## The factored check

`checkAt` is the local condition of the analysis (reads avoid the may-differ set, and every
successor keeps everything the transfer does not clear).  The flag side condition is
separate: it depends only on the written registers of the instruction, not on the pc. -/

def checkAt (pc : Nat) : Bool :=
  match prog[pc]? with
  | none => true
  | some i =>
    (readsOf i).all (fun r => decide (r ∉ Dsx pc)) &&
    (successors pc i).all (fun s =>
      (eraseAll (Dsx pc) (writesOf i)).all (fun r => decide (r ∈ Dsx s)))

/-- The 21-instruction prologue, kernel-checked. -/
theorem checkAt_lt_21 : (List.range 21).all checkAt = true := by decide +kernel

/-- The 8-instruction zero-count epilogue, kernel-checked (including the `ret`). -/
theorem checkAt_epilogue : (List.range 8).all (fun k => checkAt (4057 + k)) = true := by
  decide +kernel

/-- The loop body, symbolically: `Dsx` is empty there, so both local conditions hold
vacuously.  This covers the concrete loop-back `4056 → 13` as well. -/
theorem checkAt_body {pc : Nat} (h1 : 21 ≤ pc) (h2 : pc ≤ 4056) : checkAt pc = true := by
  have hpc : Dsx pc = [] := Dsx_body h1 h2
  unfold checkAt
  split
  · rfl
  · rw [hpc]
    simp only [Bool.and_eq_true, List.all_eq_true]
    constructor
    · intro r _; rfl
    · intro s _
      rw [eraseAll_nil]
      simp

theorem prog_size : prog.size = 4065 := by decide +kernel

/-- Every program point of `Hashtree.Kernels.X86.AvxX1.prog` satisfies the local check:
prologue, body and epilogue together cover `prog.size` (a missing range would leave a pc
unchecked here, and the gate would fail). -/
theorem checkAt_all : ∀ pc, pc < prog.size → checkAt pc = true := by
  intro pc hpc
  rw [prog_size] at hpc
  by_cases h1 : pc < 21
  · exact List.all_eq_true.mp checkAt_lt_21 pc (List.mem_range.mpr h1)
  · by_cases h2 : pc ≤ 4056
    · exact checkAt_body (by omega) h2
    · have h4 : pc - 4057 < 8 := by omega
      have h := List.all_eq_true.mp checkAt_epilogue (pc - 4057) (List.mem_range.mpr h4)
      rwa [show 4057 + (pc - 4057) = pc by omega] at h

/-- No instruction of the program writes the flag pseudo-index as a general register.
One kernel pass over the program list (no per-pc array indexing). -/
theorem flagOkAll :
    prog.toList.all (fun i => (gprWritesOf i).all (fun d => decide (d ≠ flg))) = true := by
  decide +kernel

/-! ## Soundness of the analysis for `prog` -/

theorem hsound : ∀ (pc : Nat) (i : Instr), prog[pc]? = some i →
    (∀ r, r ∈ readsOf i → r ∉ Dsx pc) ∧
    (∀ d, d ∈ gprWritesOf i → d ≠ flg) ∧
    (∀ p' : Nat, p' ∈ successors pc i →
      ∀ r, r ∈ eraseAll (Dsx pc) (writesOf i) → r ∈ Dsx p') := by
  intro pc i hget
  have hlt : pc < prog.size := by
    by_cases h : pc < prog.size
    · exact h
    · rw [Array.getElem?_eq_none (show prog.size ≤ pc from by omega)] at hget
      cases hget
  have hc : checkAt pc = true := checkAt_all pc hlt
  have hi : i ∈ prog.toList := by
    have h1 := Array.getElem?_eq_getElem hlt
    rw [hget] at h1
    rw [show i = prog[pc] from Option.some.inj h1]
    exact Array.getElem_mem_toList hlt
  have hc' := hc
  unfold checkAt at hc'
  rw [hget] at hc'
  simp only [Bool.and_eq_true, List.all_eq_true] at hc'
  obtain ⟨hread, hsucc⟩ := hc'
  refine ⟨fun r hr => of_decide_eq_true (hread r hr), ?_, ?_⟩
  · intro d hd
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp flagOkAll i hi) d hd)
  · intro p' hp' r hr
    exact of_decide_eq_true (hsucc p' hp' r hr)

/-! ## The run congruence at the concrete types -/

/-- `AgreeOn` is symmetric in its state arguments. -/
theorem AgreeOn.symm {S : List Nat} {s1 s2 : CState} (h : AgreeOn S s1 s2) :
    AgreeOn S s2 s1 := by
  refine ⟨h.pc.symm, h.halted.symm, h.tail.symm, h.err.symm, h.mem.symm, h.vr.symm,
    h.assume.symm, ?_, h.glen.symm, ?_, h.gpr16.symm⟩
  · intro hf; exact (h.flags hf).symm
  · intro i hi; exact (h.gpr i hi).symm

/-- Recover a `gpr[i]?` value from `getG` when the value is not the default cell. -/
theorem gpr_get_of_getG {s : CState} {i : Nat} {v : Val W32 Int}
    (h : s.getG i = v) (hv : v ≠ .num (Lane.const 0) (Lane.const 0)) :
    s.gpr[i]? = some v := by
  unfold State.getG at h
  rw [List.getD_eq_getElem?_getD] at h
  cases hg : s.gpr[i]? with
  | none =>
    rw [hg] at h
    simp only [Option.getD_none] at h
    exact absurd h.symm hv
  | some a =>
    rw [hg] at h
    simp only [Option.getD_some] at h
    rw [← h]

/-- An agreeing pair has the same registers by index. -/
theorem gpr_of_agree {D : List Nat} {s1 s2 : CState} (h : AgreeOn D s1 s2)
    {i : Nat} (hi : i ∉ D) {v : Val W32 Int} (h1 : s1.gpr[i]? = some v)
    (hv : v ≠ .num (Lane.const 0) (Lane.const 0)) : s2.gpr[i]? = some v := by
  have hg1 : s1.getG i = v := getG_of s1 i v h1
  have hg2 : s2.getG i = v := by
    rw [← h.gpr i hi]; exact hg1
  exact gpr_get_of_getG hg2 hv

/-- `RegsOk` transfers across agreement on a set that avoids the callee-saved registers. -/
theorem regsOk_agree {D : List Nat} {env0 : Key → W32} {σ : Nat → Int} {s1 s2 : CState}
    (h : AgreeOn D s1 s2)
    (hD : ∀ i, i ∈ [3, 4, 5, 12, 13, 14, 15] → i ∉ D)
    (h1 : RegsOk env0 σ s1) : RegsOk env0 σ s2 := by
  obtain ⟨h3, h5, h12, h14, h13, h15, h4⟩ := h1
  exact ⟨gpr_of_agree h (hD 3 (by decide)) h3 (by intro hv; cases hv),
    gpr_of_agree h (hD 5 (by decide)) h5 (by intro hv; cases hv),
    gpr_of_agree h (hD 12 (by decide)) h12 (by intro hv; cases hv),
    gpr_of_agree h (hD 14 (by decide)) h14 (by intro hv; cases hv),
    gpr_of_agree h (hD 13 (by decide)) h13 (by intro hv; cases hv),
    gpr_of_agree h (hD 15 (by decide)) h15 (by intro hv; cases hv),
    gpr_of_agree h (hD 4 (by decide)) h4 (by intro hv; cases hv)⟩

/-! ## The bridge -/

/-- **x1 from a dead-register cut.**  If a state `s` agrees with the flagged entry state
outside the dead scratch set `{0,1,9}`, then the x1 run from `s` reaches the same
postcondition as `AvxX1W.correctWAt_entry` states for the entry state.  `fl` is the entry
state's flag pair; instantiate it with the cut state's flags (the x1 prefix discards them,
so the reference run does not depend on it).

The exit agreement is on `Dsx` at the run's final pc (`Dsx_exit` for the `ret` at 4064);
the postcondition only needs the callee-saved registers, which `Dsx` never contains. -/
theorem correctWAt_agree (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r : Region)
    (hrNum : r ≠ rNum) (hrIn : r ≠ rIn) (hrOut : r ≠ rOut) (hrStack : r ≠ rStack)
    (hrG : r ≠ rG) (hrRet : r ≠ rRet)
    (hw : WfMemAtW r rodata [] env0 σ mem0c)
    (he : EnvMem env0 σ ((swap 4 r).mem mem0c))
    (hc : σ 2 = c)
    (hin : ∀ o : Nat, (swap 4 r).mem mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (fl : Option (Int × Int)) (s : CState)
    (hs : AgreeOn [0, 1, 9] s {mapState env0 σ entryW with flags := fl}) :
    let fin := run prog r mem0c orcC (steps c) s
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (σ 9) (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem ∧
      RegsOk env0 σ fin := by
  have hpost := correctWAt_entry c inp env0 σ mem0c orcC r hrNum hrIn hrOut hrStack hrG
    hrRet hw he hc hin fl
  dsimp only at hpost
  obtain ⟨hhalt, herr, htail, hRange, hOut, hRegs⟩ := hpost
  have hpc0 : ({mapState env0 σ entryW with flags := fl} : CState).pc = 0 := rfl
  have hpre : AgreeOn (Dsx ({mapState env0 σ entryW with flags := fl} : CState).pc)
      {mapState env0 σ entryW with flags := fl} s := by
    rw [hpc0, Dsx_entry]
    exact (AgreeOn.symm hs).mono (by
      intro i hi
      simp at hi
      rcases hi with rfl | rfl | rfl <;> decide)
  have hR := run_agree prog r mem0c orcC Dsx hsound (steps c)
    ({mapState env0 σ entryW with flags := fl} : CState) s hpre herr
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hR.halted]; exact hhalt
  · rw [← hR.err]; exact herr
  · rw [← hR.tail]; exact htail
  · exact hR.mem ▸ hRange
  · exact hR.mem ▸ hOut
  · exact regsOk_agree hR (fun i hi => not_mem_Dsx i _ hi) hRegs

end Hashtree.Proofs.AvxX1Agree
