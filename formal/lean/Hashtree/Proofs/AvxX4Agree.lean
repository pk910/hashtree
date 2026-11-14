import Hashtree.Kernels.X86.AvxX4
import Hashtree.Asm.X86Agree

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# Dead-register analysis of `hashtree_sha256_avx_x4`

The x8 kernel tail-calls x4 with every register of the wrapper call state restored except two
scratch values it does not bother to clear: `rcx` (left on the x8 table) and the flags.  The x4
kernel reads neither before writing it: `cmp rdx,0` at pc 1 sets the flags before the `jne` at
pc 2 reads them, and `lea rcx,[rip+..]` at pc 8 writes `rcx` before its first read (pc 9).  On
the count-0 return (pc 3) and the small-count exit (`jl` at pc 6 to `add rsp,408; jmp avx_x1`
at 4142-4143) `rcx` is never written, so it is still a may-differ register there -- harmless,
since the x1 hand-off tolerates `rcx` (`AvxX1Agree`, set `{0, 1, 9}`).

`Dsx4` is the analysis table from the entry set `{rcx, flags}` and `hsound` is its soundness
for the shipped `prog`, in the factored form of `AvxX1Agree`: the nine-instruction prologue and
the two-instruction exit are kernel-checked, the 4133-instruction body (`Dsx4 pc = []`) is
symbolic, and the flag side condition is one kernel pass over `prog.toList`.  With
`X86Agree.run_agree` this makes the x4 run from the x8 exit state agree, outside `{rcx}`, with
the run from the exact wrapper-shaped entry state the x4 W-mode link is stated at.
-/

namespace Hashtree.Proofs.AvxX4Agree

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Kernels.X86.AvxX4

/-! ## The analysis table -/

/-- May-differ registers at every pc of `hashtree_sha256_avx_x4` from the entry set
`{rcx, flags}`: the flags are written at pc 1, `rcx` at pc 8; the exits at pc 3 and at
4142-4143 are reached without writing `rcx`. -/
def Dsx4 (pc : Nat) : List Nat :=
  if pc ≤ 1 then [1, 16]
  else if pc ≤ 8 then [1]
  else if pc ≤ 4141 then []
  else [1]

theorem Dsx4_entry : Dsx4 0 = [1, 16] := by decide

/-- The analysis set at the `jmpTail` into x1 (pc 4143) and at the count-0 `ret` (pc 3). -/
theorem Dsx4_exit : Dsx4 4143 = [1] := by decide
theorem Dsx4_ret : Dsx4 3 = [1] := by decide

theorem Dsx4_body {pc : Nat} (h1 : 9 ≤ pc) (h2 : pc ≤ 4141) : Dsx4 pc = [] := by
  have h1' : ¬ pc ≤ 1 := by omega
  have h8 : ¬ pc ≤ 8 := by omega
  unfold Dsx4
  rw [if_neg h1', if_neg h8, if_pos h2]

/-- `Dsx4` only ever contains `rcx` and the flag pseudo-index. -/
theorem mem_Dsx4 (i pc : Nat) (hi : i ∈ Dsx4 pc) : i = 1 ∨ i = 16 := by
  unfold Dsx4 at hi
  split at hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  · split at hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    · split at hi
      · simp at hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega

theorem eraseAll_nil : ∀ ws : List Nat, eraseAll ([] : List Nat) ws = [] := by
  intro ws
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [eraseAll]
    simpa only [eraseReg, List.filter_nil] using ih

/-! ## The factored check -/

def checkAt (pc : Nat) : Bool :=
  match prog[pc]? with
  | none => true
  | some i =>
    (readsOf i).all (fun r => decide (r ∉ Dsx4 pc)) &&
    (successors pc i).all (fun s =>
      (eraseAll (Dsx4 pc) (writesOf i)).all (fun r => decide (r ∈ Dsx4 s)))

/-- The nine-instruction prologue (`nop; cmp; jne; ret; sub rsp; cmp; jl; xor r9,r9; lea rcx`),
kernel-checked.  The `jl` at pc 6 has the successors 4142 and 7, both with `rcx` live. -/
theorem checkAt_lt_9 : (List.range 9).all checkAt = true := by decide +kernel

/-- The two-instruction exit (`add rsp,408; jmp avx_x1`), kernel-checked. -/
theorem checkAt_exit : (List.range 2).all (fun k => checkAt (4142 + k)) = true := by
  decide +kernel

/-- The loop body, symbolically: `Dsx4` is empty there, so both local conditions are vacuous.
This covers the loop-back `jmp 5` at 4141 as well (its transfer set is empty). -/
theorem checkAt_body {pc : Nat} (h1 : 9 ≤ pc) (h2 : pc ≤ 4141) : checkAt pc = true := by
  have hpc : Dsx4 pc = [] := Dsx4_body h1 h2
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

theorem prog_size : prog.size = 4144 := by decide +kernel

theorem checkAt_all : ∀ pc, pc < prog.size → checkAt pc = true := by
  intro pc hpc
  rw [prog_size] at hpc
  by_cases h1 : pc < 9
  · exact List.all_eq_true.mp checkAt_lt_9 pc (List.mem_range.mpr h1)
  · by_cases h2 : pc ≤ 4141
    · exact checkAt_body (by omega) h2
    · have h4 : pc - 4142 < 2 := by omega
      have h := List.all_eq_true.mp checkAt_exit (pc - 4142) (List.mem_range.mpr h4)
      rwa [show 4142 + (pc - 4142) = pc by omega] at h

/-- No instruction writes the flag pseudo-index as a general register (one kernel pass). -/
theorem flagOkAll :
    prog.toList.all (fun i => (gprWritesOf i).all (fun d => decide (d ≠ flg))) = true := by
  decide +kernel

/-! ## Soundness of the analysis for `prog` -/

theorem hsound : ∀ (pc : Nat) (i : Instr), prog[pc]? = some i →
    (∀ r, r ∈ readsOf i → r ∉ Dsx4 pc) ∧
    (∀ d, d ∈ gprWritesOf i → d ≠ flg) ∧
    (∀ p' : Nat, p' ∈ successors pc i →
      ∀ r, r ∈ eraseAll (Dsx4 pc) (writesOf i) → r ∈ Dsx4 p') := by
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

/-- **The x4 run congruence.**  Two states that agree outside `{rcx, flags}` at the entry run
to states that agree outside `Dsx4` at the final pc, provided the reference run does not fail
(`X86Agree.run_agree` with the analysis above). -/
theorem run_agree4 (ro : Region) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (n : Nat) (s1 s2 : State W32 Int) (h0 : s1.pc = 0) (hpre : AgreeOn [1, 16] s1 s2)
    (herr : (run prog ro mem0c orcC n s1).err = none) :
    AgreeOn (Dsx4 (run prog ro mem0c orcC n s1).pc) (run prog ro mem0c orcC n s1)
      (run prog ro mem0c orcC n s2) := by
  have hpre' : AgreeOn (Dsx4 s1.pc) s1 s2 := by
    rw [h0, Dsx4_entry]; exact hpre
  exact run_agree prog ro mem0c orcC Dsx4 hsound n s1 s2 hpre' herr

end Hashtree.Proofs.AvxX4Agree
