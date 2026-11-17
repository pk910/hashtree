import Hashtree.Proofs.WinSseExec
import Hashtree.Proofs.WinFrame

/-!
## The windows body run of `sse_x1`/`avx_x1`

Composing the three instruction simulations on the body slice: the shipped windows body is the
linux body with the general registers renamed by `F` (`exec_ren`), the branch targets re-based
(`exec_shiftPc`), and the stack memory shifted by `μ` (`exec_sh`).  This file builds the combined
per-instruction lemma and the run induction; the concrete scans (which instructions the body
contains, and that they preserve `NoStackVal`) live with each kernel's slice file.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Hashtree.Asm.X86
open Hashtree.Asm

/-! ### The stack shift commutes with the other two state relations -/

theorem shSt_shiftPc (μ : Int) (p : Nat) (s : State W32 Int) :
    shSt μ (shiftPc p s) = shiftPc p (shSt μ s) := by
  simp only [shSt, shiftPc]

theorem shSt_renSt {F G : Nat → Nat} (μ : Int) (s : State W32 Int) :
    shSt μ (renSt F G s) = renSt F G (shSt μ s) := by
  simp only [shSt, renSt]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  exact (getG_sh μ s (G j)).symm

/-! ### `NoStackVal` under the register renaming and the pc shift -/

/-- `NoStackVal` is preserved by the register renaming.  `hG4` is the only finite fact about the
inverse permutation the proof needs (it is checked by `decide` on the sixteen registers of the
shipped layout). -/
theorem hns_ren {F G : Nat → Nat} (s : State W32 Int)
    (hG4 : ∀ j, j < 16 → j ≠ 4 → G j ≠ 4)
    (hns : ∀ j, j ≠ 4 → NoStackVal (s.getG j)) :
    ∀ j, j ≠ 4 → NoStackVal ((renSt F G s).getG j) := by
  intro j hj
  by_cases h16 : j < 16
  · have hgj : (renSt F G s).getG j = s.getG (G j) := by
      simp only [State.getG, renSt, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range h16, Option.map_some]
      rfl
    rw [hgj]
    exact hns (G j) (hG4 j h16 hj)
  · have hgj : (renSt F G s).getG j = .num (Lane.const 0) (Lane.const 0) := by
      simp only [State.getG, renSt, List.getD_eq_getElem?_getD]
      rw [List.getElem?_map, List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h16)]
      rfl
    simp only [hgj]
    intro a hv
    cases hv

/-- The pc shift does not touch the register file. -/
theorem hns_shiftPc (p : Nat) (s : State W32 Int) :
    (∀ j, j ≠ 4 → NoStackVal ((shiftPc p s).getG j)) ↔
      (∀ j, j ≠ 4 → NoStackVal (s.getG j)) := by
  have hg : ∀ j, (shiftPc p s).getG j = s.getG j := by
    intro j; simp only [shiftPc_getG]
  constructor
  · intro h j hj; rw [← hg j]; exact h j hj
  · intro h j hj; rw [hg j]; exact h j hj

/-! ### The combined windows body instruction -/

/-- The state relation at the body slice: windows is the linux state with renamed registers, a
re-based pc and shifted stack memory. -/
def winSt (F G : Nat → Nat) (μ : Int) (p : Nat) (s : State W32 Int) : State W32 Int :=
  shSt μ (shiftPc p (renSt F G s))

theorem frameSafe_shiftTgt (p : Nat) (i : Instr) : frameSafe (shiftTgt p i) ↔ frameSafe i := by
  cases i <;> simp only [shiftTgt, frameSafe]

theorem okI_shiftTgt (p : Nat) (i : Instr) : okI (shiftTgt p i) ↔ okI i := by
  cases i <;> simp only [shiftTgt, okI]

section
variable {ro : Region} {mem0w mem0l : Addr Int → Cell W32 Int} {orc : Nat → Bool}

/-- The body instruction of the windows stream (`shiftTgt p (rlI F i)`) executed on the shifted
windows state is the shifted image of the linux instruction executed on the linux state. -/
theorem exec_wx {F G : Nat → Nat} (hFG : RenPerm F G)
    (hG4 : ∀ j, j < 16 → j ≠ 4 → G j ≠ 4)
    (μ : Int) (p : Nat) (hro : ro ≠ rStack)
    (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a))
    (i : Instr) (s : State W32 Int) (hlen : s.gpr.length = 16)
    (hns : ∀ j, j ≠ 4 → NoStackVal (s.getG j))
    (hok : okI i) (hframe : frameSafe (rlI F i)) :
    exec ro mem0w orc (shiftTgt p (rlI F i)) (winSt F G μ p s)
      = winSt F G μ p (exec ro mem0l orc i s) := by
  have htr : trOk (rlI F i) := frameSafe_trOk (rlI F i) hframe
  have hns' : ∀ j, j ≠ 4 → NoStackVal ((renSt F G s).getG j) := hns_ren s hG4 hns
  simp only [winSt]
  rw [shSt_shiftPc μ p (renSt F G s)]
  rw [exec_shiftPc p (rlI F i) (shSt μ (renSt F G s)) htr]
  rw [exec_sh μ hro h0 (rlI F i) (renSt F G s) hns' hframe]
  rw [exec_ren hFG i s hlen hok]
  rw [← shSt_shiftPc μ p (renSt F G (exec ro mem0l orc i s))]

end

/-! ### The run induction over a body slice -/

section RunWx
variable {F G : Nat → Nat} {linuxProg winProg : Array Instr} {p base L : Nat}
variable {ro : Region} {mem0w mem0l : Addr Int → Cell W32 Int} {orc : Nat → Bool}

/-- `n` steps of the windows stream from the shifted starting state are the shift of the linux
run, provided the windows body instruction at `pc + p` is `shiftTgt p (rlI F i)` whenever the
linux instruction at `pc` is `i` (and every such instruction is safe), the run stays inside the
body slice, and no reachable linux state holds a stack pointer outside `rsp`. -/
theorem run_wx (μ : Int) (hFG : RenPerm F G) (hG4 : ∀ j, j < 16 → j ≠ 4 → G j ≠ 4)
    (hro : ro ≠ rStack) (h0 : ∀ a, mem0w (shAddr μ a) = shCell μ (mem0l a))
    (hmap : ∀ pc i, base ≤ pc → pc < base + L → linuxProg[pc]? = some i →
      winProg[pc + p]? = some (shiftTgt p (rlI F i)))
    (hokI : ∀ pc i, base ≤ pc → pc < base + L → linuxProg[pc]? = some i → okI i)
    (hframe : ∀ pc i, base ≤ pc → pc < base + L → linuxProg[pc]? = some i →
      frameSafe (rlI F i))
    (hLsize : base + L ≤ linuxProg.size) :
    ∀ (n : Nat) (s : State W32 Int), s.gpr.length = 16 →
    (∀ k, k < n → (run linuxProg ro mem0l orc k s).halted = true ∨
      (base ≤ (run linuxProg ro mem0l orc k s).pc ∧
        (run linuxProg ro mem0l orc k s).pc < base + L)) →
    (∀ k, k < n → ∀ j, j ≠ 4 → NoStackVal ((run linuxProg ro mem0l orc k s).getG j)) →
    run winProg ro mem0w orc n (winSt F G μ p s)
      = winSt F G μ p (run linuxProg ro mem0l orc n s) := by
  intro n
  induction n with
  | zero => intro s hlen hcond hns; rfl
  | succ n ih =>
    intro s hlen hcond hns
    by_cases hh : s.halted = true
    · have hsh : (winSt F G μ p s).halted = true := by
        simp only [winSt, shSt_halted, shiftPc_halted, renSt_halted, hh]
      rw [run_halted linuxProg ro mem0l orc (n+1) s hh,
        run_halted winProg ro mem0w orc (n+1) (winSt F G μ p s) hsh]
    · have hf : s.halted = false := by simpa using hh
      have h0c := hcond 0 (Nat.zero_lt_succ n)
      have hpc : base ≤ s.pc ∧ s.pc < base + L := by
        rcases h0c with h' | h'
        · exact absurd h' (by rw [show run linuxProg ro mem0l orc 0 s = s from rfl]; simp [hf])
        · exact h'
      have hlt : s.pc < linuxProg.size := by omega
      have hx : linuxProg[s.pc]? = some linuxProg[s.pc] := Array.getElem?_eq_getElem hlt
      have hwpc : (winSt F G μ p s).pc = s.pc + p := by
        simp only [winSt, shSt_pc, shiftPc_pc, renSt_pc]
      have hwx : winProg[(winSt F G μ p s).pc]? =
          some (shiftTgt p (rlI F linuxProg[s.pc])) := by
        rw [hwpc, hmap s.pc linuxProg[s.pc] hpc.1 hpc.2 hx]
      have hshf : (winSt F G μ p s).halted = false := by
        simp only [winSt, shSt_halted, shiftPc_halted, renSt_halted, hf]
      have e1 : run winProg ro mem0w orc (n+1) (winSt F G μ p s)
          = run winProg ro mem0w orc n
              (exec ro mem0w orc (shiftTgt p (rlI F linuxProg[s.pc])) (winSt F G μ p s)) := by
        simp only [run, hshf, Bool.false_eq_true, ite_false, hwx]
      have step : ∀ m, run linuxProg ro mem0l orc (m+1) s
          = run linuxProg ro mem0l orc m (exec ro mem0l orc linuxProg[s.pc] s) := by
        intro m; simp only [run, hf, Bool.false_eq_true, ite_false, hx]
      rw [e1, step n]
      rw [exec_wx hFG hG4 μ p hro h0 linuxProg[s.pc] s hlen
        (hns 0 (Nat.zero_lt_succ n)) (hokI s.pc _ hpc.1 hpc.2 hx)
        (hframe s.pc _ hpc.1 hpc.2 hx)]
      exact ih (exec ro mem0l orc linuxProg[s.pc] s)
        (by rw [exec_gpr_len]; exact hlen)
        (fun k hk => by
          have := hcond (k+1) (Nat.succ_lt_succ hk)
          rwa [step k] at this)
        (fun k hk => by
          have := hns (k+1) (Nat.succ_lt_succ hk)
          rwa [step k] at this)

end RunWx

end Hashtree.Asm.X86
