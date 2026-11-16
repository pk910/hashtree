import Hashtree.Proofs.WinX1Front
import Hashtree.Proofs.WinShaniEpi
import Hashtree.Asm.MemCells

/-!
# R5: the windows x1 epilogue replay, generic in the stream

The windows `sse_x1` and `avx_x1` streams share one epilogue shape (`q0` = the first restore pc,
4198 for `sse_x1`, 4068 for `avx_x1`; `vex` = the restores' VEX flag, `false` / `true`):

```
q0 .. q0+7    : vload 4 xmm{6+m}, [rsp + 64 + 16m]   -- rest_read / run_rest
q0+8          : add rsp, 192                           -- exec_add_rsp_imm
q0+9 .. q0+17 : pop r15, r14, r13, r12, rbp, rdi, rsi, r8, rbx   -- pop_read / run_pops
q0+18         : ret                                    -- ret_read / exec_ret_ok
```

The body-exit log is `W ++ saveLog st (a - 264) 8 (pushLog st a 9 tail)` (the body's own writes
`W` over the prologue's image `WinX1Front.frontSt`), with `W` outside `[a - 200, a + 8)`
(`Outside (a.plusI (-200)) 208 W`): the eight restores read the save slots back
(`loadLanes_pre`), the nine pops read the push cells back (`loadVal_pre`, through
`MemCells.loadVal_storeVal`), and `ret` reads the return pointer from the entry memory `tail`.

`run_back`: nineteen steps from such a state at pc `q0` end in `backFinal`: halted, `rsp = a + 8`,
the nine pushed registers back to their entry values (`backFinal_getG_saved`), the low four lanes
of `xmm6`-`xmm13` back to their entry values (`backFinal_getV`), every other general register as
at the body exit (`backFinal_getG_other`), the log unchanged (`backFinal_mem`).

Every projection of the computed states (`restSt`, `addSt`, `popSt`, `backFinal`) is taken by a
rewrite lemma; no `show`/`rfl` against them (one such `exact` made the first version of this file
take an hour to check).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Hashtree.Proofs.WinX1Back

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.MemCells Hashtree.Asm.RunAgreeM Hashtree.Asm.RunExit
open Hashtree.Proofs.WinShaniFront (laneLog run_succ_step gCtl_reg_ptr gCtl_imm)
open Hashtree.Proofs.WinShaniEpi (Outside loadLanes_pre laneAddr_zero laneLog_bounds plusI_add plusI_off
  plusI_region plusI_zero exec_ret_ok loadVal_mem_eq take_four_append getV_next)
open Hashtree.Proofs.WinX1Front (pushRegs pushLog saveLog)
open Hashtree.Proofs.FrameLift (exec_pop M8_of_cells)
open Hashtree.Proofs.WinShaniFlags (exec_vload_ok)

/-- The `m`-th restore: `vload 4 xmm{6+m}, [rsp + 64 + 16m]`. -/
def restStep (vex : Bool) (m : Nat) : Instr :=
  .vload vex 4 (6 + m) (.mem { base := some rsp, disp := (64 + 16 * (m : Int)) })

/-- The register of the `k`-th pop: the pushes in reverse order. -/
def popReg (k : Nat) : Nat := pushRegs.reverse.getD k 0

theorem popReg_ne4 (k : Nat) (hk : k < 9) : popReg k ≠ 4 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem popReg_lt16 (k : Nat) (hk : k < 9) : popReg k < 16 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem popReg_inj (j k : Nat) (hj : j < 9) (hk : k < 9) (hne : j ≠ k) : popReg j ≠ popReg k := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first | exact absurd rfl hne | decide

/-- Pop `k` restores push `8 - k`. -/
theorem popReg_push (k : Nat) (hk : k < 9) : pushRegs.getD (8 - k) 0 = popReg k := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## Bounds of the prologue's image -/

theorem disp64 (k : Nat) : (64 + 16 * (k : Int)) = ((64 + 16 * k : Nat) : Int) := by
  rw [Int.natCast_add, Int.natCast_mul]; rfl

theorem laneLog_upper (a : Addr Int) (xs : List W32) :
    ∀ p ∈ laneLog a xs, p.1.off < a.off + 4 * xs.length := by
  induction xs generalizing a with
  | nil => intro p hp; simp only [laneLog, List.not_mem_nil] at hp
  | cons x xs ih =>
    intro p hp
    simp only [laneLog, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    simp only [List.length_cons]
    rcases hp with hp | rfl | rfl | rfl | rfl
    · have := ih (a.plusI 4) p hp
      rw [plusI_off] at this
      omega
    all_goals (simp only [plusI_off]; omega)

/-- The save log of `n` slots is a block in `[b + 64, b + 64 + 16 n)` over its tail. -/
theorem saveLog_all (st : State W32 Int) (b : Addr Int) (tail : CLog) :
    ∀ n, ∃ S, saveLog st b n tail = S ++ tail ∧
      ∀ p ∈ S, p.1.region = b.region ∧ b.off + 64 ≤ p.1.off ∧ p.1.off < b.off + 64 + 16 * n := by
  intro n
  induction n with
  | zero => exact ⟨[], rfl, fun p hp => by simp at hp⟩
  | succ n ih =>
    obtain ⟨S, hS, hb⟩ := ih
    refine ⟨laneLog (b.plusI ((64 + 16 * n : Nat) : Int)) ((st.getV (6 + n)).take 4) ++ S, ?_, ?_⟩
    · show laneLog (b.plusI ((64 + 16 * n : Nat) : Int)) ((st.getV (6 + n)).take 4) ++ saveLog st b n tail = _
      rw [hS, List.append_assoc]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · have h1 := laneLog_bounds _ _ p hp
        have h2 := laneLog_upper _ _ p hp
        rw [plusI_region, plusI_off] at h1
        rw [plusI_off] at h2
        have hl : ((st.getV (6 + n)).take 4).length ≤ 4 := by
          rw [List.length_take]; omega
        refine ⟨h1.1, ?_, ?_⟩
        · have := h1.2; push_cast at this ⊢; omega
        · push_cast at h2 ⊢; omega
      · have := hb p hp
        refine ⟨this.1, this.2.1, ?_⟩
        have := this.2.2
        push_cast at this ⊢; omega

/-- Above slot `k` the save log is a block at offsets `≥ b + 64 + 16 (k + 1)`. -/
theorem saveLog_split (st : State W32 Int) (b : Addr Int) (tail : CLog) (k : Nat) :
    ∀ d, ∃ P, saveLog st b (k + 1 + d) tail
        = P ++ (laneLog (b.plusI ((64 + 16 * k : Nat) : Int)) ((st.getV (6 + k)).take 4) ++ saveLog st b k tail) ∧
      ∀ p ∈ P, p.1.region = b.region ∧ b.off + 64 + 16 * (k + 1) ≤ p.1.off := by
  intro d
  induction d with
  | zero => exact ⟨[], rfl, fun p hp => by simp at hp⟩
  | succ d ih =>
    obtain ⟨P, hP, hb⟩ := ih
    refine ⟨laneLog (b.plusI ((64 + 16 * (k + 1 + d) : Nat) : Int)) ((st.getV (6 + (k + 1 + d))).take 4) ++ P, ?_, ?_⟩
    · show laneLog (b.plusI ((64 + 16 * (k + 1 + d) : Nat) : Int)) ((st.getV (6 + (k + 1 + d))).take 4)
          ++ saveLog st b (k + 1 + d) tail = _
      rw [hP, List.append_assoc]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · have h1 := laneLog_bounds _ _ p hp
        rw [plusI_region, plusI_off] at h1
        refine ⟨h1.1, ?_⟩
        have := h1.2
        push_cast at this ⊢; omega
      · exact hb p hp

theorem storeCells_bounds (q : Addr Int) (v : Val W32 Int) :
    ∀ p ∈ storeCells q v, p.1.region = q.region ∧ q.off ≤ p.1.off ∧ p.1.off < q.off + 8 := by
  intro p hp
  cases v with
  | num lo hi =>
    simp only [storeCells, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨rfl, by simp only [plusI_off]; omega, by simp only [plusI_off]; omega⟩
  | ptr r =>
    simp only [storeCells, List.mem_map, List.mem_reverse, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact ⟨rfl, by simp only [plusI_off, Int.ofNat_eq_natCast]; omega,
      by simp only [plusI_off, Int.ofNat_eq_natCast]; omega⟩

/-- The push log of `j + d` pushes is the `d` deepest blocks, in `[a - 8 (j + d), a - 8 j)`, over
the log of `j` pushes. -/
theorem pushLog_split (st : State W32 Int) (a : Addr Int) (tail : CLog) (j : Nat) :
    ∀ d, ∃ P, pushLog st a (j + d) tail = P ++ pushLog st a j tail ∧
      ∀ p ∈ P, p.1.region = a.region ∧ a.off - 8 * (j + d) ≤ p.1.off ∧ p.1.off < a.off - 8 * j := by
  intro d
  induction d with
  | zero => exact ⟨[], rfl, fun p hp => by simp at hp⟩
  | succ d ih =>
    obtain ⟨P, hP, hb⟩ := ih
    refine ⟨storeCells (a.plusI (-(8 * (j + d + 1) : Int))) (st.getG (pushRegs.getD (j + d) 0)) ++ P, ?_, ?_⟩
    · show storeCells (a.plusI (-(8 * (j + d + 1) : Int))) (st.getG (pushRegs.getD (j + d) 0))
          ++ pushLog st a (j + d) tail = _
      rw [hP, List.append_assoc]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · have h := storeCells_bounds _ _ p hp
        rw [plusI_region, plusI_off] at h
        refine ⟨h.1, ?_, ?_⟩
        · have := h.2.1; push_cast at this ⊢; omega
        · have := h.2.2; push_cast at this ⊢; omega
      · obtain ⟨h1, h2, h3⟩ := hb p hp
        refine ⟨h1, ?_, h3⟩
        push_cast at h2 ⊢; omega

/-! ## Reading back through a prefix -/

/-- A 64-bit value stored at `q` reads back through any prefix outside its eight cells. -/
theorem loadVal_pre (mem0 : Addr Int → Cell W32 Int) (t : State W32 Int) (P rest : CLog)
    (q : Addr Int) (v : Val W32 Int) (hmem : t.mem = P ++ (storeCells q v ++ rest))
    (hP : ∀ p ∈ P, ¬ Cells q 8 p.1) : loadVal mem0 t q = .ok v := by
  let s' : State W32 Int := { t with mem := rest }
  have hm : MemAg (Cells q 8) (storeVal s' q v).mem t.mem := by
    intro x hx
    rw [storeVal_mem, hmem, Hashtree.Asm.X86.lookup_app_right x P _ (fun p hp he => hP p hp (by rw [he]; exact hx))]
  rw [loadVal_memAg hm mem0 rfl rfl q (M8_of_cells _ _ (fun x hx => hx))]
  exact loadVal_storeVal mem0 s' q v

/-- The `k`-th restore reads save slot `k` (`[a - 200 + 16 k, +16)`) back. -/
theorem rest_read (mem0 : Addr Int → Cell W32 Int) (t st : State W32 Int) (a : Addr Int) (tail W : CLog)
    (hW : Outside (a.plusI (-200)) 208 W)
    (hmem : t.mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail))
    (h4 : t.getG rsp = .ptr (a.plusI (-264))) (k : Nat) (hk : k < 8)
    (hvlen : 4 ≤ (st.getV (6 + k)).length) :
    readVSrc 4 mem0 t 4 (.mem { base := some rsp, disp := (64 + 16 * (k : Int)) })
      = .ok ((st.getV (6 + k)).take 4) := by
  have he : effAddr 4 t ({ base := some rsp, disp := (64 + 16 * (k : Int)) } : MemRef)
      = .ok ((a.plusI (-264)).plusI ((64 + 16 * k : Nat) : Int)) := by
    simp only [effAddr, baseAddr, regPtr, h4, disp64]
  simp only [readVSrc, he, Hashtree.Asm.X86.bind_ok_eq]
  obtain ⟨d, hd⟩ : ∃ d, k + 1 + d = 8 := ⟨8 - (k + 1), by omega⟩
  obtain ⟨P, hP, hPb⟩ := saveLog_split st (a.plusI (-264)) (pushLog st a 9 tail) k d
  rw [hd] at hP
  have hmem' : t.mem = (W ++ P) ++ (laneLog ((a.plusI (-264)).plusI ((64 + 16 * k : Nat) : Int))
      ((st.getV (6 + k)).take 4) ++ saveLog st (a.plusI (-264)) k (pushLog st a 9 tail)) := by
    rw [hmem, hP, List.append_assoc]
  have hout : Outside ((a.plusI (-264)).plusI ((64 + 16 * k : Nat) : Int)) 16 (W ++ P) := by
    intro p hp
    simp only [plusI_off, plusI_region]
    rcases List.mem_append.mp hp with hp | hp
    · rcases hW p hp with h | h | h
      · rw [plusI_off] at h; left; push_cast; omega
      · rw [plusI_off] at h; right; left; push_cast; omega
      · right; right; rw [plusI_region] at h; exact h
    · obtain ⟨_, h2⟩ := hPb p hp
      rw [plusI_off] at h2
      right; left; push_cast at h2 ⊢; omega
  have h := loadLanes_pre mem0 t (W ++ P) _ _ ((st.getV (6 + k)).take 4) hmem' hout 4 0
    (by rw [List.length_take]; omega) (by omega)
  simp only [laneAddr_zero, List.drop_zero, List.take_take, Nat.min_self] at h
  exact h

/-- The `k`-th pop reads the push cell at `a - 8 (9 - k)` back. -/
theorem pop_read (mem0 : Addr Int → Cell W32 Int) (t st : State W32 Int) (a : Addr Int) (tail W : CLog)
    (hW : Outside (a.plusI (-200)) 208 W)
    (hmem : t.mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail))
    (k : Nat) (hk : k < 9) :
    loadVal mem0 t (a.plusI (8 * (k : Int) - 72)) = .ok (st.getG (popReg k)) := by
  obtain ⟨j, hj⟩ : ∃ j, j = 8 - k := ⟨_, rfl⟩
  obtain ⟨S, hS, hSb⟩ := saveLog_all st (a.plusI (-264)) (pushLog st a 9 tail) 8
  obtain ⟨P, hP, hPb⟩ := pushLog_split st a tail (j + 1) k
  have h9 : j + 1 + k = 9 := by omega
  rw [h9] at hP
  have hq : a.plusI (-(8 * (j + 1) : Int)) = a.plusI (8 * (k : Int) - 72) := by
    congr 1; push_cast; omega
  have hr : pushRegs.getD j 0 = popReg k := by rw [hj]; exact popReg_push k hk
  have hmem' : t.mem = (W ++ S ++ P) ++ (storeCells (a.plusI (8 * (k : Int) - 72)) (st.getG (popReg k))
      ++ pushLog st a j tail) := by
    rw [hmem, hS, hP, show pushLog st a (j + 1) tail = storeCells (a.plusI (-(8 * (j + 1) : Int)))
      (st.getG (pushRegs.getD j 0)) ++ pushLog st a j tail from rfl, hq, hr]
    simp only [List.append_assoc]
  apply loadVal_pre mem0 t _ _ _ _ hmem'
  intro p hp hc
  obtain ⟨hc1, hc2, hc3⟩ := hc
  rw [plusI_region] at hc1
  rw [plusI_off] at hc2 hc3
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · rcases hW p hp with h | h | h
      · rw [plusI_off] at h; omega
      · rw [plusI_off] at h; omega
      · exact h (by rw [hc1]; rfl)
    · obtain ⟨_, _, h3⟩ := hSb p hp
      rw [plusI_off] at h3; omega
  · obtain ⟨_, _, h3⟩ := hPb p hp
    push_cast at h3; omega

/-- `ret` reads the return pointer from the entry memory `tail`: nothing above it is in `[a, a + 8)`. -/
theorem ret_read (mem0 : Addr Int → Cell W32 Int) (t st : State W32 Int) (a : Addr Int) (tail W : CLog)
    (hW : Outside (a.plusI (-200)) 208 W)
    (hmem : t.mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail)) :
    loadVal mem0 t a = loadVal mem0 { t with mem := tail } a := by
  obtain ⟨S, hS, hSb⟩ := saveLog_all st (a.plusI (-264)) (pushLog st a 9 tail) 8
  obtain ⟨P, hP, hPb⟩ := pushLog_split st a tail 0 9
  have hP' : pushLog st a 9 tail = P ++ tail := hP
  have hmem' : t.mem = (W ++ S ++ P) ++ tail := by
    rw [hmem, hS, hP']
    simp only [List.append_assoc]
  have hm : MemAg (Cells a 8) tail t.mem := by
    intro x hx
    rw [hmem', Hashtree.Asm.X86.lookup_app_right x _ _ ?_]
    intro p hp he
    obtain ⟨hc1, hc2, hc3⟩ := hx
    rw [← he] at hc1 hc2 hc3
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · rcases hW p hp with h | h | h
        · rw [plusI_off] at h; omega
        · rw [plusI_off] at h; omega
        · exact h (by rw [hc1]; rfl)
      · obtain ⟨_, _, h3⟩ := hSb p hp
        rw [plusI_off] at h3; omega
    · obtain ⟨_, _, h3⟩ := hPb p hp
      push_cast at h3; omega
  exact loadVal_memAg hm mem0 rfl rfl a (M8_of_cells _ _ (fun x hx => hx))

/-! ## The `exec` forms -/

theorem run_one {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool} (prog : Array Instr)
    (s : State W32 Int) (i : Instr) (hh : s.halted = false) (hp : prog[s.pc]? = some i) :
    run prog 4 mem0 orc 1 s = exec 4 mem0 orc i s := by
  simp only [run, hh, Bool.false_eq_true, ite_false, hp]

/-- `add rsp, imm v` on a state whose `rsp` holds `a`. -/
theorem exec_add_rsp_imm {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (s : State W32 Int) (v : Int) (a : Addr Int) (hh : s.halted = false) (h4 : s.getG rsp = .ptr a) :
    exec ro mem0 orc (.alu .add 64 rsp (.imm v)) s
      = { s with
          gpr := s.gpr.set rsp (.ptr (a.plusI v)),
          flags := some ((a.plusI v).off, Ctl.ofInt 0),
          pc := s.pc + 1 } := by
  have hg : gCtl s (.reg rsp) = .ok a := gCtl_reg_ptr s rsp a h4
  have hi : gCtl s (.imm v) = .ok (⟨rNum, Ctl.ofInt v⟩ : Addr Int) := gCtl_imm s v
  simp only [exec, hh, Bool.false_eq_true, ite_false, hg, Hashtree.Asm.X86.bind_ok_eq, hi]
  rw [ite_eq_left trivial]
  rw [ite_eq_right (fun h => nomatch h.1)]
  rw [ite_eq_left (Or.inl trivial)]
  rw [Hashtree.Asm.X86.okOr_pure]
  simp only [State.next, State.setG, setFlags]
  rw [hh]
  rfl

/-! ## Projections through the state constructors (generic states: cheap) -/

theorem next_mem (s : State W32 Int) : s.next.mem = s.mem := rfl
theorem next_halted (s : State W32 Int) : s.next.halted = s.halted := rfl
theorem next_vr (s : State W32 Int) : s.next.vr = s.vr := rfl
theorem next_pc (s : State W32 Int) : s.next.pc = s.pc + 1 := rfl
theorem next_gpr (s : State W32 Int) : s.next.gpr = s.gpr := rfl
theorem next_err (s : State W32 Int) : s.next.err = s.err := rfl
theorem next_tail (s : State W32 Int) : s.next.tail = s.tail := rfl
theorem setG_mem (s : State W32 Int) (i : Nat) (v : Val W32 Int) : (s.setG i v).mem = s.mem := rfl
theorem setG_halted (s : State W32 Int) (i : Nat) (v : Val W32 Int) : (s.setG i v).halted = s.halted := rfl
theorem setG_vr (s : State W32 Int) (i : Nat) (v : Val W32 Int) : (s.setG i v).vr = s.vr := rfl
theorem setG_pc (s : State W32 Int) (i : Nat) (v : Val W32 Int) : (s.setG i v).pc = s.pc := rfl
theorem setG_gpr (s : State W32 Int) (i : Nat) (v : Val W32 Int) : (s.setG i v).gpr = s.gpr.set i v := rfl
theorem setG_err (s : State W32 Int) (i : Nat) (v : Val W32 Int) : (s.setG i v).err = s.err := rfl
theorem setG_tail (s : State W32 Int) (i : Nat) (v : Val W32 Int) : (s.setG i v).tail = s.tail := rfl
theorem setG_getV (s : State W32 Int) (i : Nat) (v : Val W32 Int) (j : Nat) : (s.setG i v).getV j = s.getV j := rfl
theorem halt_mem (s : State W32 Int) : (halt s).mem = s.mem := rfl
theorem halt_gpr (s : State W32 Int) : (halt s).gpr = s.gpr := rfl
theorem halt_getG (s : State W32 Int) (j : Nat) : (halt s).getG j = s.getG j := rfl
theorem halt_getV (s : State W32 Int) (j : Nat) : (halt s).getV j = s.getV j := rfl
theorem halt_err (s : State W32 Int) : (halt s).err = s.err := rfl
theorem halt_tail (s : State W32 Int) : (halt s).tail = s.tail := rfl
theorem halt_vr (s : State W32 Int) : (halt s).vr = s.vr := rfl
theorem setVec_mem (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) : (setVec s vex w d v).mem = s.mem := rfl
theorem setVec_halted (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) : (setVec s vex w d v).halted = s.halted := rfl
theorem setVec_pc (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) : (setVec s vex w d v).pc = s.pc := rfl
theorem setVec_gpr (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) : (setVec s vex w d v).gpr = s.gpr := rfl
theorem setVec_err (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) : (setVec s vex w d v).err = s.err := rfl
theorem setVec_tail (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) : (setVec s vex w d v).tail = s.tail := rfl
theorem setVec_vr_len (s : State W32 Int) (vex : Bool) (w d : Nat) (v : List W32) :
    (setVec s vex w d v).vr.length = s.vr.length := by
  simp only [setVec, State.setV, List.length_set]

/-- Writing a vector register: the low four lanes are the read value (either VEX form). -/
theorem getV_setVec_take (s : State W32 Int) (vex : Bool) (d : Nat) (v : List W32)
    (hd : d < s.vr.length) (hv : v.length = 4) :
    ((setVec s vex 4 d v).getV d).take 4 = v := by
  simp only [setVec, State.setV, State.getV]
  rw [getD_set_self_r5 _ _ hd]
  have ht : v.take 4 = v := List.take_of_length_le (by omega)
  cases vex
  · simp only [Bool.false_eq_true, ite_false, ht]
    exact take_four_append _ _ hv
  · simp only [ite_true, ht]
    exact take_four_append _ _ hv

theorem getV_setVec_ne' (s : State W32 Int) (vex : Bool) (w d j : Nat) (v : List W32) (h : j ≠ d) :
    (setVec s vex w d v).getV j = s.getV j := by
  simp only [setVec, State.setV, State.getV]
  exact getD_set_ne_r5 _ _ _ (Ne.symm h) _ _

/-! ## The eight restores -/

/-- The state after the first `k` restores. -/
def restSt (vex : Bool) (t0 st : State W32 Int) : Nat → State W32 Int
  | 0 => t0
  | k + 1 => (setVec (restSt vex t0 st k) vex 4 (6 + k) ((st.getV (6 + k)).take 4)).next

theorem restSt_succ (vex : Bool) (t0 st : State W32 Int) (k : Nat) :
    restSt vex t0 st (k + 1) = (setVec (restSt vex t0 st k) vex 4 (6 + k) ((st.getV (6 + k)).take 4)).next := rfl

theorem restSt_mem (vex : Bool) (t0 st : State W32 Int) (k : Nat) : (restSt vex t0 st k).mem = t0.mem := by
  induction k with
  | zero => rfl
  | succ k ih => rw [restSt_succ, next_mem, setVec_mem, ih]

theorem restSt_halted (vex : Bool) (t0 st : State W32 Int) (k : Nat) : (restSt vex t0 st k).halted = t0.halted := by
  induction k with
  | zero => rfl
  | succ k ih => rw [restSt_succ, next_halted, setVec_halted, ih]

theorem restSt_pc (vex : Bool) (t0 st : State W32 Int) (k : Nat) : (restSt vex t0 st k).pc = t0.pc + k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [restSt_succ, next_pc, setVec_pc, ih]; omega

theorem restSt_gpr (vex : Bool) (t0 st : State W32 Int) (k : Nat) : (restSt vex t0 st k).gpr = t0.gpr := by
  induction k with
  | zero => rfl
  | succ k ih => rw [restSt_succ, next_gpr, setVec_gpr, ih]

theorem restSt_getG (vex : Bool) (t0 st : State W32 Int) (k j : Nat) : (restSt vex t0 st k).getG j = t0.getG j := by
  simp only [State.getG, restSt_gpr]

theorem restSt_err (vex : Bool) (t0 st : State W32 Int) (k : Nat) : (restSt vex t0 st k).err = t0.err := by
  induction k with
  | zero => rfl
  | succ k ih => rw [restSt_succ, next_err, setVec_err, ih]

theorem restSt_tail (vex : Bool) (t0 st : State W32 Int) (k : Nat) : (restSt vex t0 st k).tail = t0.tail := by
  induction k with
  | zero => rfl
  | succ k ih => rw [restSt_succ, next_tail, setVec_tail, ih]

theorem restSt_vr_len (vex : Bool) (t0 st : State W32 Int) (k : Nat) :
    (restSt vex t0 st k).vr.length = t0.vr.length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [restSt_succ, next_vr, setVec_vr_len, ih]

/-- A register not yet restored still holds what it held at the start. -/
theorem restSt_getV_ne (vex : Bool) (t0 st : State W32 Int) (k d : Nat)
    (hd : ∀ l, l < k → d ≠ 6 + l) : (restSt vex t0 st k).getV d = t0.getV d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [restSt_succ, getV_next, getV_setVec_ne' _ _ _ _ _ _ (hd k (by omega))]
    exact ih (fun l hl => hd l (by omega))

/-- The register restored at slot `j` (`j < k`): its low four lanes are the saved ones. -/
theorem restSt_getV_after (vex : Bool) (t0 st : State W32 Int) (j : Nat) (hvr : 16 ≤ t0.vr.length)
    (hvlen : 4 ≤ (st.getV (6 + j)).length) :
    ∀ k, k ≤ 8 → j < k → ((restSt vex t0 st k).getV (6 + j)).take 4 = (st.getV (6 + j)).take 4 := by
  intro k
  induction k with
  | zero => intro _ hj; omega
  | succ k ih =>
    intro hk hj
    rw [restSt_succ, getV_next]
    by_cases hjk : j = k
    · subst hjk
      exact getV_setVec_take _ _ _ _ (by rw [restSt_vr_len]; omega) (by rw [List.length_take]; omega)
    · rw [getV_setVec_ne' _ _ _ _ _ _ (by omega)]
      exact ih (by omega) (by omega)

theorem run_rest {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool} (prog : Array Instr) (q0 : Nat) (vex : Bool)
    (hrest : ∀ m, m < 8 → prog[q0 + m]? = some (restStep vex m))
    (t0 st : State W32 Int) (a : Addr Int) (tail W : CLog)
    (hh : t0.halted = false) (hpc : t0.pc = q0) (hrsp : t0.getG rsp = .ptr (a.plusI (-264)))
    (hW : Outside (a.plusI (-200)) 208 W)
    (hmem : t0.mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail))
    (hvlen : ∀ k, k < 8 → 4 ≤ (st.getV (6 + k)).length) :
    ∀ k, k ≤ 8 → run prog 4 mem0 orc k t0 = restSt vex t0 st k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk8
    have hk : k < 8 := by omega
    have hh' : (restSt vex t0 st k).halted = false := by rw [restSt_halted, hh]
    have hpc' : (restSt vex t0 st k).pc = q0 + k := by rw [restSt_pc, hpc]
    have hrsp' : (restSt vex t0 st k).getG rsp = .ptr (a.plusI (-264)) := by rw [restSt_getG]; exact hrsp
    have hmem' : (restSt vex t0 st k).mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail) := by
      rw [restSt_mem]; exact hmem
    have hv := rest_read mem0 (restSt vex t0 st k) st a tail W hW hmem' hrsp' k hk (hvlen k hk)
    rw [run_add prog 4 mem0 orc k 1, ih (by omega)]
    rw [run_one prog (restSt vex t0 st k) (restStep vex k) hh' (by rw [hpc']; exact hrest k hk)]
    rw [restStep, exec_vload_ok (restSt vex t0 st k) vex 4 (6 + k) _ _ hh' hv]
    rfl

/-! ## The nine pops -/

/-- The state after `add rsp, 192`: `rsp = a - 72`, the flags of the addition, pc `q0 + 9`. -/
def addSt (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) : State W32 Int :=
  { restSt vex t0 st 8 with
    gpr := (restSt vex t0 st 8).gpr.set rsp (.ptr (a.plusI (-72))),
    flags := some ((a.plusI (-72)).off, Ctl.ofInt 0),
    pc := (restSt vex t0 st 8).pc + 1 }

theorem addSt_eq (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    addSt vex t0 st a =
      { restSt vex t0 st 8 with
        gpr := (restSt vex t0 st 8).gpr.set rsp (.ptr (a.plusI (-72))),
        flags := some ((a.plusI (-72)).off, Ctl.ofInt 0),
        pc := (restSt vex t0 st 8).pc + 1 } := rfl

theorem addSt_mem (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    (addSt vex t0 st a).mem = t0.mem := by simp only [addSt, restSt_mem]
theorem addSt_halted (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    (addSt vex t0 st a).halted = t0.halted := by simp only [addSt, restSt_halted]
theorem addSt_pc (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    (addSt vex t0 st a).pc = t0.pc + 9 := by simp only [addSt, restSt_pc]
theorem addSt_gpr (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    (addSt vex t0 st a).gpr = t0.gpr.set rsp (.ptr (a.plusI (-72))) := by simp only [addSt, restSt_gpr]
theorem addSt_vr (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    (addSt vex t0 st a).vr = (restSt vex t0 st 8).vr := by simp only [addSt]
theorem addSt_err (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    (addSt vex t0 st a).err = t0.err := by simp only [addSt, restSt_err]
theorem addSt_tail (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    (addSt vex t0 st a).tail = t0.tail := by simp only [addSt, restSt_tail]
theorem addSt_getV (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) (j : Nat) :
    (addSt vex t0 st a).getV j = (restSt vex t0 st 8).getV j := by simp only [State.getV, addSt_vr]

theorem addSt_gpr_len (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    (addSt vex t0 st a).gpr.length = t0.gpr.length := by rw [addSt_gpr, List.length_set]

theorem addSt_rsp (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) (hlen : t0.gpr.length = 16) :
    (addSt vex t0 st a).getG rsp = .ptr (a.plusI (-72)) := by
  simp only [State.getG, addSt_gpr]
  exact getD_set_self_r5 _ _ (by rw [hlen]; decide) _ _

theorem addSt_getG_ne (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) (j : Nat) (hj : j ≠ 4) :
    (addSt vex t0 st a).getG j = t0.getG j := by
  simp only [State.getG, addSt_gpr]
  exact getD_set_ne_r5 _ _ _ (Ne.symm hj) _ _

/-- The state after `k` pops from `A`: the popped registers restored from `st`, `rsp = a - 72 + 8k`. -/
def popSt (A st : State W32 Int) (a : Addr Int) : Nat → State W32 Int
  | 0 => A
  | k + 1 => (((popSt A st a k).setG (popReg k) (st.getG (popReg k))).setG rsp
      (.ptr (a.plusI (8 * ((k + 1 : Nat) : Int) - 72)))).next

theorem popSt_succ (A st : State W32 Int) (a : Addr Int) (k : Nat) :
    popSt A st a (k + 1) = (((popSt A st a k).setG (popReg k) (st.getG (popReg k))).setG rsp
      (.ptr (a.plusI (8 * ((k + 1 : Nat) : Int) - 72)))).next := rfl

theorem popSt_mem (A st : State W32 Int) (a : Addr Int) (k : Nat) : (popSt A st a k).mem = A.mem := by
  induction k with
  | zero => rfl
  | succ k ih => rw [popSt_succ, next_mem, setG_mem, setG_mem, ih]

theorem popSt_halted (A st : State W32 Int) (a : Addr Int) (k : Nat) : (popSt A st a k).halted = A.halted := by
  induction k with
  | zero => rfl
  | succ k ih => rw [popSt_succ, next_halted, setG_halted, setG_halted, ih]

theorem popSt_vr (A st : State W32 Int) (a : Addr Int) (k : Nat) : (popSt A st a k).vr = A.vr := by
  induction k with
  | zero => rfl
  | succ k ih => rw [popSt_succ, next_vr, setG_vr, setG_vr, ih]

theorem popSt_err (A st : State W32 Int) (a : Addr Int) (k : Nat) : (popSt A st a k).err = A.err := by
  induction k with
  | zero => rfl
  | succ k ih => rw [popSt_succ, next_err, setG_err, setG_err, ih]

theorem popSt_tail (A st : State W32 Int) (a : Addr Int) (k : Nat) : (popSt A st a k).tail = A.tail := by
  induction k with
  | zero => rfl
  | succ k ih => rw [popSt_succ, next_tail, setG_tail, setG_tail, ih]

theorem popSt_pc (A st : State W32 Int) (a : Addr Int) (k : Nat) : (popSt A st a k).pc = A.pc + k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [popSt_succ, next_pc, setG_pc, setG_pc, ih]; omega

theorem popSt_gpr_len (A st : State W32 Int) (a : Addr Int) (k : Nat) :
    (popSt A st a k).gpr.length = A.gpr.length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [popSt_succ, next_gpr, setG_gpr, setG_gpr, List.length_set, List.length_set, ih]

theorem popSt_getV (A st : State W32 Int) (a : Addr Int) (k j : Nat) : (popSt A st a k).getV j = A.getV j := by
  simp only [State.getV, popSt_vr]

theorem popSt_rsp (A st : State W32 Int) (a : Addr Int) (hA4 : A.getG rsp = .ptr (a.plusI (-72)))
    (hlen : 4 < A.gpr.length) :
    ∀ k, (popSt A st a k).getG rsp = .ptr (a.plusI (8 * (k : Int) - 72)) := by
  intro k
  cases k with
  | zero =>
    rw [show (8 * ((0 : Nat) : Int) - 72) = -72 from by omega]
    exact hA4
  | succ k =>
    rw [popSt_succ, getG_next]
    exact Hashtree.Proofs.FrameLift.getG_setG_self' _ _ _ (by
      rw [setG_gpr, List.length_set, popSt_gpr_len]; exact hlen)

theorem exec_popSt {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (A st : State W32 Int) (a : Addr Int) (tail W : CLog)
    (hhA : A.halted = false) (hlen : A.gpr.length = 16) (hA4 : A.getG rsp = .ptr (a.plusI (-72)))
    (hW : Outside (a.plusI (-200)) 208 W)
    (hmemA : A.mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail))
    (k : Nat) (hk : k < 9) :
    exec 4 mem0 orc (.pop (popReg k)) (popSt A st a k) = popSt A st a (k + 1) := by
  have hh' : (popSt A st a k).halted = false := by rw [popSt_halted]; exact hhA
  have h4 : (popSt A st a k).getG rsp = .ptr (a.plusI (8 * (k : Int) - 72)) :=
    popSt_rsp A st a hA4 (by rw [hlen]; decide) k
  have hv : loadVal mem0 (popSt A st a k) (a.plusI (8 * (k : Int) - 72)) = .ok (st.getG (popReg k)) := by
    rw [loadVal_mem_eq (s := A) (t := popSt A st a k) (popSt_mem A st a k)]
    exact pop_read mem0 A st a tail W hW hmemA k hk
  rw [exec_pop (popReg k) hh' h4 hv]
  have e : (a.plusI (8 * (k : Int) - 72)).plusI 8 = a.plusI (8 * ((k + 1 : Nat) : Int) - 72) := by
    rw [plusI_add]; congr 1; push_cast; omega
  rw [e, popSt_succ]

theorem run_pops {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool} (prog : Array Instr) (q1 : Nat)
    (hpop : ∀ k, k < 9 → prog[q1 + k]? = some (.pop (popReg k)))
    (A st : State W32 Int) (a : Addr Int) (tail W : CLog)
    (hhA : A.halted = false) (hlen : A.gpr.length = 16) (hA4 : A.getG rsp = .ptr (a.plusI (-72)))
    (hW : Outside (a.plusI (-200)) 208 W)
    (hmemA : A.mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail))
    (hpcA : A.pc = q1) :
    ∀ k, k ≤ 9 → run prog 4 mem0 orc k A = popSt A st a k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk9
    have hk : k < 9 := by omega
    rw [run_add prog 4 mem0 orc k 1, ih (by omega)]
    rw [run_one prog (popSt A st a k) (.pop (popReg k)) (by rw [popSt_halted]; exact hhA)
      (by rw [popSt_pc, hpcA]; exact hpop k hk)]
    exact exec_popSt A st a tail W hhA hlen hA4 hW hmemA k hk

/-! ## The whole epilogue -/

/-- The state after the epilogue: halted, `rsp = a + 8`, the nine pops and eight restores applied. -/
def backFinal (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) : State W32 Int :=
  halt ((popSt (addSt vex t0 st a) st a 9).setG rsp (.ptr (a.plusI 8)))

theorem backFinal_eq (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    backFinal vex t0 st a = halt ((popSt (addSt vex t0 st a) st a 9).setG rsp (.ptr (a.plusI 8))) := rfl

/-- **The x1 epilogue.**  Nineteen instructions carry the body-exit state `t0` (pc `q0`,
`rsp = a - 264`, the body's writes `W` over the prologue's image, `W` outside `[a - 200, a + 8)`)
to the halted `backFinal` state, provided the eight bytes at `a` of the entry memory `tail` are
the return pointer. -/
theorem run_back {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool} (prog : Array Instr) (q0 : Nat) (vex : Bool)
    (hrest : ∀ m, m < 8 → prog[q0 + m]? = some (restStep vex m))
    (hadd : prog[q0 + 8]? = some (.alu .add 64 rsp (.imm 192)))
    (hpop : ∀ k, k < 9 → prog[q0 + 9 + k]? = some (.pop (popReg k)))
    (hret : prog[q0 + 18]? = some .ret)
    (t0 st : State W32 Int) (a : Addr Int) (tail W : CLog)
    (hh : t0.halted = false) (hpc : t0.pc = q0) (hrsp : t0.getG rsp = .ptr (a.plusI (-264)))
    (hlen : t0.gpr.length = 16)
    (hW : Outside (a.plusI (-200)) 208 W)
    (hmem : t0.mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail))
    (hvlen : ∀ k, k < 8 → 4 ≤ (st.getV (6 + k)).length)
    (hretv : loadVal mem0 { t0 with mem := tail } a = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int))) :
    run prog 4 mem0 orc 19 t0 = backFinal vex t0 st a := by
  rw [show (19 : Nat) = 8 + (1 + (9 + 1)) from rfl, run_add,
    run_rest prog q0 vex hrest t0 st a tail W hh hpc hrsp hW hmem hvlen 8 (by omega)]
  have hh8 : (restSt vex t0 st 8).halted = false := by rw [restSt_halted, hh]
  have hpc8 : (restSt vex t0 st 8).pc = q0 + 8 := by rw [restSt_pc, hpc]
  have hrsp8 : (restSt vex t0 st 8).getG rsp = .ptr (a.plusI (-264)) := by rw [restSt_getG]; exact hrsp
  rw [run_add, run_one prog (restSt vex t0 st 8) (.alu .add 64 rsp (.imm 192)) hh8 (by rw [hpc8]; exact hadd)]
  rw [exec_add_rsp_imm (restSt vex t0 st 8) 192 (a.plusI (-264)) hh8 hrsp8]
  have e1 : (a.plusI (-264)).plusI 192 = a.plusI (-72) := by rw [plusI_add]; rfl
  rw [e1]
  rw [← addSt_eq]
  have hhA : (addSt vex t0 st a).halted = false := by rw [addSt_halted]; exact hh
  have hpcA : (addSt vex t0 st a).pc = q0 + 9 := by rw [addSt_pc, hpc]
  have hlenA : (addSt vex t0 st a).gpr.length = 16 := by rw [addSt_gpr_len, hlen]
  have hA4 : (addSt vex t0 st a).getG rsp = .ptr (a.plusI (-72)) := addSt_rsp vex t0 st a hlen
  have hmemA : (addSt vex t0 st a).mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail) := by
    rw [addSt_mem]; exact hmem
  rw [run_add, run_pops prog (q0 + 9) hpop (addSt vex t0 st a) st a tail W hhA hlenA hA4 hW hmemA hpcA 9 (by omega)]
  have hh9 : (popSt (addSt vex t0 st a) st a 9).halted = false := by rw [popSt_halted]; exact hhA
  have hpc9 : (popSt (addSt vex t0 st a) st a 9).pc = q0 + 18 := by rw [popSt_pc, hpcA]
  have hrsp9 : (popSt (addSt vex t0 st a) st a 9).getG rsp = .ptr (a.plusI (8 * ((9 : Nat) : Int) - 72)) :=
    popSt_rsp _ _ _ hA4 (by rw [hlenA]; try decide) 9
  have h9 : a.plusI (8 * ((9 : Nat) : Int) - 72) = a := by
    rw [show (8 * ((9 : Nat) : Int) - 72) = 0 from by first | decide | (push_cast; omega)]
    exact plusI_zero a
  rw [h9] at hrsp9
  have hret9 : loadVal mem0 (popSt (addSt vex t0 st a) st a 9) a = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int)) := by
    rw [ret_read mem0 _ st a tail W hW (by rw [popSt_mem]; exact hmemA)]
    rw [loadVal_mem_eq (s := { t0 with mem := tail }) (t := { popSt (addSt vex t0 st a) st a 9 with mem := tail }) rfl]
    exact hretv
  rw [run_one prog (popSt (addSt vex t0 st a) st a 9) .ret hh9 (by rw [hpc9]; exact hret)]
  rw [exec_ret_ok (popSt (addSt vex t0 st a) st a 9) a 0 hh9 hrsp9 hret9, backFinal_eq]

/-! ## The final state -/

theorem backFinal_halted (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) : (backFinal vex t0 st a).halted = true := by
  rw [backFinal_eq]; rfl

theorem backFinal_mem (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) : (backFinal vex t0 st a).mem = t0.mem := by
  rw [backFinal_eq, halt_mem, setG_mem, popSt_mem, addSt_mem]

theorem backFinal_err (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) : (backFinal vex t0 st a).err = t0.err := by
  rw [backFinal_eq, halt_err, setG_err, popSt_err, addSt_err]

theorem backFinal_tail (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) : (backFinal vex t0 st a).tail = t0.tail := by
  rw [backFinal_eq, halt_tail, setG_tail, popSt_tail, addSt_tail]

theorem backFinal_gpr_len (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) :
    (backFinal vex t0 st a).gpr.length = t0.gpr.length := by
  rw [backFinal_eq, halt_gpr, setG_gpr, List.length_set, popSt_gpr_len, addSt_gpr_len]

/-- The epilogue returns with `rsp = a + 8` (the return address popped). -/
theorem backFinal_rsp (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) (hlen : t0.gpr.length = 16) :
    (backFinal vex t0 st a).getG rsp = .ptr (a.plusI 8) := by
  rw [backFinal_eq, halt_getG]
  exact Hashtree.Proofs.FrameLift.getG_setG_self' _ _ _ (by rw [popSt_gpr_len, addSt_gpr_len, hlen]; try decide)

/-- A register restored by pop `j` keeps its value through the later pops. -/
theorem popSt_getG_restored (A st : State W32 Int) (a : Addr Int) (hlen : A.gpr.length = 16) (j : Nat) (hj : j < 9) :
    ∀ k, j < k → k ≤ 9 → (popSt A st a k).getG (popReg j) = st.getG (popReg j) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hjk hk9
    rw [popSt_succ, getG_next, getG_setG_of_ne _ _ _ _ (show ¬ popReg j = rsp from popReg_ne4 j hj)]
    by_cases hjk' : j = k
    · subst hjk'
      exact Hashtree.Proofs.FrameLift.getG_setG_self' _ _ _ (by rw [popSt_gpr_len, hlen]; exact popReg_lt16 j hj)
    · rw [getG_setG_of_ne _ _ _ _ (popReg_inj j k hj (by omega) hjk')]
      exact ih (by omega) (by omega)

/-- A register no pop writes keeps its value through the pops. -/
theorem popSt_getG_other (A st : State W32 Int) (a : Addr Int) (r : Nat) (hr : r ≠ 4)
    (hr' : ∀ j, j < 9 → r ≠ popReg j) : ∀ k, k ≤ 9 → (popSt A st a k).getG r = A.getG r := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk9
    rw [popSt_succ, getG_next, getG_setG_of_ne _ _ _ _ (show ¬ r = rsp from hr),
      getG_setG_of_ne _ _ _ _ (hr' k (by omega))]
    exact ih (by omega)

/-- **The nine pushed registers come back** with their entry values. -/
theorem backFinal_getG_saved (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) (hlen : t0.gpr.length = 16)
    (j : Nat) (hj : j < 9) : (backFinal vex t0 st a).getG (popReg j) = st.getG (popReg j) := by
  rw [backFinal_eq, halt_getG, getG_setG_of_ne _ _ _ _ (show ¬ popReg j = rsp from popReg_ne4 j hj)]
  exact popSt_getG_restored (addSt vex t0 st a) st a (by rw [addSt_gpr_len, hlen]) j hj 9 hj (by omega)

/-- Every other general register is as at the body exit. -/
theorem backFinal_getG_other (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) (r : Nat) (hr : r ≠ 4)
    (hr' : ∀ j, j < 9 → r ≠ popReg j) : (backFinal vex t0 st a).getG r = t0.getG r := by
  rw [backFinal_eq, halt_getG, getG_setG_of_ne _ _ _ _ (show ¬ r = rsp from hr),
    popSt_getG_other (addSt vex t0 st a) st a r hr hr' 9 (by omega), addSt_getG_ne _ _ _ _ r hr]

/-- **The eight callee-saved vector registers come back**: the low four lanes of `xmm6`-`xmm13`
are the lanes the prologue saved. -/
theorem backFinal_getV (vex : Bool) (t0 st : State W32 Int) (a : Addr Int) (hvr : 16 ≤ t0.vr.length)
    (hvlen : ∀ k, k < 8 → 4 ≤ (st.getV (6 + k)).length) (j : Nat) (hj : j < 8) :
    ((backFinal vex t0 st a).getV (6 + j)).take 4 = (st.getV (6 + j)).take 4 := by
  rw [backFinal_eq, halt_getV, setG_getV, popSt_getV, addSt_getV]
  exact restSt_getV_after vex t0 st j hvr (hvlen j hj) 8 (by omega) hj

end Hashtree.Proofs.WinX1Back
