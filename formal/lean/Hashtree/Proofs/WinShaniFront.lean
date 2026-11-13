import Hashtree.Proofs.WinShani
import Hashtree.Proofs.WinFrameStack

/-!
# R5: `shani_x2` prologue steps

The first steps of the windows `shani_x2` prologue, proved from the machine semantics:

```
pc 0     : sub rsp, 248                     -- exec_sub_rsp
pc 1..10 : vstore 4 [rsp + 16k] (xmm{6+k})  -- exec_vstore_rsp
```

`laneLog` is the write log of a `storeLanes` (four byte cells per lane, newest first), so
`mem_storeLanes` reads the prologue's memory effect, which is the prefix `saveLog` of the
composition in `formal/notes/R5.md` section 6.
-/

open Hashtree.Asm Hashtree.Asm.X86
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinShaniFront

/-! ## `Except` reductions (copies of the one-liners in `Proofs.Win64`) -/

theorem gCtl_reg_ptr (s : State W32 Int) (d : Nat) (a : Addr Int) (h : s.getG d = .ptr a) :
    gCtl s (.reg d) = .ok a := by
  simp only [gCtl, h]
  rfl

theorem gCtl_imm (s : State W32 Int) (v : Int) :
    gCtl s (.imm v) = .ok (⟨rNum, v⟩ : Addr Int) := by
  simp only [gCtl]
  rfl

theorem bind_ok_eq {β δ : Type} (b : β) (k : β → Except String δ) :
    ((Except.ok b : Except String β) >>= k) = k b := rfl

theorem okOr_pure (s t : State W32 Int) : okOr s (pure t) = t := rfl

/-! ## The write log of `storeLanes` -/

/-- The cells written by `storeLanes s a xs` (newest first), as a function of `a` and `xs`. -/
def laneLog (a : Addr Int) : List W32 → List (Addr Int × Cell W32 Int)
  | [] => []
  | x :: xs => laneLog (a.plusI 4) xs ++ [(a.plusI 3, .dat x 3), (a.plusI 2, .dat x 2), (a.plusI 1, .dat x 1), (a, .dat x 0)]

/-- `storeLanes` changes only `mem`. -/
theorem storeLanes_rec (s : State W32 Int) (a : Addr Int) (xs : List W32) :
    storeLanes s a xs = { s with mem := laneLog a xs ++ s.mem } := by
  induction xs generalizing a s with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [laneLog, storeLanes]
    rw [ih]
    simp only [storeLane, List.append_assoc, List.cons_append, List.nil_append]

theorem mem_storeLanes (s : State W32 Int) (a : Addr Int) (xs : List W32) :
    (storeLanes s a xs).mem = laneLog a xs ++ s.mem := by
  rw [storeLanes_rec]

/-! ## The `sub rsp, imm` prologue instruction -/

/-- `sub 64 rsp (imm v)` on a state whose `rsp` holds the pointer `a`: `rsp` becomes `a - v`,
the flags record the subtraction, and the pc advances. -/
theorem exec_sub_rsp (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int) (v : Int) (a : Addr Int) (hh : s.halted = false) (h4 : s.getG rsp = .ptr a) :
    exec ro mem0 orc (.sub 64 rsp (.imm v)) s = { s with gpr := s.gpr.set rsp (.ptr (a.plusI (-v))), flags := some (a.off, v), pc := s.pc + 1 } := by
  have hg : gCtl s (.reg rsp) = .ok a := gCtl_reg_ptr s rsp a h4
  have hi : gCtl s (.imm v) = .ok (⟨rNum, (v : Int)⟩ : Addr Int) := gCtl_imm s v
  have hr : (a.plus (Ctl.smul (-1) v) : Addr Int) = a.plusI (-v) := by
    simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.smul, Ctl.ofInt, id_eq]
    rw [show (-1 : Int) * v = -v from by omega]
  simp only [exec, hh, Bool.false_eq_true, ite_false]
  rw [ite_eq_left trivial]
  rw [hg, bind_ok_eq, hi, bind_ok_eq]
  rw [ite_eq_left rfl]
  rw [okOr_pure, hr]
  simp only [State.next, State.setG, setFlags, hh]

/-! ## The `vstore 4 [rsp + d] src` prologue instruction -/

/-- `vstore w [rsp + d] src` on a state whose `rsp` holds the pointer `a`: the `w` lanes of `src`
are stored at `a + d` (four byte cells each), `mem` grows by `laneLog`, and the pc advances. -/
theorem exec_vstore_rsp (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (s : State W32 Int) (w src : Nat) (d : Int) (a : Addr Int) (hh : s.halted = false) (h4 : s.getG rsp = .ptr a) :
    exec ro mem0 orc (.vstore w { base := some rsp, disp := d } src) s = { s with mem := laneLog (a.plusI d) ((s.getV src).take w) ++ s.mem, pc := s.pc + 1 } := by
  have he : effAddr ro s ({ base := some rsp, disp := d } : MemRef) = .ok (a.plusI d) := by
    simp only [effAddr, baseAddr, regPtr, h4]
  simp only [exec, hh, Bool.false_eq_true, ite_false]
  rw [he, bind_ok_eq, okOr_pure, storeLanes_rec]
  simp only [State.next, hh]

/-! ## The concrete prologue of the shipped stream -/

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Shani.prog

/-- The `m`-th callee-save store of the prologue: `vstore 4 [rsp + 16 m] (xmm{6+m})`. -/
def saveStep (m : Nat) : Instr := .vstore 4 { base := some rsp, disp := ((16 * m : Nat) : Int) } (6 + m)

/-- Lookup check for the prologue stores, for the kernel scan. -/
def saveLookupB (m : Nat) : Bool :=
  match winProg[1 + m]? with
  | some i => decide (i = saveStep m)
  | none => false

/-- Kernel-checked: the ten prologue stores are at pcs `1 … 10`, with the expected operands. -/
theorem save_lookups : ((List.range 10).all saveLookupB) = true := by decide +kernel

/-- The prologue store at index `m < 10` is `saveStep m`. -/
theorem save_lookup (m : Nat) (hm : m < 10) : winProg[1 + m]? = some (saveStep m) := by
  have h := List.all_eq_true.mp save_lookups m (List.mem_range.mpr hm)
  unfold saveLookupB at h
  split at h
  · rename_i i hi
    rw [hi]
    rw [show i = saveStep m from of_decide_eq_true h]
  · exact nomatch h

/-- The first instruction of the shipped stream is the stack-pointer decrement. -/
theorem sub_lookup : winProg[0]? = some (.sub 64 rsp (.imm 248)) := by decide

/-! ## The save log -/

/-- The memory log written by the ten prologue stores, newest first, over the tail `tail`. -/
def saveLog (st : State W32 Int) (r : Addr Int) : Nat → List (Addr Int × Cell W32 Int) → List (Addr Int × Cell W32 Int)
  | 0, tail => tail
  | k + 1, tail => laneLog (r.plusI ((16 * k : Nat) : Int)) ((st.getV (6 + k)).take 4) ++ saveLog st r k tail

/-- The state after `m` prologue stores, from an entry state whose `rsp` holds `a`: `rsp` is
`a - 248`, the flags are those of `sub rsp, 248`, the memory holds the first `m` save slots, and
the pc is `1 + m`. -/
def saveSt (st : State W32 Int) (a : Addr Int) (m : Nat) : State W32 Int :=
  { st with gpr := st.gpr.set rsp (.ptr (a.plusI (-248))), flags := some (a.off, 248), mem := saveLog st (a.plusI (-248)) m st.mem, pc := 1 + m }

/-- One prologue store, from the `m`-th to the `(m+1)`-th save state. -/
theorem exec_saveSt (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int) (hh : st.halted = false) (hlen : st.gpr.length = 16) (m : Nat) :
    exec ro mem0 orc (saveStep m) (saveSt st a m) = saveSt st a (m + 1) := by
  have h4 : (saveSt st a m).getG rsp = .ptr (a.plusI (-248)) := by
    simp only [saveSt, State.getG]
    exact getD_set_self st.gpr rsp (by rw [rsp]; omega) (.ptr (a.plusI (-248))) _
  have hh' : (saveSt st a m).halted = false := by
    simp only [saveSt, hh]
  rw [show saveStep m = .vstore 4 { base := some rsp, disp := ((16 * m : Nat) : Int) } (6 + m) from rfl]
  rw [exec_vstore_rsp ro mem0 orc _ 4 (6 + m) ((16 * m : Nat) : Int) (a.plusI (-248)) hh' h4]
  simp only [saveSt, saveLog, State.getV]
  rw [show 1 + m + 1 = 1 + (m + 1) from by omega]

/-! ## The prologue replay -/

/-- `run` of one step at a known instruction. -/
theorem run_succ_step (prog : Array Instr) (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (n : Nat) (s : State W32 Int) (i : Instr) (hh : s.halted = false) (hp : prog[s.pc]? = some i) :
    run prog ro mem0 orc (n + 1) s = run prog ro mem0 orc n (exec ro mem0 orc i s) := by
  simp only [run, hh, Bool.false_eq_true, ite_false, hp]

/-- The ten stores, `k` steps at a time. -/
theorem run_saves (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int) (hh : st.halted = false) (hlen : st.gpr.length = 16) :
    ∀ (m k : Nat), m + k ≤ 10 → run winProg ro mem0 orc k (saveSt st a m) = saveSt st a (m + k) := by
  intro m k
  induction k generalizing m with
  | zero =>
    intro _
    exact (show run winProg ro mem0 orc 0 (saveSt st a m) = saveSt st a (m + 0) from rfl)
  | succ k ih =>
    intro hk
    have hm : m < 10 := by omega
    rw [run_succ_step winProg ro mem0 orc k (saveSt st a m) (saveStep m) (by simp only [saveSt, hh]) (by simp only [saveSt, save_lookup m hm])]
    rw [exec_saveSt ro mem0 orc st a hh hlen m]
    rw [ih (m + 1) (by omega)]
    rw [show (m + 1) + k = m + (k + 1) from by omega]

/-- **The `shani_x2` prologue.**  Eleven instructions carry an ABI state with `rsp = a` to the
body-entry state of the windows stream: `rsp` is `a - 248`, the flags are those of `sub rsp, 248`,
the ten callee-save slots hold xmm6-xmm15, and the pc is 11. -/
theorem run_prologue (ro : Region) (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int) (hh : st.halted = false) (h4 : st.getG rsp = .ptr a) (hlen : st.gpr.length = 16) :
    run winProg ro mem0 orc 11 { st with pc := 0 } = saveSt st a 10 := by
  have hsub : exec ro mem0 orc (.sub 64 rsp (.imm 248)) { st with pc := 0 } = saveSt st a 0 := by
    rw [exec_sub_rsp ro mem0 orc { st with pc := 0 } 248 a (by simp only [hh]) h4]
    simp only [saveSt, saveLog]
  rw [show (11 : Nat) = 10 + 1 from rfl]
  rw [run_succ_step winProg ro mem0 orc 10 { st with pc := 0 } (.sub 64 rsp (.imm 248)) (by simp only [hh]) (by simp only [sub_lookup])]
  rw [hsub]
  exact run_saves ro mem0 orc st a hh hlen 0 10 (by omega)

end Hashtree.Proofs.WinShaniFront
