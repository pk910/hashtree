import Hashtree.Proofs.WinShaniFlags
import Hashtree.Proofs.WinShaniFront
import Hashtree.Asm.X86Loop
import Hashtree.Asm.Hom

/-!
# R5: the epilogue of the windows `shani_x2` kernel

The prologue (`Proofs/WinShaniFront.lean`) saves `xmm6`-`xmm15` into the 160-byte stack slot
`[rsp, rsp + 160)`; the body (`formal/notes/R5.md` section 6) only writes outside that slot; the
epilogue must therefore read each saved lane back and restore its low four lanes.

This file proves that readback and replays the twelve epilogue instructions from the machine
semantics (`Hashtree.Kernels.X86Win.Shani.prog`):

```
pc 679..688 : vload 4 xmm{6+k}, [rsp + 16k]   -- readVSrc_save / run_epi
pc 689      : add rsp, 248                    -- exec_add64_rsp
pc 690      : ret                             -- exec_ret_ok
```

The readback is done through the *write log* rather than through concrete cells: a read inside
slot `k` skips every newer entry of `saveLog` (`lookup_saveLog_from`), lands on the four byte
cells of the right lane (`lookup_laneLog_lane`), and reassembles the lane (`loadLane_dat`,
`bytes_reassemble`).  The body's own writes are ignored by `Outside r 160 W`, the predicate that
`shani_save_slots_untouched` discharges for the shipped stream.

The main results are `run_epilogue` (the full twelve-step replay into `epiFinal`) and
`run_epilogue_getV` (the ten callee-saved vector registers come back lane for lane).
-/

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinShaniFront
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Hashtree.Proofs.WinShaniEpi

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.Shani.prog

theorem plusI_zero (r : Addr Int) : r.plusI 0 = r := by
  simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq, Int.add_zero]

theorem plusI_add (r : Addr Int) (i j : Int) : (r.plusI i).plusI j = r.plusI (i + j) := by
  simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq, Int.add_assoc]

theorem plusI_off (r : Addr Int) (i : Int) : (r.plusI i).off = r.off + i := by
  simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq]

theorem plusI_region (r : Addr Int) (i : Int) : (r.plusI i).region = r.region := rfl

theorem same_self (a : Addr Int) : AddrEq.same a a = some true := by
  simp only [AddrEq.same, beq_self_eq_true, Bool.true_and]

theorem same_ne (a b : Addr Int) (h : b ≠ a) : AddrEq.same a b = some false := by
  obtain ⟨ra, oa⟩ := a
  obtain ⟨rb, ob⟩ := b
  simp only [AddrEq.same]
  simp only [ne_eq, Addr.mk.injEq] at h
  by_cases hr : ra = rb
  · subst hr
    have ho : oa ≠ ob := fun hh => h ⟨rfl, hh.symm⟩
    simp [ho]
  · simp [hr]

theorem plusI_ne (r : Addr Int) (i j : Int) (h : i ≠ j) : r.plusI i ≠ r.plusI j := by
  intro he
  have h2 := congrArg Addr.off he
  simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq] at h2
  omega

theorem same_plusI (r : Addr Int) (i j : Int) (h : i ≠ j) :
    AddrEq.same (r.plusI i) (r.plusI j) = some false :=
  same_ne _ _ (plusI_ne r j i (Ne.symm h))

def laneAddr (a : Addr Int) : Nat → Addr Int
  | 0 => a
  | k + 1 => (laneAddr a k).plusI 4

theorem laneAddr_shift (a : Addr Int) (j : Nat) :
    laneAddr (a.plusI 4) j = (laneAddr a j).plusI 4 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show (laneAddr (a.plusI 4) j).plusI 4 = ((laneAddr a j).plusI 4).plusI 4
    rw [ih]

theorem laneAddr_zero (a : Addr Int) : laneAddr a 0 = a := rfl

theorem laneAddr_region (a : Addr Int) (j : Nat) : (laneAddr a j).region = a.region := by
  induction j with
  | zero => rfl
  | succ j ih => rw [laneAddr]; exact ih

theorem laneAddr_off (a : Addr Int) (j : Nat) :
    (laneAddr a j).off = a.off + ((4 * j : Nat) : Int) := by
  induction j with
  | zero => rw [laneAddr, Nat.mul_zero, Int.ofNat_zero, Int.add_zero]
  | succ j ih =>
    rw [laneAddr, plusI_off, ih]
    have h4 : ((4 * (j + 1) : Nat) : Int) = ((4 * j : Nat) : Int) + 4 := by
      rw [Nat.mul_succ, Int.natCast_add]
      rfl
    rw [h4]
    omega

def laneCells (a : Addr Int) (x : W32) : CLog :=
  [ (a.plusI 3, .dat x 3), (a.plusI 2, .dat x 2), (a.plusI 1, .dat x 1), (a, .dat x 0) ]

theorem laneLog_eq (a : Addr Int) (x : W32) (xs : List W32) :
    laneLog a (x :: xs) = laneLog (a.plusI 4) xs ++ laneCells a x := rfl

theorem lookup_hit (a : Addr Int) (c : Cell W32 Int) (rest : CLog) :
    lookup a ((a, c) :: rest) = .ok (some c) := by
  simp only [lookup, same_self]

theorem same_zero_left (r : Addr Int) : AddrEq.same (r.plusI 0) r = some true := by
  rw [plusI_zero]; exact same_self r

theorem lookup_hit_z (a : Addr Int) (c : Cell W32 Int) (rest : CLog) :
    lookup (a.plusI 0) ((a, c) :: rest) = .ok (some c) := by
  simp only [lookup, same_zero_left]

theorem lookup_skip (a b : Addr Int) (c : Cell W32 Int) (rest : CLog)
    (h : AddrEq.same a b = some false) :
    lookup a ((b, c) :: rest) = lookup a rest := by
  simp only [lookup, h]

theorem lookup_laneCells (a : Addr Int) (x : W32) (b : Nat) (hb : b < 4) :
    lookup (a.plusI (b : Int)) (laneCells a x) = .ok (some (.dat x b)) := by
  rcases b with _ | _ | _ | _ | b
  · show lookup (a.plusI (0 : Int)) (laneCells a x) = .ok (some (.dat x 0))
    simp only [laneCells]
    rw [lookup_skip _ _ _ _ (same_plusI a 0 3 (by decide)),
        lookup_skip _ _ _ _ (same_plusI a 0 2 (by decide)),
        lookup_skip _ _ _ _ (same_plusI a 0 1 (by decide))]
    exact lookup_hit_z a (.dat x 0) _
  · show lookup (a.plusI (1 : Int)) (laneCells a x) = .ok (some (.dat x 1))
    simp only [laneCells]
    rw [lookup_skip _ _ _ _ (same_plusI a 1 3 (by decide)),
        lookup_skip _ _ _ _ (same_plusI a 1 2 (by decide))]
    exact lookup_hit (a.plusI 1) (.dat x 1) _
  · show lookup (a.plusI (2 : Int)) (laneCells a x) = .ok (some (.dat x 2))
    simp only [laneCells]
    rw [lookup_skip _ _ _ _ (same_plusI a 2 3 (by decide))]
    exact lookup_hit (a.plusI 2) (.dat x 2) _
  · show lookup (a.plusI (3 : Int)) (laneCells a x) = .ok (some (.dat x 3))
    simp only [laneCells]
    exact lookup_hit (a.plusI 3) (.dat x 3) _
  · omega

theorem laneLog_bounds (a : Addr Int) (xs : List W32) (p : Addr Int × Cell W32 Int)
    (hp : p ∈ laneLog a xs) : p.1.region = a.region ∧ a.off ≤ p.1.off := by
  induction xs generalizing a with
  | nil => simp only [laneLog, List.not_mem_nil] at hp
  | cons x xs ih =>
    rw [laneLog_eq] at hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · have h' := ih (a.plusI 4) hp
      constructor
      · rw [h'.1]; rfl
      · have := h'.2
        simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq] at this ⊢
        omega
    · simp only [laneCells, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with hp | hp | hp | hp <;> rw [hp] <;>
        exact ⟨by simp only [Addr.plusI, Addr.plus],
          by simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq]; omega⟩

theorem lookup_none_laneLog_low (a q : Addr Int) (xs : List W32)
    (h : q.off < a.off ∨ q.region ≠ a.region) : lookup q (laneLog a xs) = .ok none := by
  apply lookup_none_ne
  intro p hp he
  obtain ⟨hreg, hoff⟩ := laneLog_bounds a xs p hp
  rw [he] at hoff hreg
  rcases h with h | h
  · omega
  · exact h hreg

theorem lookup_laneLog_lane (a : Addr Int) (xs : List W32) (j b : Nat)
    (hj : j < xs.length) (hb : b < 4) :
    lookup ((laneAddr a j).plusI (b : Int)) (laneLog a xs)
      = .ok (some (.dat (xs.getD j (Lane.const 0)) b)) := by
  induction xs generalizing a j with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hj
  | cons x xs ih =>
    rw [laneLog_eq]
    rcases j with _ | j
    · rw [laneAddr_zero]
      rw [lookup_append]
      rw [lookup_none_laneLog_low (a.plusI 4) (a.plusI (b : Int)) xs (Or.inl (by
        simp only [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt, id_eq]
        omega))]
      exact lookup_laneCells a x b hb
    · rw [show (x :: xs).getD (j + 1) (Lane.const 0) = xs.getD j (Lane.const 0) from by
        simp only [List.getD_cons_succ]]
      refine lookup_app_left _ _ _ _ ?_
      have := ih (a.plusI 4) j (by simp only [List.length_cons] at hj; omega)
      rwa [laneAddr_shift] at this

/-! ## Reading cells and lanes through a log prefix -/

theorem readCell_laneLog (mem0 : Addr Int → Cell W32 Int) (t : State W32 Int) (a : Addr Int)
    (xs : List W32) (hmem : t.mem = laneLog a xs) (j b : Nat) (hj : j < xs.length) (hb : b < 4) :
    readCell mem0 t ((laneAddr a j).plusI (b : Int))
      = .ok (.dat (xs.getD j (Lane.const 0)) b) := by
  simp only [readCell, hmem]
  rw [lookup_laneLog_lane a xs j b hj hb]

/-- Read a cell at lane `j`, byte `b` of the block at `a` through an ignored prefix `P`. -/
theorem readCell_laneLog_pre (mem0 : Addr Int → Cell W32 Int) (t : State W32 Int) (P : CLog)
    (a : Addr Int) (xs : List W32) (hmem : t.mem = P ++ laneLog a xs) (j b : Nat)
    (hj : j < xs.length) (hj4 : j < 4) (hb : b < 4)
    (hP : ∀ p ∈ P, p.1.off < a.off ∨ a.off + 16 ≤ p.1.off ∨ p.1.region ≠ a.region) :
    readCell mem0 t ((laneAddr a j).plusI (b : Int))
      = .ok (.dat (xs.getD j (Lane.const 0)) b) := by
  simp only [readCell, hmem]
  rw [lookup_app_right _ P _ (fun p hp => ?_)]
  · rw [lookup_laneLog_lane a xs j b hj hb]
  · -- the query is inside `[a, a + 16)`
    have hqoff : ((laneAddr a j).plusI ((b : Nat) : Int)).off
        = a.off + ((4 * j : Nat) : Int) + (b : Int) := by
      rw [plusI_off, laneAddr_off]
    have hqreg : ((laneAddr a j).plusI ((b : Nat) : Int)).region = a.region := by
      rw [plusI_region, laneAddr_region]
    have hqj : ((4 * j : Nat) : Int) ≥ 0 := Int.natCast_nonneg _
    have hqj4 : ((4 * j : Nat) : Int) < 16 := by
      have : ((4 * j : Nat) : Int) = 4 * (j : Int) := by
        rw [Int.natCast_mul]; rfl
      rw [this]
      have : (j : Int) < 4 := by exact_mod_cast hj4
      omega
    have hqb4 : (b : Int) < 4 := by exact_mod_cast hb
    have hqb0 : (b : Int) ≥ 0 := Int.natCast_nonneg _
    rcases hP p hp with h | h | h
    · -- p below a
      intro he
      have hoff : p.1.off = ((laneAddr a j).plusI (b : Int)).off := congrArg Addr.off he
      omega
    · intro he
      have hoff : p.1.off = ((laneAddr a j).plusI (b : Int)).off := congrArg Addr.off he
      omega
    · intro he
      have hreg : p.1.region = ((laneAddr a j).plusI (b : Int)).region := congrArg Addr.region he
      exact h (by rw [hqreg] at hreg; exact hreg)

theorem loadLane_dat {mem0 : Addr Int → Cell W32 Int} {s : State W32 Int} (a : Addr Int) (x : W32)
    (h0 : readCell mem0 s a = .ok (.dat x 0))
    (h1 : readCell mem0 s (a.plusI 1) = .ok (.dat x 1))
    (h2 : readCell mem0 s (a.plusI 2) = .ok (.dat x 2))
    (h3 : readCell mem0 s (a.plusI 3) = .ok (.dat x 3)) :
    loadLane mem0 s a = .ok x := by
  simp only [loadLane, h0, h1, h2, h3, Hashtree.Asm.X86.bind_ok_eq, lanePat]
  show Except.ok (Lane.or (Lane.or (byteOf x 0) (Lane.shl (byteOf x 1) 8))
      (Lane.or (Lane.shl (byteOf x 2) 16) (Lane.shl (byteOf x 3) 24))) = Except.ok x
  exact congrArg Except.ok (Hashtree.Asm.bytes_reassemble x)

theorem loadLane_laneLog (mem0 : Addr Int → Cell W32 Int) (t : State W32 Int) (a : Addr Int)
    (xs : List W32) (hmem : t.mem = laneLog a xs) (j : Nat) (hj : j < xs.length) :
    loadLane mem0 t (laneAddr a j) = .ok (xs.getD j (Lane.const 0)) := by
  apply loadLane_dat (x := xs.getD j (Lane.const 0))
  · have h := readCell_laneLog mem0 t a xs hmem j 0 hj (by decide)
    rwa [show (laneAddr a j).plusI ((0 : Nat) : Int) = laneAddr a j from plusI_zero _] at h
  · exact readCell_laneLog mem0 t a xs hmem j 1 hj (by decide)
  · exact readCell_laneLog mem0 t a xs hmem j 2 hj (by decide)
  · exact readCell_laneLog mem0 t a xs hmem j 3 hj (by decide)

theorem loadLanes_laneLog (mem0 : Addr Int → Cell W32 Int) (t : State W32 Int) (a : Addr Int)
    (xs : List W32) (hmem : t.mem = laneLog a xs) :
    ∀ (n j : Nat), j + n ≤ xs.length →
      loadLanes mem0 t (laneAddr a j) n = .ok ((xs.drop j).take n) := by
  intro n
  induction n with
  | zero => intro j _; rfl
  | succ n ih =>
    intro j hn
    have hj : j < xs.length := by omega
    simp only [loadLanes, loadLane_laneLog mem0 t a xs hmem j hj]
    rw [show (laneAddr a j).plusI 4 = laneAddr a (j + 1) from rfl]
    rw [Hashtree.Asm.X86.bind_ok_eq]
    rw [ih (j + 1) (by omega)]
    rw [Hashtree.Asm.X86.bind_ok_eq]
    congr 1
    rw [List.drop_eq_getElem_cons hj]
    rw [show (xs[j] :: xs.drop (j + 1)).take (n + 1) = xs[j] :: (xs.drop (j + 1)).take n from by
      rw [List.take_succ_cons]]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl

theorem getV_take4_length (st : State W32 Int) (i : Nat) :
    ((st.getV i).take 4).length = min 4 (st.getV i).length := List.length_take


/-! ## The save area of the prologue read back through an outside prefix -/

abbrev saveBlock (st : State W32 Int) (r : Addr Int) (k : Nat) : CLog :=
  laneLog (r.plusI ((16 * k : Nat) : Int)) ((st.getV (6 + k)).take 4)

theorem saveLog_succ (st : State W32 Int) (r : Addr Int) (k : Nat) (tail : CLog) :
    saveLog st r (k + 1) tail = saveBlock st r k ++ saveLog st r k tail := rfl

theorem saveBlock_bounds (st : State W32 Int) (r : Addr Int) (k : Nat)
    (p : Addr Int × Cell W32 Int) (hp : p ∈ saveBlock st r k) :
    p.1.region = r.region ∧ r.off + ((16 * k : Nat) : Int) ≤ p.1.off := by
  have h := laneLog_bounds (r.plusI ((16 * k : Nat) : Int)) ((st.getV (6 + k)).take 4) p hp
  constructor
  · rw [h.1, plusI_region]
  · rw [plusI_off] at h
    exact h.2

/-- Split `saveLog st r n tail` at slot `k`: everything above it, and the rest. -/
theorem saveLog_above (st : State W32 Int) (r : Addr Int) (tail : CLog) :
    ∀ (n k : Nat), k < n → ∃ P : CLog,
      saveLog st r n tail = P ++ (saveBlock st r k ++ saveLog st r k tail) ∧
      (∀ p ∈ P, p.1.region = r.region ∧ r.off + ((16 * (k + 1) : Nat) : Int) ≤ p.1.off) := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | heq
    · obtain ⟨P, hP, hPb⟩ := ih k hlt
      refine ⟨saveBlock st r n ++ P, ?_, ?_⟩
      · rw [saveLog_succ, hP, List.append_assoc]
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · have hb := saveBlock_bounds st r n p hp
          refine ⟨hb.1, ?_⟩
          have hle : ((16 * (k + 1) : Nat) : Int) ≤ ((16 * n : Nat) : Int) := by
            have hnk : k + 1 ≤ n := by omega
            exact_mod_cast Nat.mul_le_mul_left 16 hnk
          omega
        · exact hPb p hp
    · subst heq
      exact ⟨[], by rw [List.nil_append, saveLog_succ], by simp⟩

/-- Reads inside slot `k` never see the blocks above it. -/
theorem lookup_saveLog_from (st : State W32 Int) (r : Addr Int) (tail : CLog) (q : Addr Int) :
    ∀ (n k : Nat), k + 1 ≤ n → r.off ≤ q.off →
      q.off < r.off + ((16 * (k + 1) : Nat) : Int) →
      lookup q (saveLog st r n tail) = lookup q (saveLog st r (k + 1) tail)
  | 0, k, h, _, _ => by omega
  | n + 1, k, h, hq0, hq1 => by
    rw [saveLog_succ]
    rcases Nat.lt_or_eq_of_le h with hle | heq
    · have hne : ∀ p ∈ saveBlock st r n, p.1 ≠ q := by
        intro p hp he
        obtain ⟨hreg, hoff⟩ := saveBlock_bounds st r n p hp
        have hle16 : ((16 * (k + 1) : Nat) : Int) ≤ ((16 * n : Nat) : Int) := by
          exact_mod_cast Nat.mul_le_mul_left 16 (by omega)
        have hpq : p.1.off = q.off := congrArg Addr.off he
        omega
      rw [lookup_app_right _ (saveBlock st r n) _ hne]
      exact lookup_saveLog_from st r tail q n k (by omega) hq0 hq1
    · rw [show k + 1 = n + 1 from by omega, saveLog_succ]

/-- The prefix of a read is either below or far above it. -/
def Outside (r : Addr Int) (w : Int) (L : CLog) : Prop :=
  ∀ p ∈ L, p.1.off < r.off ∨ r.off + w ≤ p.1.off ∨ p.1.region ≠ r.region

/-- A query inside `[a, a + 16)` does not alias a log outside that range. -/
theorem ne_of_outside (a q : Addr Int) (L : CLog) (hL : Outside a 16 L)
    (hq0 : a.off ≤ q.off) (hq1 : q.off < a.off + 16) (hqr : q.region = a.region) :
    ∀ p ∈ L, p.1 ≠ q := by
  intro p hp he
  have hoff : p.1.off = q.off := congrArg Addr.off he
  have hreg : p.1.region = q.region := congrArg Addr.region he
  rcases hL p hp with h | h | h
  · omega
  · omega
  · exact h (by rw [hqr] at hreg; exact hreg)

theorem query_bounds (a : Addr Int) (j b : Nat) (hj4 : j < 4) (hb : b < 4) :
    a.off ≤ ((laneAddr a j).plusI ((b : Nat) : Int)).off
      ∧ ((laneAddr a j).plusI ((b : Nat) : Int)).off < a.off + 16
      ∧ ((laneAddr a j).plusI ((b : Nat) : Int)).region = a.region := by
  have hoff : ((laneAddr a j).plusI ((b : Nat) : Int)).off
      = a.off + ((4 * j : Nat) : Int) + (b : Int) := by
    rw [plusI_off, laneAddr_off]
  have hreg : ((laneAddr a j).plusI ((b : Nat) : Int)).region = a.region := by
    rw [plusI_region, laneAddr_region]
  have hj0 : ((4 * j : Nat) : Int) ≥ 0 := Int.natCast_nonneg _
  have hj16 : ((4 * j : Nat) : Int) < 16 := by
    have hm : ((4 * j : Nat) : Int) = 4 * (j : Int) := by rw [Int.natCast_mul]; rfl
    rw [hm]
    have : (j : Int) < 4 := by exact_mod_cast hj4
    omega
  have hb4 : (b : Int) < 4 := by exact_mod_cast hb
  have hb0 : (b : Int) ≥ 0 := Int.natCast_nonneg _
  refine ⟨?_, ?_, hreg⟩ <;> omega

/-- Read a cell of a lane through an ignored prefix and suffix. -/
theorem readCell_laneLog_pre2 (mem0 : Addr Int → Cell W32 Int) (t : State W32 Int)
    (P S : CLog) (a : Addr Int) (xs : List W32) (hmem : t.mem = P ++ (laneLog a xs ++ S))
    (hP : Outside a 16 P) (j b : Nat) (hj : j < xs.length) (hj4 : j < 4) (hb : b < 4) :
    readCell mem0 t ((laneAddr a j).plusI ((b : Nat) : Int))
      = .ok (.dat (xs.getD j (Lane.const 0)) b) := by
  have hq := query_bounds a j b hj4 hb
  simp only [readCell, hmem, List.append_assoc]
  rw [lookup_app_right _ P _ (ne_of_outside a _ P hP hq.1 hq.2.1 hq.2.2)]
  rw [lookup_app_left _ _ _ _ (lookup_laneLog_lane a xs j b hj hb)]

theorem loadLane_pre (mem0 : Addr Int → Cell W32 Int) (t : State W32 Int) (P S : CLog)
    (a : Addr Int) (xs : List W32) (hmem : t.mem = P ++ (laneLog a xs ++ S))
    (hP : Outside a 16 P) (j : Nat) (hj : j < xs.length) (hj4 : j < 4) :
    loadLane mem0 t (laneAddr a j) = .ok (xs.getD j (Lane.const 0)) := by
  apply loadLane_dat (x := xs.getD j (Lane.const 0))
  · have h := readCell_laneLog_pre2 mem0 t P S a xs hmem hP j 0 hj hj4 (by decide)
    rwa [show (laneAddr a j).plusI ((0 : Nat) : Int) = laneAddr a j from plusI_zero _] at h
  · exact readCell_laneLog_pre2 mem0 t P S a xs hmem hP j 1 hj hj4 (by decide)
  · exact readCell_laneLog_pre2 mem0 t P S a xs hmem hP j 2 hj hj4 (by decide)
  · exact readCell_laneLog_pre2 mem0 t P S a xs hmem hP j 3 hj hj4 (by decide)

theorem loadLanes_pre (mem0 : Addr Int → Cell W32 Int) (t : State W32 Int) (P S : CLog)
    (a : Addr Int) (xs : List W32) (hmem : t.mem = P ++ (laneLog a xs ++ S))
    (hP : Outside a 16 P) :
    ∀ (n j : Nat), j + n ≤ xs.length → j + n ≤ 4 →
      loadLanes mem0 t (laneAddr a j) n = .ok ((xs.drop j).take n) := by
  intro n
  induction n with
  | zero => intro j _ _; rfl
  | succ n ih =>
    intro j hn hn4
    have hj : j < xs.length := by omega
    have hj4 : j < 4 := by omega
    simp only [loadLanes, loadLane_pre mem0 t P S a xs hmem hP j hj hj4]
    rw [show (laneAddr a j).plusI 4 = laneAddr a (j + 1) from rfl]
    rw [Hashtree.Asm.X86.bind_ok_eq]
    rw [ih (j + 1) (by omega) (by omega)]
    rw [Hashtree.Asm.X86.bind_ok_eq]
    congr 1
    rw [List.drop_eq_getElem_cons hj]
    rw [show (xs[j] :: xs.drop (j + 1)).take (n + 1) = xs[j] :: (xs.drop (j + 1)).take n from by
      rw [List.take_succ_cons]]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl

/-- The readback of one prologue save slot from the stack. -/
theorem loadLanes_save (mem0 : Addr Int → Cell W32 Int) (st : State W32 Int) (r : Addr Int)
    (tail W : CLog) (t : State W32 Int) (hW : Outside r 160 W)
    (hmem : t.mem = W ++ saveLog st r 10 tail) (k : Nat) (hk : k < 10)
    (hvlen : 4 ≤ (st.getV (6 + k)).length) :
    loadLanes mem0 t (r.plusI ((16 * k : Nat) : Int)) 4 = .ok ((st.getV (6 + k)).take 4) := by
  obtain ⟨P, hP, hPb⟩ := saveLog_above st r tail 10 k hk
  have hmem' : t.mem = (W ++ P) ++ (saveBlock st r k ++ saveLog st r k tail) := by
    rw [hmem, hP, List.append_assoc]
  have hout : Outside (r.plusI ((16 * k : Nat) : Int)) 16 (W ++ P) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · -- an entry of the outside prefix
      have ha : (r.plusI ((16 * k : Nat) : Int)).off = r.off + ((16 * k : Nat) : Int) := plusI_off _ _
      have har : (r.plusI ((16 * k : Nat) : Int)).region = r.region := plusI_region _ _
      rcases hW p hp with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by rw [har]; exact h))
    · have hb := hPb p hp
      refine Or.inr (Or.inl ?_)
      have h16 : ((16 * (k + 1) : Nat) : Int) = ((16 * k : Nat) : Int) + 16 := by
        rw [show 16 * (k + 1) = 16 * k + 16 from by omega, Int.natCast_add]
        rfl
      have haoff : (r.plusI ((16 * k : Nat) : Int)).off = r.off + ((16 * k : Nat) : Int) :=
        plusI_off _ _
      omega
  have hlen : ((st.getV (6 + k)).take 4).length = 4 := by
    rw [getV_take4_length]
    rw [show (st.getV (6 + k)).length = (st.getV (6 + k)).length from rfl]
    omega
  have h := loadLanes_pre mem0 t (W ++ P) (saveLog st r k tail)
    (r.plusI ((16 * k : Nat) : Int)) ((st.getV (6 + k)).take 4) hmem' hout 4 0 (by omega) (by omega)
  have ht : List.take 4 (List.take 4 (st.getV (6 + k))) = List.take 4 (st.getV (6 + k)) := by
    simp only [List.take_take, Nat.min_self]
  rwa [laneAddr_zero, List.drop_zero, ht] at h

/-- `(16 * k : Int)` and `((16 * k : Nat) : Int)` are the same displacement. -/
theorem disp16 (k : Nat) : (16 * (k : Int)) = ((16 * k : Nat) : Int) := by
  rw [Int.natCast_mul]
  rfl

/-- The vector read of one prologue save slot from the stack. -/
theorem readVSrc_save (ro : Region) (mem0 : Addr Int → Cell W32 Int)
    (st : State W32 Int) (r : Addr Int) (tail W : CLog) (t : State W32 Int)
    (hW : Outside r 160 W) (hmem : t.mem = W ++ saveLog st r 10 tail)
    (h4 : t.getG rsp = .ptr r) (k : Nat) (hk : k < 10)
    (hvlen : 4 ≤ (st.getV (6 + k)).length) :
    readVSrc ro mem0 t 4 (.mem { base := some rsp, disp := (16 * (k : Int)) })
      = .ok ((st.getV (6 + k)).take 4) := by
  have he : effAddr ro t ({ base := some rsp, disp := (16 * (k : Int)) } : MemRef)
      = .ok (r.plusI ((16 * k : Nat) : Int)) := by
    simp only [effAddr, baseAddr, regPtr, h4, disp16]
  simp only [readVSrc, he, Hashtree.Asm.X86.bind_ok_eq]
  exact loadLanes_save mem0 st r tail W t hW hmem k hk hvlen

/-! ## `setVec` and the state projections -/

/-- `next` leaves the vector registers alone. -/
theorem getV_next (s : State W32 Int) (j : Nat) : s.next.getV j = s.getV j := rfl

/-- Writing a vector register: the written register keeps its high lanes, the low four are the
read value. -/
theorem getV_setVec_self (s : State W32 Int) (d : Nat) (v : List W32)
    (hd : d < s.vr.length) :
    (setVec s false 4 d v).getV d = v.take 4 ++ (s.getV d).drop 4 := by
  simp only [setVec, State.setV, State.getV]
  exact getD_set_self _ _ hd _ _

/-- Writing a vector register: every other register is unchanged. -/
theorem getV_setVec_ne (s : State W32 Int) (d j : Nat) (v : List W32) (h : j ≠ d) :
    (setVec s false 4 d v).getV j = s.getV j := by
  simp only [setVec, State.setV, State.getV]
  exact getD_set_ne _ _ _ (Ne.symm h) _ _

/-! ## The epilogue instructions and their `exec` formulas -/

/-- The `k`-th restore of the epilogue: `vload 4 xmm{6+k}, [rsp + 16k]`. -/
def epiStep (k : Nat) : Instr :=
  .vload false 4 (6 + k) (.mem { base := some rsp, disp := (16 * (k : Int)) })

/-- Kernel-checked: the ten restores are at pcs 679 … 688 (`WinShani.shani_epilogue_restores`). -/
theorem epi_lookup (k : Nat) (hk : k < 10) : winProg[679 + k]? = some (epiStep k) := by
  have h := List.all_eq_true.mp Hashtree.Proofs.WinShani.shani_epilogue_restores k
    (List.mem_range.mpr hk)
  exact of_decide_eq_true h

/-- The stack-pointer restore at pc 689 (`WinShani.shani_rsp_balanced`). -/
theorem epi_add_lookup : winProg[689]? = some (.alu .add 64 rsp (.imm 248)) :=
  Hashtree.Proofs.WinShani.shani_rsp_balanced.2.1

/-- The `ret` at pc 690. -/
theorem epi_ret_lookup : winProg[690]? = some .ret := by decide +kernel

/-- `add rsp, 248` on a state whose `rsp` holds `a`: `rsp` becomes `a + 248`, the flags record
the addition, and the pc advances. -/
theorem exec_add64_rsp {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (s : State W32 Int) (a : Addr Int) (hh : s.halted = false) (h4 : s.getG rsp = .ptr a) :
    exec ro mem0 orc (.alu .add 64 rsp (.imm 248)) s
      = { s with
          gpr := s.gpr.set rsp (.ptr (a.plusI 248)),
          flags := some ((a.plusI 248).off, Ctl.ofInt 0),
          pc := s.pc + 1 } := by
  have hg : gCtl s (.reg rsp) = .ok a := gCtl_reg_ptr s rsp a h4
  have hi : gCtl s (.imm 248) = .ok (⟨rNum, Ctl.ofInt 248⟩ : Addr Int) := gCtl_imm s 248
  simp only [exec, hh, Bool.false_eq_true, ite_false, hg, Hashtree.Asm.X86.bind_ok_eq, hi]
  rw [ite_eq_left trivial]
  rw [ite_eq_right (by decide : ¬(LOp.add = LOp.xor ∧ GSrc.imm 248 = GSrc.reg rsp))]
  rw [ite_eq_left (Or.inl trivial)]
  rw [Hashtree.Proofs.WinShaniFront.okOr_pure]
  simp only [State.next, State.setG, setFlags]
  rw [hh]
  rfl

/-- `ret` on a state whose `rsp` holds `a`, where the eight bytes at `a` give the return
pointer: the machine halts with `rsp` popped past the return address. -/
theorem exec_ret_ok {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (s : State W32 Int) (a : Addr Int) (o : Int)
    (hh : s.halted = false) (h4 : s.getG rsp = .ptr a)
    (hv : loadVal mem0 s a = .ok (.ptr (⟨rRet, Ctl.ofInt o⟩ : Addr Int))) :
    exec ro mem0 orc .ret s = halt (s.setG rsp (.ptr (a.plusI 8))) := by
  simp only [exec, hh, Bool.false_eq_true, ite_false, h4, hv, rRet,
    Hashtree.Asm.X86.bind_ok_eq, Hashtree.Proofs.WinShaniFront.okOr_pure]

/-! ## `loadVal` depends only on the write log -/

theorem readCell_mem_eq {mem0 : Addr Int → Cell W32 Int} {s t : State W32 Int}
    (h : t.mem = s.mem) (a : Addr Int) : readCell mem0 t a = readCell mem0 s a := by
  simp only [readCell, h]

theorem pbRest_mem_eq {mem0 : Addr Int → Cell W32 Int} {s t : State W32 Int}
    (h : t.mem = s.mem) (p a : Addr Int) :
    ∀ n k, pbRest mem0 t p a n k = pbRest mem0 s p a n k := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    simp only [pbRest, readCell_mem_eq h, ih]

theorem loadLane_mem_eq {mem0 : Addr Int → Cell W32 Int} {s t : State W32 Int}
    (h : t.mem = s.mem) (a : Addr Int) : loadLane mem0 t a = loadLane mem0 s a := by
  simp only [loadLane, readCell_mem_eq h]

/-- `loadVal` reads only through the write log. -/
theorem loadVal_mem_eq {mem0 : Addr Int → Cell W32 Int} {s t : State W32 Int}
    (h : t.mem = s.mem) (a : Addr Int) : loadVal mem0 t a = loadVal mem0 s a := by
  simp only [loadVal, readCell_mem_eq h, pbRest_mem_eq h, loadLane_mem_eq h]

/-! ## The restored registers after `k` steps -/

/-- The state after the first `k` restores: `k` successive `setVec` of the low four lanes. -/
def epiSt (s st : State W32 Int) : Nat → State W32 Int
  | 0 => s
  | k + 1 => (setVec (epiSt s st k) false 4 (6 + k) ((st.getV (6 + k)).take 4)).next

theorem epiSt_succ (s st : State W32 Int) (k : Nat) :
    epiSt s st (k + 1) =
      (setVec (epiSt s st k) false 4 (6 + k) ((st.getV (6 + k)).take 4)).next := rfl

theorem epiSt_mem (s st : State W32 Int) (k : Nat) : (epiSt s st k).mem = s.mem := by
  induction k with
  | zero => rfl
  | succ k ih => rw [epiSt_succ]; exact ih

theorem epiSt_halted (s st : State W32 Int) (k : Nat) :
    (epiSt s st k).halted = s.halted := by
  induction k with
  | zero => rfl
  | succ k ih => rw [epiSt_succ]; exact ih

theorem epiSt_pc (s st : State W32 Int) (k : Nat) : (epiSt s st k).pc = s.pc + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [epiSt_succ]
    show (setVec (epiSt s st k) false 4 (6 + k) ((st.getV (6 + k)).take 4)).pc + 1
      = s.pc + (k + 1)
    rw [show (setVec (epiSt s st k) false 4 (6 + k) ((st.getV (6 + k)).take 4)).pc
      = (epiSt s st k).pc from rfl, ih]
    omega

theorem epiSt_getG (s st : State W32 Int) (k j : Nat) :
    (epiSt s st k).getG j = s.getG j := by
  induction k with
  | zero => rfl
  | succ k ih => rw [epiSt_succ]; exact ih

theorem epiSt_vr_len (s st : State W32 Int) (k : Nat) :
    (epiSt s st k).vr.length = s.vr.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [epiSt_succ]
    simp only [setVec, State.setV, State.next, List.length_set]
    exact ih

theorem epiSt_gpr_len (s st : State W32 Int) (k : Nat) :
    (epiSt s st k).gpr.length = s.gpr.length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [epiSt_succ]; exact ih

/-- A register not yet restored still holds what it held at the start. -/
theorem epiSt_getV_ne (s st : State W32 Int) (k d : Nat)
    (hd : ∀ l, l < k → d ≠ 6 + l) : (epiSt s st k).getV d = s.getV d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [epiSt_succ, getV_next, getV_setVec_ne _ _ _ _ (hd k (by omega))]
    exact ih (fun l hl => hd l (by omega))

/-- The register restored at slot `j` (`j < k`): low four lanes from the saved state, high lanes
as they were. -/
theorem epiSt_getV_after (s st : State W32 Int) (j : Nat) (hvr : 16 ≤ s.vr.length) :
    ∀ k, k ≤ 10 → j < k →
      (epiSt s st k).getV (6 + j) =
        (st.getV (6 + j)).take 4 ++ (s.getV (6 + j)).drop 4 := by
  intro k
  induction k with
  | zero => intro _ hj; omega
  | succ k ih =>
    intro hk hj
    rw [epiSt_succ]
    by_cases hjk : j = k
    · rw [hjk]
      rw [getV_next, getV_setVec_self _ _ _ (by rw [epiSt_vr_len]; omega)]
      rw [epiSt_getV_ne s st k (6 + k) (by intro l hl; omega)]
      simp only [List.take_take, Nat.min_self]
    · rw [getV_next, getV_setVec_ne _ _ _ _ (by omega)]
      exact ih (by omega) (by omega)

/-! ## The epilogue replay -/

/-- `run` of one step at a known instruction. -/
theorem run_one {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (s : State W32 Int) (i : Instr) (hh : s.halted = false)
    (hp : winProg[s.pc]? = some i) :
    run winProg ro mem0 orc 1 s = exec ro mem0 orc i s := by
  simp only [run, hh, Bool.false_eq_true, ite_false, hp]

/-- `k` restores of the epilogue, `k ≤ 10`. -/
theorem run_epi {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (t0 st : State W32 Int) (r : Addr Int) (tail W : CLog)
    (hh : t0.halted = false) (hpc : t0.pc = 679) (hrsp : t0.getG rsp = .ptr r)
    (hW : Outside r 160 W) (hmem : t0.mem = W ++ saveLog st r 10 tail)
    (hvlen : ∀ k, k < 10 → 4 ≤ (st.getV (6 + k)).length) :
    ∀ k, k ≤ 10 → run winProg ro mem0 orc k t0 = epiSt t0 st k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk10
    have hk : k < 10 := by omega
    have hh' : (epiSt t0 st k).halted = false := by rw [epiSt_halted, hh]
    have hpc' : (epiSt t0 st k).pc = 679 + k := by rw [epiSt_pc, hpc]
    have hrsp' : (epiSt t0 st k).getG rsp = .ptr r := by rw [epiSt_getG]; exact hrsp
    have hmem' : (epiSt t0 st k).mem = W ++ saveLog st r 10 tail := by
      rw [epiSt_mem]; exact hmem
    have hv : readVSrc ro mem0 (epiSt t0 st k) 4
        (.mem { base := some rsp, disp := (16 * (k : Int)) })
        = .ok ((st.getV (6 + k)).take 4) :=
      readVSrc_save ro mem0 st r tail W (epiSt t0 st k) hW hmem' hrsp' k hk (hvlen k hk)
    have hev : exec ro mem0 orc (epiStep k) (epiSt t0 st k) = epiSt t0 st (k + 1) := by
      rw [epiStep]
      rw [Hashtree.Proofs.WinShaniFlags.exec_vload_ok (epiSt t0 st k) false 4 (6 + k) _ _
        hh' hv]
      rfl
    rw [run_add winProg ro mem0 orc k 1, ih (by omega)]
    rw [show (1 : Nat) = 0 + 1 from rfl]
    rw [run_succ_step winProg ro mem0 orc 0 (epiSt t0 st k) (epiStep k) hh'
      (by rw [hpc']; exact epi_lookup k hk)]
    rw [hev]
    rfl

/-- The state after the whole epilogue: the vector registers as restored by the ten `vload`s,
`rsp` popped past the return address, the flags of `add rsp, 248`, the pc after the `ret`, and
the machine halted. -/
def epiFinal (t0 st : State W32 Int) (r : Addr Int) : State W32 Int :=
  halt { (epiSt t0 st 10) with
    gpr := (epiSt t0 st 10).gpr.set rsp (.ptr (r.plusI 256)),
    flags := some ((r.plusI 248).off, Ctl.ofInt 0),
    pc := (epiSt t0 st 10).pc + 1 }

/-- **The `shani_x2` epilogue.**  Twelve instructions carry the body-exit state `t0` (pc 679,
`rsp = r`, save log in memory) to the halted `epiFinal` state, provided the eight bytes at
`rsp + 248` are the return pointer. -/
theorem run_epilogue {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (t0 st : State W32 Int) (r : Addr Int) (tail W : CLog)
    (hh : t0.halted = false) (hpc : t0.pc = 679) (hrsp : t0.getG rsp = .ptr r)
    (hW : Outside r 160 W) (hmem : t0.mem = W ++ saveLog st r 10 tail)
    (hgr : 5 ≤ t0.gpr.length)
    (hvlen : ∀ k, k < 10 → 4 ≤ (st.getV (6 + k)).length)
    (hret : loadVal mem0 t0 (r.plusI 248) = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int))) :
    run winProg ro mem0 orc 12 t0 = epiFinal t0 st r := by
  rw [show (12 : Nat) = 10 + 2 from rfl]
  rw [run_add winProg ro mem0 orc 10 2]
  rw [run_epi t0 st r tail W hh hpc hrsp hW hmem hvlen 10 (by omega)]
  have hh10 : (epiSt t0 st 10).halted = false := by rw [epiSt_halted, hh]
  have hpc10 : (epiSt t0 st 10).pc = 689 := by rw [epiSt_pc, hpc]
  have hrsp10 : (epiSt t0 st 10).getG rsp = .ptr r := by rw [epiSt_getG]; exact hrsp
  rw [show (2 : Nat) = 1 + 1 from rfl]
  rw [run_succ_step winProg ro mem0 orc 1 (epiSt t0 st 10) (.alu .add 64 rsp (.imm 248))
    hh10 (by rw [hpc10]; exact epi_add_lookup)]
  rw [exec_add64_rsp (epiSt t0 st 10) r hh10 hrsp10]
  -- the state after `add rsp, 248`
  let A : State W32 Int := { (epiSt t0 st 10) with
    gpr := (epiSt t0 st 10).gpr.set rsp (.ptr (r.plusI 248)),
    flags := some ((r.plusI 248).off, Ctl.ofInt 0),
    pc := (epiSt t0 st 10).pc + 1 }
  have hhA : A.halted = false := hh10
  have hpcA : A.pc = 690 := by
    show (epiSt t0 st 10).pc + 1 = 690; omega
  have hrspA : A.getG rsp = .ptr (r.plusI 248) := by
    show ((epiSt t0 st 10).gpr.set rsp (.ptr (r.plusI 248))).getD rsp _ = _
    rw [getD_set_self _ _ (by rw [epiSt_gpr_len, show rsp = 4 from rfl]; omega)]
  have hretA : loadVal mem0 A (r.plusI 248) = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int)) := by
    rw [loadVal_mem_eq (s := t0) (t := A)
      (by show A.mem = t0.mem
          rw [show A.mem = (epiSt t0 st 10).mem from rfl, epiSt_mem])]
    exact hret
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [run_succ_step winProg ro mem0 orc 0 A .ret hhA (by rw [hpcA]; exact epi_ret_lookup)]
  rw [exec_ret_ok A (r.plusI 248) 0 hhA hrspA hretA]
  -- identify the final halted state
  show halt (A.setG rsp (.ptr ((r.plusI 248).plusI 8))) = epiFinal t0 st r
  unfold epiFinal
  congr 1
  have hgpr : A.gpr.set rsp (.ptr ((r.plusI 248).plusI 8))
      = (epiSt t0 st 10).gpr.set rsp (.ptr (r.plusI 256)) := by
    show ((epiSt t0 st 10).gpr.set rsp (.ptr (r.plusI 248))).set rsp
      (.ptr ((r.plusI 248).plusI 8)) = _
    rw [List.set_set, plusI_add]
    rfl
  show { A with gpr := A.gpr.set rsp (.ptr ((r.plusI 248).plusI 8)) } = _
  rw [hgpr]

/-- Taking four lanes of a four-lane list returns the list. -/
theorem take_four_append (a b : List W32) (ha : a.length = 4) : (a ++ b).take 4 = a := by
  rw [← ha]
  exact List.take_left

/-- The halted state after the epilogue. -/
theorem epiFinal_halted (t0 st : State W32 Int) (r : Addr Int) :
    (epiFinal t0 st r).halted = true := rfl

/-- The epilogue restores the stack pointer: it points just past the return address. -/
theorem epiFinal_getG_rsp (t0 st : State W32 Int) (r : Addr Int)
    (hgr : 5 ≤ t0.gpr.length) :
    (epiFinal t0 st r).getG rsp = .ptr (r.plusI 256) := by
  show ((epiSt t0 st 10).gpr.set rsp (.ptr (r.plusI 256))).getD rsp _ = _
  rw [getD_set_self _ _ (by rw [epiSt_gpr_len, show rsp = 4 from rfl]; omega)]

/-- The epilogue leaves every other general register alone. -/
theorem epiFinal_getG_ne (t0 st : State W32 Int) (r : Addr Int) (j : Nat) (hj : j ≠ rsp) :
    (epiFinal t0 st r).getG j = t0.getG j := by
  show ((epiSt t0 st 10).gpr.set rsp (.ptr (r.plusI 256))).getD j _ = t0.gpr.getD j _
  rw [getD_set_ne _ _ _ (Ne.symm hj)]
  exact epiSt_getG t0 st 10 j

/-- The epilogue leaves the write log alone. -/
theorem epiFinal_mem (t0 st : State W32 Int) (r : Addr Int) :
    (epiFinal t0 st r).mem = t0.mem := epiSt_mem t0 st 10

/-- **The ten callee-saved vector registers come back.**  After the epilogue, the low four lanes
of `xmm6`-`xmm15` are the lanes the prologue saved. -/
theorem run_epilogue_getV {ro : Region} {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (t0 st : State W32 Int) (r : Addr Int) (tail W : CLog)
    (hh : t0.halted = false) (hpc : t0.pc = 679) (hrsp : t0.getG rsp = .ptr r)
    (hW : Outside r 160 W) (hmem : t0.mem = W ++ saveLog st r 10 tail)
    (hvr : 16 ≤ t0.vr.length) (hgr : 5 ≤ t0.gpr.length)
    (hvlen : ∀ k, k < 10 → 4 ≤ (st.getV (6 + k)).length)
    (hret : loadVal mem0 t0 (r.plusI 248) = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int)))
    (j : Nat) (hj : j < 10) :
    ((run winProg ro mem0 orc 12 t0).getV (6 + j)).take 4
      = (st.getV (6 + j)).take 4 := by
  rw [run_epilogue t0 st r tail W hh hpc hrsp hW hmem hgr hvlen hret]
  show ((epiSt t0 st 10).getV (6 + j)).take 4 = _
  rw [epiSt_getV_after t0 st j hvr 10 (by omega) hj]
  refine take_four_append _ _ ?_
  rw [getV_take4_length]
  have := hvlen j hj
  omega

end Hashtree.Proofs.WinShaniEpi
