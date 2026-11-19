import Hashtree.Asm.RunAgreeM
import Hashtree.Asm.X86Loop
import Hashtree.Asm.Hom

/-!
# Concrete memory cells: what a store leaves untouched, and what it reads back

For the concrete machine (`Int` addresses, `W32` lanes): the cells `Cells a n` = `[a, a + n)` in
`a`'s region; a `storeLane`/`storeLanes`/`storeVal` changes the lookups only inside its cells
(`lookup_storeVal_untouched` …), and the eight cells written by `storeVal s a v` read back as `v`
(`loadVal_storeVal`).  With `RunAgreeM.loadVal_memAg` this gives: a 64-bit value at `b` survives
any store disjoint from `Cells b 8`.
-/

set_option autoImplicit false

namespace Hashtree.Asm.MemCells

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.RunAgreeM

abbrev CMem := List (Addr Int × Cell W32 Int)

/-- The cells `[a, a + n)` of `a`'s region. -/
def Cells (a : Addr Int) (n : Nat) (x : Addr Int) : Prop :=
  x.region = a.region ∧ a.off ≤ x.off ∧ x.off < a.off + n

theorem plusI_int (a : Addr Int) (k : Int) : a.plusI k = ⟨a.region, a.off + k⟩ := rfl

theorem same_int (a b : Addr Int) : AddrEq.same a b = some (a.region == b.region && a.off == b.off) := rfl

theorem lookup_cons_ne (a b : Addr Int) (c : Cell W32 Int) (m : CMem) (hne : a ≠ b) :
    lookup a ((b, c) :: m) = lookup a m := by
  have hb : (a.region == b.region && a.off == b.off) = false := by
    cases hr : (a.region == b.region) with
    | false => rfl
    | true =>
      cases ho : (a.off == b.off) with
      | false => rfl
      | true =>
        exfalso; apply hne
        obtain ⟨ra, oa⟩ := a
        obtain ⟨rb, ob⟩ := b
        simp only [beq_iff_eq] at hr ho
        simp [hr, ho]
  simp only [lookup, same_int, hb]

theorem lookup_cons_self (a : Addr Int) (c : Cell W32 Int) (m : CMem) : lookup a ((a, c) :: m) = .ok (some c) := by
  simp only [lookup, same_int, beq_self_eq_true, Bool.and_self]

theorem not_cells_ne {a x : Addr Int} {n : Nat} (h : ¬ Cells a n x) (k : Int) (hk0 : 0 ≤ k) (hkn : k < n) :
    x ≠ a.plusI k := by
  intro he
  apply h
  rw [he, plusI_int]
  exact ⟨rfl, by dsimp only; omega, by dsimp only; omega⟩

theorem lookup_storeLane_untouched (s : State W32 Int) (a : Addr Int) (v : W32) (x : Addr Int)
    (hx : ¬ Cells a 4 x) : lookup x (storeLane s a v).mem = lookup x s.mem := by
  simp only [storeLane]
  rw [lookup_cons_ne _ _ _ _ (not_cells_ne hx 3 (by omega) (by omega)),
    lookup_cons_ne _ _ _ _ (not_cells_ne hx 2 (by omega) (by omega)),
    lookup_cons_ne _ _ _ _ (not_cells_ne hx 1 (by omega) (by omega)),
    lookup_cons_ne _ _ _ _ (by
      intro he; apply hx; rw [he]; exact ⟨rfl, Int.le_refl _, by omega⟩)]

theorem lookup_storeLanes_untouched (s : State W32 Int) (a : Addr Int) (xs : List W32) (x : Addr Int)
    (hx : ¬ Cells a (4 * xs.length) x) : lookup x (storeLanes s a xs).mem = lookup x s.mem := by
  induction xs generalizing s a with
  | nil => rfl
  | cons y ys ih =>
    simp only [storeLanes]
    rw [ih _ _ (by
      intro hc; apply hx
      obtain ⟨h1, h2, h3⟩ := hc
      rw [plusI_int] at h1 h2 h3
      exact ⟨h1, by simp at h2 ⊢; omega, by simp [List.length_cons] at h3 ⊢; omega⟩)]
    exact lookup_storeLane_untouched s a y x (by
      intro hc; apply hx
      obtain ⟨h1, h2, h3⟩ := hc
      exact ⟨h1, h2, by simp [List.length_cons]; omega⟩)

theorem lookup_storeVal_untouched (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) (x : Addr Int)
    (hx : ¬ Cells a 8 x) : lookup x (storeVal s a v).mem = lookup x s.mem := by
  cases v with
  | num lo hi =>
    simp only [storeVal]
    rw [lookup_storeLane_untouched _ _ _ _ (by
        intro hc; apply hx
        obtain ⟨h1, h2, h3⟩ := hc
        rw [plusI_int] at h1 h2 h3
        exact ⟨h1, by simp at h2 ⊢; omega, by simp at h3 ⊢; omega⟩),
      lookup_storeLane_untouched _ _ _ _ (by
        intro hc; apply hx
        obtain ⟨h1, h2, h3⟩ := hc
        exact ⟨h1, h2, by omega⟩)]
  | ptr p =>
    simp only [storeVal]
    apply Hashtree.Asm.X86.lookup_app_right
    intro q hq
    simp only [List.mem_map, List.mem_reverse, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact (not_cells_ne hx i (by omega) (by omega)).symm

theorem reassemble (x : W32) :
    (byteOf x 0 ||| byteOf x 1 <<< 8 ||| (byteOf x 2 <<< 16 ||| byteOf x 3 <<< 24)) = x :=
  bytes_reassemble x

theorem same_w32 (x y : W32) : Lane.same x y = false := rfl

/-- The four cells of a stored lane. -/
theorem lookup_storeLane_cells (t : State W32 Int) (b : Addr Int) (y : W32) :
    lookup b (storeLane t b y).mem = .ok (some (.dat y 0)) ∧
    lookup (b.plusI 1) (storeLane t b y).mem = .ok (some (.dat y 1)) ∧
    lookup (b.plusI 2) (storeLane t b y).mem = .ok (some (.dat y 2)) ∧
    lookup (b.plusI 3) (storeLane t b y).mem = .ok (some (.dat y 3)) := by
  have n01 : b ≠ b.plusI 1 := by rw [plusI_int]; obtain ⟨r, o⟩ := b; simp; omega
  have n02 : b ≠ b.plusI 2 := by rw [plusI_int]; obtain ⟨r, o⟩ := b; simp; omega
  have n03 : b ≠ b.plusI 3 := by rw [plusI_int]; obtain ⟨r, o⟩ := b; simp; omega
  have n12 : b.plusI 1 ≠ b.plusI 2 := by rw [plusI_int, plusI_int]; simp
  have n13 : b.plusI 1 ≠ b.plusI 3 := by rw [plusI_int, plusI_int]; simp
  have n23 : b.plusI 2 ≠ b.plusI 3 := by rw [plusI_int, plusI_int]; simp
  simp only [storeLane]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lookup_cons_ne _ _ _ _ n03, lookup_cons_ne _ _ _ _ n02, lookup_cons_ne _ _ _ _ n01, lookup_cons_self]
  · rw [lookup_cons_ne _ _ _ _ n13, lookup_cons_ne _ _ _ _ n12, lookup_cons_self]
  · rw [lookup_cons_ne _ _ _ _ n23, lookup_cons_self]
  · rw [lookup_cons_self]

theorem beq_add_right (o j k : Int) : (o + j == o + k) = (j == k) := by
  cases hb : (j == k) with
  | true => simp only [beq_iff_eq] at hb; subst hb; simp
  | false => simp only [beq_eq_false_iff_ne, ne_eq] at hb ⊢; omega

theorem beq_self_add (o k : Int) : (o == o + k) = (0 == k) := by
  cases hb : ((0 : Int) == k) with
  | true => simp only [beq_iff_eq] at hb; subst hb; simp
  | false => simp only [beq_eq_false_iff_ne, ne_eq] at hb ⊢; omega

/-- Eight cells holding the bytes of pointer `p` load as `p` (as `WrapperPre.loadVal_ptr`). -/
theorem loadVal_ptr (m : Addr Int → Cell W32 Int) (s : State W32 Int) (a p : Addr Int)
    (h : ∀ k : Nat, k < 8 → readCell m s (a.plusI k) = .ok (.pb p k)) : loadVal m s a = .ok (.ptr p) := by
  have h0 : readCell m s a = .ok (.pb p 0) := by
    have := h 0 (by decide)
    have e : a.plusI ((0 : Nat) : Int) = a := by
      obtain ⟨r, o⟩ := a; simp [Addr.plusI, Addr.plus, Ctl.add, Ctl.ofInt]
    rwa [e] at this
  have hs : AddrEq.same p p = some true := by simp [AddrEq.same]
  simp only [loadVal, h0, bind, Except.bind]
  simp only [pbRest, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), isPb, hs, bind, Except.bind, pure, Except.pure]
  rfl

/-- The eight cells of a stored 64-bit value read back as the value. -/
theorem loadVal_storeVal (mem0 : Addr Int → Cell W32 Int) (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) :
    loadVal mem0 (storeVal s a v) a = .ok v := by
  cases v with
  | num lo hi =>
    simp only [storeVal]
    have hout : ∀ x, ¬ Cells (a.plusI 4) 4 x →
        lookup x (storeLane (storeLane s a lo) (a.plusI 4) hi).mem = lookup x (storeLane s a lo).mem :=
      fun x hx => lookup_storeLane_untouched _ _ _ _ hx
    have nc : ∀ k : Int, k < 4 → ¬ Cells (a.plusI 4) 4 (a.plusI k) := by
      intro k hk h
      obtain ⟨_, h2, _⟩ := h
      rw [plusI_int, plusI_int] at h2
      dsimp only at h2; omega
    have nc0 : ¬ Cells (a.plusI 4) 4 a := by
      intro h; obtain ⟨_, h2, _⟩ := h; rw [plusI_int] at h2; dsimp only at h2; omega
    obtain ⟨l0, l1, l2, l3⟩ := lookup_storeLane_cells s a lo
    obtain ⟨m0, m1, m2, m3⟩ := lookup_storeLane_cells (storeLane s a lo) (a.plusI 4) hi
    have c0 : readCell mem0 (storeLane (storeLane s a lo) (a.plusI 4) hi) a = .ok (.dat lo 0) := by
      simp only [readCell, hout a nc0, l0]
    have c1 : readCell mem0 (storeLane (storeLane s a lo) (a.plusI 4) hi) (a.plusI 1) = .ok (.dat lo 1) := by
      simp only [readCell, hout _ (nc 1 (by omega)), l1]
    have c2 : readCell mem0 (storeLane (storeLane s a lo) (a.plusI 4) hi) (a.plusI 2) = .ok (.dat lo 2) := by
      simp only [readCell, hout _ (nc 2 (by omega)), l2]
    have c3 : readCell mem0 (storeLane (storeLane s a lo) (a.plusI 4) hi) (a.plusI 3) = .ok (.dat lo 3) := by
      simp only [readCell, hout _ (nc 3 (by omega)), l3]
    have c4 : readCell mem0 (storeLane (storeLane s a lo) (a.plusI 4) hi) (a.plusI 4) = .ok (.dat hi 0) := by
      simp only [readCell, m0]
    have c5 : readCell mem0 (storeLane (storeLane s a lo) (a.plusI 4) hi) ((a.plusI 4).plusI 1) = .ok (.dat hi 1) := by
      simp only [readCell, m1]
    have c6 : readCell mem0 (storeLane (storeLane s a lo) (a.plusI 4) hi) ((a.plusI 4).plusI 2) = .ok (.dat hi 2) := by
      simp only [readCell, m2]
    have c7 : readCell mem0 (storeLane (storeLane s a lo) (a.plusI 4) hi) ((a.plusI 4).plusI 3) = .ok (.dat hi 3) := by
      simp only [readCell, m3]
    simp only [loadVal, c0, bind, Except.bind, loadLane, c1, c2, c3, c4, c5, c6, c7, lanePat]
    simp [same_w32, reassemble, pure, Except.pure]
  | ptr p =>
    apply loadVal_ptr
    intro k hk
    simp only [readCell, storeVal, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, List.map, Int.ofNat_eq_natCast]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [lookup, same_int, plusI_int, beq_add_right, beq_self_add]

/-! ## The cells a store writes, as a list -/

/-- The log entries `storeVal s a v` prepends (newest first). -/
def storeCells (a : Addr Int) : Val W32 Int → CMem
  | .num lo hi => [((a.plusI 4).plusI 3, .dat hi 3), ((a.plusI 4).plusI 2, .dat hi 2), ((a.plusI 4).plusI 1, .dat hi 1),
      (a.plusI 4, .dat hi 0), (a.plusI 3, .dat lo 3), (a.plusI 2, .dat lo 2), (a.plusI 1, .dat lo 1), (a, .dat lo 0)]
  | .ptr p => (List.range 8).reverse.map (fun (i : Nat) => (a.plusI (Int.ofNat i), Cell.pb p i))

theorem storeVal_mem (s : State W32 Int) (a : Addr Int) (v : Val W32 Int) :
    (storeVal s a v).mem = storeCells a v ++ s.mem := by
  cases v with
  | num lo hi => rfl
  | ptr p => rfl

/-- The addresses a store writes do not depend on the value. -/
theorem storeCells_addrs (a : Addr Int) (v w : Val W32 Int) : (storeCells a v).map Prod.fst = (storeCells a w).map Prod.fst := by
  cases v <;> cases w <;> simp [storeCells, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, plusI_int, Int.add_assoc]

/-- Inside the written cells the lookup is the new cell, whatever the old log. -/
theorem lookup_storeCells_inside (a : Addr Int) (v : Val W32 Int) (x : Addr Int) (hx : Cells a 8 x) :
    ∃ c, lookup x (storeCells a v) = .ok (some c) := by
  obtain ⟨h1, h2, h3⟩ := hx
  obtain ⟨xr, xo⟩ := x
  obtain ⟨ar, ao⟩ := a
  simp only at h1 h2 h3
  subst h1
  have : ∃ k : Nat, k < 8 ∧ xo = ao + k := ⟨(xo - ao).toNat, by omega, by omega⟩
  obtain ⟨k, hk, rfl⟩ := this
  cases v with
  | num lo hi =>
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [storeCells, lookup, same_int, plusI_int, Int.add_assoc, beq_add_right, beq_self_add]
  | ptr p =>
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [storeCells, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, lookup, same_int,
        plusI_int, Int.add_assoc, beq_add_right, beq_self_add]

/-- Two stores of the same value at the same address agree inside the written cells. -/
theorem lookup_storeVal_inside (s s' : State W32 Int) (a : Addr Int) (v : Val W32 Int) (x : Addr Int)
    (hx : Cells a 8 x) : lookup x (storeVal s a v).mem = lookup x (storeVal s' a v).mem := by
  obtain ⟨c, hc⟩ := lookup_storeCells_inside a v x hx
  rw [storeVal_mem, storeVal_mem, Hashtree.Asm.X86.lookup_app_left _ _ _ c hc,
    Hashtree.Asm.X86.lookup_app_left _ _ _ c hc]

/-- Outside the written cells a store keeps the agreement of the old logs. -/
theorem lookup_storeVal_outside (s s' : State W32 Int) (a : Addr Int) (v : Val W32 Int) (x : Addr Int)
    (hx : ¬ Cells a 8 x) (h : lookup x s.mem = lookup x s'.mem) :
    lookup x (storeVal s a v).mem = lookup x (storeVal s' a v).mem := by
  rw [lookup_storeVal_untouched s a v x hx, lookup_storeVal_untouched s' a v x hx, h]

end Hashtree.Asm.MemCells
