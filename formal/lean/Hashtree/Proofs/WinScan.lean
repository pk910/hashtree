import Hashtree.Proofs.Win64

/-!
# R5: kernel-checked scans of the shipped instruction arrays, one chunk at a time

`decide +kernel` on a scan of a whole shipped stream (4000-odd instructions) is a single kernel
reduction of a four-thousand-element list literal.  The reducer unfolds the array once per index,
so the work grows quadratically and the intermediate terms reach tens of gigabytes (measured:
> 120 GB and no result after nine minutes for a 4243-instruction scan).  These helpers reduce a
scan one slice at a time instead: `all_take_drop` splits `l.all f` into `(l.take k).all f` and
`(l.drop k).all f`, so every `decide +kernel` step only sees one chunk of a few thousand
instructions, and the whole scan of `sse_x1` then checks in seconds.

For the body comparisons the scan is stated over a *zipped pair of list slices* rather than over
indices; `zip_slice_get` shows that the `j`-th pair is the pair of `j`-th instructions, and
`of_zip_scan` turns a zipped scan into the per-pc statement the transfer engine consumes.  This
keeps the expensive array indexing out of the kernel reduction entirely.

Everything here is proved by the kernel (`decide` / `decide +kernel`); no `native_decide` axiom is
introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinScan

/-- Split a Boolean `List.all` scan into two scans. -/
theorem all_take_drop {α} (f : α → Bool) (l : List α) (k : Nat)
    (h1 : (l.take k).all f = true) (h2 : (l.drop k).all f = true) :
    l.all f = true := by
  rw [← List.take_append_drop k l, List.all_append, h1, h2]
  rfl

/-- `(l.drop i)[j]? = l[i + j]?`. -/
theorem getElem?_drop {α} : ∀ (l : List α) (i j : Nat), (l.drop i)[j]? = l[i + j]?
  | [], _, _ => by simp
  | _ :: xs, 0, j => by simp
  | x :: xs, i + 1, j => by
      show (xs.drop i)[j]? = (x :: xs)[i + 1 + j]?
      rw [getElem?_drop xs i j]
      simp [Nat.add_right_comm]

/-- The `j`-th element of the zip of two slices is the pair of `j`-th elements of the slices. -/
theorem zip_slice_get {α β} (l1 : List α) (l2 : List β) (o1 o2 n j : Nat) (hj : j < n) :
    (((l1.drop o1).take n).zip ((l2.drop o2).take n))[j]? =
      (l1[o1 + j]?).bind (fun a => (l2[o2 + j]?).map (fun b => (a, b))) := by
  simp only [List.zip, List.getElem?_zipWith]
  rw [List.getElem?_take_of_lt hj, List.getElem?_take_of_lt hj]
  rw [getElem?_drop l1 o1 j, getElem?_drop l2 o2 j]
  cases l1[o1 + j]? <;> cases l2[o2 + j]? <;> rfl

/-- A scan over zipped slices implies the per-pc correspondence of the two lists. -/
theorem of_zip_scan {α β} [DecidableEq α] {l1 : List α} {l2 : List β} {o1 o2 n : Nat}
    {f : β → α}
    (h1 : o1 + n ≤ l1.length) (h2 : o2 + n ≤ l2.length)
    (hz : (((l1.drop o1).take n).zip ((l2.drop o2).take n)).all
            (fun p => decide (p.1 = f p.2)) = true) :
    ∀ j, j < n → l1[o1 + j]? = (l2[o2 + j]?).map f := by
  intro j hj
  have hi1 : o1 + j < l1.length := by omega
  have hi2 : o2 + j < l2.length := by omega
  have ha : l1[o1 + j]? = some (l1[o1 + j]) := List.getElem?_eq_getElem hi1
  have hb : l2[o2 + j]? = some (l2[o2 + j]) := List.getElem?_eq_getElem hi2
  have hz' := zip_slice_get l1 l2 o1 o2 n j hj
  rw [ha, hb] at hz'
  simp at hz'
  have hmem : (l1[o1 + j], l2[o2 + j]) ∈
      ((l1.drop o1).take n).zip ((l2.drop o2).take n) :=
    List.mem_iff_getElem?.mpr ⟨j, hz'⟩
  have hdec := List.all_eq_true.mp hz _ hmem
  have heq : l1[o1 + j] = f (l2[o2 + j]) := of_decide_eq_true hdec
  rw [ha, hb, heq]
  rfl

end Hashtree.Proofs.WinScan
