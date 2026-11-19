import Hashtree.Proofs.AvxX4X1Agree
import Hashtree.Proofs.AvxX4LoopWAll
import Hashtree.Proofs.AvxX4Exit

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# The x4 -> x1 chain edge at the W-mode cut, behind a write log

`AvxX4X1Agree` closes the small-count (`0 < c < 4`) x4 -> x1 edge through the dead-register
hand-off.  The all-count (`c >= 4`) cut is `fr M' (mapState e' σ' K201W)`: its log is
nonempty, so the unframed `AgreeOn` pre of the x1 link is false there.  This module states and
proves the x1 pre and post behind that log.

* `agreeOn_fr` lifts `AgreeOn` through appending one log, and `wfAt_view` / `mem_view_eq` show
  that a W-mode log (`OutLogW`) never shadows a cell the x1 kernel reads: the log holds output
  bytes and stack bytes strictly below the return marker at `σ 9`, while the kernel reads the
  table, the input and the return marker at `σ 9 + k`, `0 <= k < 8`.
* `cutEnv` is the environment of the cut.  The cut's abstract state does not settle the
  vector lanes or the shifted pointer registers, so the reference state of the hand-off is
  built from the cut itself: numbered variables above `100` are read out of the cut's own
  vector registers, and the memory keys are read out of the log-framed memory.
* `x1cut_agree` is the `AgreeOn [0, 1, 9]` agreement of the resumed cut with that reference.
  It is where the three fields the cut really differs in are discharged: the write log (empty
  reference, so the cut's is stripped), the vector registers (rebuilt) and the three pointer
  registers `rdx`, `rbp`, `r12`, whose abstract offsets are `tau`'s first three entries.
-/

namespace Hashtree.Proofs.AvxX4X1WAgree

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Kernels.X86.AvxX1
open Hashtree.Proofs.ShaniW (OutOk RegsOk)
open Hashtree.Proofs.AvxX1W (steps InRange correctWAt_entry)
open Hashtree.Proofs.AvxX1Agree (correctWAt_agree)
open Hashtree.Proofs.AvxX4LoopWExit (K201W upd15_9)
open Hashtree.Proofs.AvxX4W (upd15)
open Hashtree.Spec
open Hashtree.Proofs.X86Chain (CS resume)
open Hashtree.Proofs.AvxX4LoopWExit (outLogW_s9)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW outLogW_ne tau_s9 sIt_s9 sAt_eval)
open Hashtree.Proofs.AvxX4LoopTurn (tau)
open Hashtree.Proofs.AvxX4LoopFrame (tau_count TURNLEN)
open Hashtree.Proofs.AvxX4Exit (sigmaOf_tau0 sigmaOf_tau1)
open Hashtree.Proofs.AvxX4LoopWAll (x4_runW)
open Hashtree.Proofs.AvxX4Exit (sIt_0 sIt_1 sIt_2)
open Hashtree.Proofs.AvxX4LoopFrame (sIt)
open Hashtree.Proofs.AvxX4LoopWFrame (sAt_eval)

/-! ## Framing -/

/-- `AgreeOn` survives appending the same log to both states.  Only the `mem` field moves. -/
theorem agreeOn_fr {S : List Nat} {s1 s2 : CS} (L : CLog) (h : AgreeOn S s1 s2) :
    AgreeOn S (fr L s1) (fr L s2) where
  pc := h.pc
  halted := h.halted
  tail := h.tail
  err := h.err
  mem := by simp only [fr]; rw [h.mem]
  vr := h.vr
  assume := h.assume
  flags := h.flags
  glen := h.glen
  gpr := h.gpr
  gpr16 := h.gpr16

/-- A W-mode log never shadows a cell outside the output region and below the return marker. -/
theorem mem_view_eq (mem0c : Addr Int → Cell W32 Int) (M : CLog) (σ : Nat → Int)
    (hM : OutLogW σ M) (a : Addr Int) (h1 : a.region ≠ rOut)
    (h2 : a.region = rStack → σ 9 ≤ a.off) :
    view M mem0c a = mem0c a :=
  view_other M mem0c a (outLogW_ne M σ hM a ⟨h1, h2⟩)

/-- The input cells of the viewed memory are the caller's. -/
theorem view_in (mem0c : Addr Int → Cell W32 Int) (M : CLog) (σ : Nat → Int)
    (hM : OutLogW σ M) (x : Int) :
    view M mem0c ⟨rIn, x⟩ = mem0c ⟨rIn, x⟩ :=
  mem_view_eq mem0c M σ hM _
    (show rIn ≠ rOut from by decide)
    (fun h => absurd (show rIn = rStack from h) (show rIn ≠ rStack from by decide))

/-- W-mode memory well-formedness survives viewing through the log, at a fresh region. -/
theorem wfAt_view (ro : Region) (rodata : List Nat) (env env' : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (M : CLog) (hM : OutLogW σ M)
    (hOut : ro ≠ rOut) (hStk : ro ≠ rStack)
    (hw : WfMemAtW ro rodata [] env σ m) : WfMemAtW ro rodata [] env' σ (view M m) := by
  obtain ⟨htab, hret, hin, hpush⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o
    rw [mem_view_eq m M σ hM _ hOut (fun h => absurd h hStk)]
    exact htab o
  · intro k h0 h8
    rw [mem_view_eq m M σ hM _ (show rStack ≠ rOut from by decide) (fun _ => by simp only; omega)]
    exact hret k h0 h8
  · intro o
    rw [view_in m M σ hM o]
    exact hin o
  · intro k c hk
    simp [plookup] at hk


/-! ## Lists: `getD` over ranges and concatenation -/

theorem range_succ_map {α : Type} (n : Nat) (g : Nat → α) :
    (List.range (n + 1)).map g = g 0 :: (List.range n).map (fun i => g (i + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e1 : (List.range (n + 1 + 1)).map g = (List.range (n + 1)).map g ++ [g (n + 1)] := by
      rw [List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil]
    have e2 : (List.range (n + 1)).map (fun i => g (i + 1)) =
        (List.range n).map (fun i => g (i + 1)) ++ [g (n + 1)] := by
      rw [List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil]
    rw [e1, ih, e2, List.cons_append]

theorem map_range_congr {α : Type} (n : Nat) (f g : Nat → α) (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e1 : (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by
      rw [List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil]
    have e2 : (List.range (n + 1)).map g = (List.range n).map g ++ [g n] := by
      rw [List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil]
    rw [e1, e2, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.length_cons, range_succ_map]
    simp only [List.getD_cons_zero]
    rw [show (fun i => (a :: t).getD (i + 1) d) = (fun i => t.getD i d) from by
      funext i; rw [List.getD_cons_succ]]
    rw [ih]

theorem getD_default {α : Type} (l : List α) (i : Nat) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => simp at h
    | succ i =>
      simp only [List.getD_cons_succ]
      exact ih i (by simpa using h)

theorem getD_append_lt {α : Type} : ∀ (a b : List α) (k : Nat) (d : α), k < a.length →
    (a ++ b).getD k d = a.getD k d
  | [], _, _, _, h => by simp at h
  | x :: xs, b, 0, d, _ => rfl
  | x :: xs, b, k + 1, d, h => by
    rw [show (x :: xs) ++ b = x :: (xs ++ b) from rfl, List.getD_cons_succ, List.getD_cons_succ]
    exact getD_append_lt xs b k d (by simpa using h)

theorem getD_append_ge {α : Type} : ∀ (a b : List α) (k : Nat) (d : α),
    (a ++ b).getD (a.length + k) d = b.getD k d
  | [], b, k, d => by simp
  | x :: xs, b, k, d => by
    rw [show (x :: xs).length + k = (xs.length + k) + 1 from by simp; omega,
      show (x :: xs) ++ b = x :: (xs ++ b) from rfl, List.getD_cons_succ]
    exact getD_append_ge xs b k d

theorem getD_flat {α : Type} (ll : List (List α)) (d : α) :
    ∀ (i : Nat), i < ll.length → (∀ l ∈ ll, l.length = 16) →
      (List.range 16).map (fun l => ll.flatten.getD (16 * i + l) d) = ll.getD i [] := by
  induction ll with
  | nil => intro i h; simp at h
  | cons l0 rest ih =>
    intro i hlen hinner
    have hl0 : l0.length = 16 := hinner l0 (List.mem_cons_self ..)
    have hflat : (l0 :: rest).flatten = l0 ++ rest.flatten := rfl
    cases i with
    | zero =>
      rw [hflat]
      have hmap : (List.range 16).map (fun l => (l0 ++ rest.flatten).getD (16 * 0 + l) d) =
          (List.range 16).map (fun l => l0.getD l d) := by
        apply map_range_congr
        intro l hl
        rw [show 16 * 0 + l = l from by omega,
          getD_append_lt l0 rest.flatten l d (by omega)]
      rw [hmap, show (16 : Nat) = l0.length from hl0.symm, getD_range]
      rfl
    | succ i =>
      rw [hflat]
      have hleni : i < rest.length := by simpa using hlen
      have heq : (List.range 16).map (fun l => (l0 ++ rest.flatten).getD (16 * (i + 1) + l) d) =
          (List.range 16).map (fun l => rest.flatten.getD (16 * i + l) d) := by
        apply map_range_congr
        intro l hl
        rw [show 16 * (i + 1) + l = l0.length + (16 * i + l) from by rw [hl0]; omega,
          getD_append_ge]
      rw [heq, ih i hleni (fun l hl => hinner l (List.mem_cons_of_mem _ hl))]
      rfl

/-! ## The environment of the cut -/

/-- The exit cut's vector lanes in one list, evaluated in the cut's own environment. -/
def cutFlat (e : Key → W32) : List W32 := (K201W.vr.map (·.map (E.eval e))).flatten

/-- The cut's environment.  Numbered variables from `100` on are the cut's own vector lanes
(the `vId` keys of its abstract vector registers); the ones below are the caller's; memory
keys read the log-framed memory through the region renaming. -/
def cutEnv (ρ : RegionRenaming) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) : Key → W32
  | .n i => if 100 ≤ i then (cutFlat e).getD (i - 100) 0 else e (.n i)
  | .m r off => cellX (ρ.mem m ⟨r, off.eval σ⟩)

theorem cutEnv_mem (ρ : RegionRenaming) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) : EnvMem (cutEnv ρ e σ m) σ (ρ.mem m) := fun _ _ => rfl

theorem cutEnv_n_hi (ρ : RegionRenaming) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (i : Nat) (h : 100 ≤ i) :
    cutEnv ρ e σ m (.n i) = (cutFlat e).getD (i - 100) 0 := by
  simp only [cutEnv, if_pos h]

theorem cutEnv_n_lo (ρ : RegionRenaming) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (i : Nat) (h : ¬ 100 ≤ i) :
    cutEnv ρ e σ m (.n i) = e (.n i) := by
  simp only [cutEnv, if_neg h]

/-! ## Shape facts of the exit cut -/

theorem K201W_vr_len : K201W.vr.length = 32 := by decide +kernel
theorem K201W_vr_lanes : K201W.vr.all (fun l => l.length == 16) = true := by decide +kernel
/-- The cut's vector registers are its own `getD` lanes. -/
theorem K201W_vr_eq_range : K201W.vr = (List.range 32).map (fun i => K201W.vr.getD i []) := by
  have h := getD_range K201W.vr ([] : List E)
  rw [K201W_vr_len] at h
  exact h.symm

theorem entryW_vr_shape :
    entryW.vr = (List.range 32).map (fun i => (List.range 16).map fun l => E.var (.n (vId i l))) :=
  rfl

theorem cutFlat_lane (e : Key → W32) :
    ∀ l ∈ K201W.vr.map (·.map (E.eval e)), l.length = 16 := by
  intro l hl
  obtain ⟨l0, h0, rfl⟩ := List.mem_map.mp hl
  rw [List.length_map]
  exact beq_iff_eq.mp (List.all_eq_true.mp K201W_vr_lanes l0 h0)

/-- `getD` commutes with `map` when the default is preserved. -/
theorem getD_map_eq {α β : Type} (f : α → β) (l : List α) (i : Nat) (da : α) (db : β)
    (hd : f da = db) : (l.map f).getD i db = f (l.getD i da) := by
  induction l generalizing i with
  | nil =>
    cases i with
    | zero => exact hd.symm
    | succ i => exact hd.symm
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih i

/-- One vector lane of the cut, rebuilt from its own lanes. -/
theorem cut_vr_lane (ρ : RegionRenaming) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (i : Nat) (hi : i < 32) :
    (List.range 16).map (fun l => cutEnv ρ e σ m (.n (vId i l))) =
      (K201W.vr.getD i []).map (E.eval e) := by
  have h1 : ∀ l, cutEnv ρ e σ m (.n (vId i l)) = (cutFlat e).getD (16 * i + l) 0 := by
    intro l
    rw [cutEnv_n_hi ρ e σ m _ (by unfold vId; omega)]
    congr 1
    unfold vId
    omega
  rw [show (fun l => cutEnv ρ e σ m (.n (vId i l))) =
      (fun l => (cutFlat e).getD (16 * i + l) 0) from funext h1]
  have hlen : i < (K201W.vr.map (·.map (E.eval e))).length := by
    rw [List.length_map, K201W_vr_len]; exact hi
  rw [show cutFlat e = (K201W.vr.map (·.map (E.eval e))).flatten from rfl]
  rw [getD_flat (K201W.vr.map (·.map (E.eval e))) 0 i hlen (cutFlat_lane e)]
  exact getD_map_eq (·.map (E.eval e)) K201W.vr i [] [] rfl

/-! ## Shape facts of the cut's registers -/

/-- The cut's general registers. -/
def K201L : List (Val E Lin) :=
  [.ptr ⟨rOut, Lin.sym 15⟩, .ptr ⟨4, ⟨1024, []⟩⟩, .ptr ⟨rNum, ⟨-4, [0, 0, 1]⟩⟩,
   .ptr ⟨rStack, Lin.sym 5⟩, .ptr ⟨rStack, sAt 0⟩, .ptr ⟨rStack, Lin.sym 6⟩,
   .ptr ⟨rIn, ⟨256, [1]⟩⟩, .ptr ⟨rOut, ⟨128, [0, 1]⟩⟩,
   .num (.var (.n 16)) (.var (.n 17)), .ptr ⟨rNum, ⟨1024, []⟩⟩,
   .num (.var (.n 20)) (.var (.n 21)), .num (.var (.n 22)) (.var (.n 23)),
   .ptr ⟨rStack, Lin.sym 7⟩, .ptr ⟨rNum, Lin.sym 11⟩, .ptr ⟨rG, Lin.sym 8⟩,
   .ptr ⟨rNum, Lin.sym 12⟩]

/-- The wrapper call state's general registers. -/
def E201L : List (Val E Lin) :=
  [.ptr ⟨rOut, Lin.sym 1⟩, .ptr ⟨rNum, Lin.sym 2⟩, .ptr ⟨rNum, Lin.sym 2⟩,
   .ptr ⟨rStack, Lin.sym 5⟩, .ptr ⟨rStack, sAt 0⟩, .ptr ⟨rStack, Lin.sym 6⟩,
   .ptr ⟨rIn, Lin.sym 0⟩, .ptr ⟨rOut, Lin.sym 1⟩,
   .num (.var (.n 16)) (.var (.n 17)), .num (.var (.n 18)) (.var (.n 19)),
   .num (.var (.n 20)) (.var (.n 21)), .num (.var (.n 22)) (.var (.n 23)),
   .ptr ⟨rStack, Lin.sym 7⟩, .ptr ⟨rNum, Lin.sym 11⟩, .ptr ⟨rG, Lin.sym 8⟩,
   .ptr ⟨rNum, Lin.sym 12⟩]

theorem K201W_gpr_list : K201W.gpr = K201L := by decide +kernel
theorem entryW_gpr_list : entryW.gpr = E201L := by decide +kernel
theorem K201L_len : K201L.length = 16 := rfl
theorem E201L_len : E201L.length = 16 := rfl

/-- `tau` acts trivially on the symbols from `5` on. -/
theorem tauAt_hi (i : Nat) (h : 5 ≤ i) : tauAt tau i = Lin.sym i := by
  unfold tauAt tau
  split <;> (apply getD_default; simpa using h)

theorem sigmaOf_hi (i : Nat) (h : 5 ≤ i) (σ : Nat → Int) :
    sigmaOf tau σ i = σ i := by
  rw [sigmaOf, tauAt_hi i h, Lin.eval_sym]

theorem sigmaOf_s9 (σ : Nat → Int) : sigmaOf tau σ 9 = σ 9 := sigmaOf_hi 9 (by omega) σ

/-! ## `mapVal` agreement on the cut's register values -/

theorem mapVal_ptr_sym (e : Key → W32) (σ' σ1 : Nat → Int)
    (hσ : ∀ k, 5 ≤ k → σ1 k = σ' k) (reg : Region) (k : Nat) (hk : 5 ≤ k) :
    mapVal e σ' (.ptr ⟨reg, Lin.sym k⟩) = mapVal e σ1 (.ptr ⟨reg, Lin.sym k⟩) := by
  simp only [mapVal, mapAddr, Lin.eval_sym, hσ k hk]

theorem mapVal_ptr_sAt (e : Key → W32) (σ' σ1 : Nat → Int) (h9 : σ1 9 = σ' 9) :
    mapVal e σ' (.ptr ⟨rStack, sAt 0⟩) = mapVal e σ1 (.ptr ⟨rStack, sAt 0⟩) := by
  simp only [mapVal, mapAddr, sAt, sAt_eval, h9]

theorem mapVal_num_n (e env : Key → W32) (σ' σ1 : Nat → Int)
    (he : ∀ i, i < 100 → e (.n i) = env (.n i)) (a b : Nat) (ha : a < 100) (hb : b < 100) :
    mapVal e σ' (.num (.var (.n a)) (.var (.n b))) =
      mapVal env σ1 (.num (.var (.n a)) (.var (.n b))) := by
  show (.num (e (.n a)) (e (.n b)) : Val W32 Int) = .num (env (.n a)) (env (.n b))
  rw [he a ha, he b hb]

theorem lin_eval_shift2 (σ : Nat → Int) : (⟨-4, [0, 0, 1]⟩ : Lin).eval σ = σ 2 - 4 := by
  simp [Lin.eval, dotC]
  omega

theorem lin_eval_shift6 (σ : Nat → Int) : (⟨256, [1]⟩ : Lin).eval σ = σ 0 + 256 := by
  simp [Lin.eval, dotC]
  omega

theorem lin_eval_shift7 (σ : Nat → Int) : (⟨128, [0, 1]⟩ : Lin).eval σ = σ 1 + 128 := by
  simp [Lin.eval, dotC]
  omega

/-- The cut's `rdx`: `tau`'s count entry. -/
theorem mapVal_shift2 (e : Key → W32) (σ' σ1 : Nat → Int) (h2 : σ1 2 = σ' 2 - 4) :
    mapVal e σ' (.ptr ⟨rNum, ⟨-4, [0, 0, 1]⟩⟩) = mapVal e σ1 (.ptr ⟨rNum, Lin.sym 2⟩) := by
  simp only [mapVal, mapAddr, Lin.eval_sym]
  rw [h2, lin_eval_shift2]

/-- The cut's `rbp`: `tau`'s input entry. -/
theorem mapVal_shift6 (e : Key → W32) (σ' σ1 : Nat → Int) (h0 : σ1 0 = σ' 0 + 256) :
    mapVal e σ' (.ptr ⟨rIn, ⟨256, [1]⟩⟩) = mapVal e σ1 (.ptr ⟨rIn, Lin.sym 0⟩) := by
  simp only [mapVal, mapAddr, Lin.eval_sym]
  rw [h0, lin_eval_shift6]

/-- The cut's `r12`: `tau`'s output entry. -/
theorem mapVal_shift7 (e : Key → W32) (σ' σ1 : Nat → Int) (h1 : σ1 1 = σ' 1 + 128) :
    mapVal e σ' (.ptr ⟨rOut, ⟨128, [0, 1]⟩⟩) = mapVal e σ1 (.ptr ⟨rOut, Lin.sym 1⟩) := by
  simp only [mapVal, mapAddr, Lin.eval_sym]
  rw [h1, lin_eval_shift7]

/-! ## `getD` on a mapped list, below its length -/

theorem getD_map_lt {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat) (h : i < l.length)
    (db : β) (da : α), (l.map f).getD i db = f (l.getD i da) := by
  intro l
  induction l with
  | nil => intro i h; simp at h
  | cons x xs ih =>
    intro i h db da
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih i (by simpa using h) db da

/-! ## The framed cut and the reference entry state -/

/-- The cut of the W-mode exit, with its write log split off: the entry state the x1 slice
sees once the log framing is applied. -/
def cutBare (e' : Key → W32) (σ' : Nat → Int) : CS :=
  { resume (mapState e' σ' K201W) with mem := [] }

/-- The x1 entry state the framed cut is compared against: the reference `entryW`, with the
cut's environment (which places the cut's vector lanes and reads the log-framed memory through
the region renaming). -/
def refCut (ρ : RegionRenaming) (e' : Key → W32) (σ' : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (M' : CLog) : CS :=
  { mapState (cutEnv ρ e' (sigmaOf tau σ')
      (view ((mapState e' σ' K201W).mem ++ M') mem0c)) (sigmaOf tau σ') entryW
    with flags := (cutBare e' σ').flags }

/-! ## The register agreement at the cut -/

theorem cut_gpr_pointwise (e' env : Key → W32) (σ' σ1 : Nat → Int)
    (hσ : ∀ k, 5 ≤ k → σ1 k = σ' k)
    (h0 : σ1 0 = σ' 0 + 256) (h1 : σ1 1 = σ' 1 + 128) (h2 : σ1 2 = σ' 2 - 4)
    (h9 : σ1 9 = σ' 9) (he : ∀ i, i < 100 → e' (.n i) = env (.n i))
    (i : Nat) (hi : i < 16) (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi9 : i ≠ 9) :
    mapVal e' σ' (K201L.getD i (default : Val E Lin)) =
      mapVal env σ1 (E201L.getD i (default : Val E Lin)) := by
  have hdisj : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hdisj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [K201L, E201L, List.getD_cons_zero, List.getD_cons_succ]
  · exact mapVal_shift2 e' σ' σ1 h2
  · exact mapVal_ptr_sym e' σ' σ1 hσ rStack 5 (by omega)
  · exact mapVal_ptr_sAt e' σ' σ1 h9
  · exact mapVal_ptr_sym e' σ' σ1 hσ rStack 6 (by omega)
  · exact mapVal_shift6 e' σ' σ1 h0
  · exact mapVal_shift7 e' σ' σ1 h1
  · exact mapVal_num_n e' env σ' σ1 he 16 17 (by omega) (by omega)
  · exact mapVal_num_n e' env σ' σ1 he 20 21 (by omega) (by omega)
  · exact mapVal_num_n e' env σ' σ1 he 22 23 (by omega) (by omega)
  · exact mapVal_ptr_sym e' σ' σ1 hσ rStack 7 (by omega)
  · exact mapVal_ptr_sym e' σ' σ1 hσ rNum 11 (by omega)
  · exact mapVal_ptr_sym e' σ' σ1 hσ rG 8 (by omega)
  · exact mapVal_ptr_sym e' σ' σ1 hσ rNum 12 (by omega)

/-! ## The log-framed W-cut agreement -/

/-- **The log-framed agreement at the W-mode exit cut.**  The cut state `cutBare` (the exit
slice's final state with its write log removed) agrees with the flagged x1 entry state of
`refCut` outside `{rax, rcx, r9}`.  There is no hypothesis on the log: the three fields that do
not survive a nonempty log (`mem`, `vr`, `gpr[rax/rcx/r9]`) are rebuilt by `cutBare`'s empty log
and by `cutEnv`, which names the cut's own vector lanes and its memory through the renaming.

The field goals are closed by unfolding the two states with `simp only` (which reduces the
projections syntactically); a `rfl` on `A.pc = B.pc` would make the unifier compare the two
states first and evaluate the symbolic exit run `K201W` in the elaborator. -/
theorem x1cut_agree (e' : Key → W32) (σ' : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (M' : CLog) (r : Region) :
    AgreeOn [0, 1, 9] (cutBare e' σ') (refCut (swap 4 r) e' σ' mem0c M') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cutBare, refCut, resume, mapState, entryW]
  · simp only [cutBare, refCut, resume, mapState, entryW]
  · simp only [cutBare, refCut, resume, mapState, entryW]
  · simp only [cutBare, refCut, resume, mapState, entryW, Hashtree.Proofs.AvxX4LoopWExit.K201W_err]
  · simp only [cutBare, refCut, resume, mapState, entryW, List.map_nil]
  · -- the vector lanes
    simp only [cutBare, refCut, resume, mapState]
    rw [entryW_vr_shape, K201W_vr_eq_range]
    simp only [List.map_map, Function.comp_def]
    apply map_range_congr
    intro i hi
    exact (cut_vr_lane (swap 4 r) e' (sigmaOf tau σ')
      (view ((mapState e' σ' K201W).mem ++ M') mem0c) i (by simpa using hi)).symm
  · simp only [cutBare, refCut, resume, mapState, entryW]
  · intro _
    simp only [cutBare, refCut, resume, mapState]
  · -- register file length
    simp only [cutBare, refCut, resume, mapState, K201W_gpr_list, entryW_gpr_list]
    rw [List.length_map, List.length_map, K201L_len, E201L_len]
  · -- the registers outside `{rax, rcx, r9}`
    intro i hi
    have h3 : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 9 := by simpa using hi
    simp only [cutBare, refCut, resume, mapState, State.getG, K201W_gpr_list, entryW_gpr_list]
    by_cases h16 : i < 16
    · rw [getD_map_lt _ _ _ (by rw [K201L_len]; exact h16),
        getD_map_lt _ _ _ (by rw [E201L_len]; exact h16)]
      exact cut_gpr_pointwise e' _ σ' (sigmaOf tau σ')
        (fun k hk => sigmaOf_hi k hk σ')
        (sigmaOf_tau0 σ') (sigmaOf_tau1 σ') (tau_count σ') (sigmaOf_s9 σ')
        (fun j hj => (cutEnv_n_lo (swap 4 r) e' (sigmaOf tau σ')
          (view ((mapState e' σ' K201W).mem ++ M') mem0c) j (by omega)).symm)
        i h16 h3.1 h3.2.1 h3.2.2
    · rw [getD_default _ _ _ (by rw [List.length_map, K201L_len]; omega),
        getD_default _ _ _ (by rw [List.length_map, E201L_len]; omega)]
  · -- the pseudo-register `flg`
    have hf : flg = 16 := rfl
    simp only [cutBare, refCut, resume, mapState, State.getG, K201W_gpr_list, entryW_gpr_list]
    rw [getD_default _ _ _ (by rw [List.length_map, K201L_len]; omega),
        getD_default _ _ _ (by rw [List.length_map, E201L_len]; omega)]



/-! ## The log-framed x1 link at the W-mode cut -/

/-- `OutLogW` depends on `σ` only through `σ 9`. -/
theorem outLogW_congr (σ σ1 : Nat → Int) (h9 : σ1 9 = σ 9) (M : CLog)
    (h : OutLogW σ M) : OutLogW σ1 M := by
  intro p hp
  rcases h p hp with h' | ⟨h1, h2⟩
  · exact Or.inl h'
  · exact Or.inr ⟨h1, by rw [h9]; exact h2⟩

/-- The exit cut's write log: its own slice's writes and the turns before it. -/
def cutLog (e' : Key → W32) (σ' : Nat → Int) (M' : CLog) : CLog :=
  (mapState e' σ' K201W).mem ++ M'

/-- The state handed to the next link at the W-mode tail call: the resumed cut, with its log
split into the pre-frame `M'` and the write log. -/
theorem resume_cut_fr (e' : Key → W32) (σ' : Nat → Int) (M' : CLog) :
    resume (fr M' (mapState e' σ' K201W)) = fr (cutLog e' σ' M') (cutBare e' σ') := by
  simp only [resume, fr, cutBare, cutLog, List.nil_append]

/-- The x1 run of the link, behind the cut's log. -/
theorem run_cut_fr (c1 : Nat) (e' : Key → W32) (σ' : Nat → Int) (M' : CLog)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r : Region) :
    run Hashtree.Kernels.X86.AvxX1.prog r mem0c orcC (steps c1)
        (resume (fr M' (mapState e' σ' K201W)))
      = fr (cutLog e' σ' M')
          (run Hashtree.Kernels.X86.AvxX1.prog r (view (cutLog e' σ' M') mem0c) orcC
            (steps c1) (cutBare e' σ')) := by
  rw [resume_cut_fr, run_fr]

/-- The W-mode memory shape does not see the `tau` shift of the stack pointer. -/
theorem wfAt_shift (ro : Region) (rodata : List Nat)
    (env : Key → W32) (σ σ1 : Nat → Int) (h9 : σ1 9 = σ 9)
    (m : Addr Int → Cell W32 Int) (hw : WfMemAtW ro rodata [] env σ m) :
    WfMemAtW ro rodata [] env σ1 m := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  exact ⟨h1, fun k h0 h8 => by rw [h9]; exact h2 k h0 h8, h3, fun k c hk => by simp [plookup] at hk⟩

/-- The x1 table, return-marker and input clauses survive the log framing and the count shift:
none of them is shadowed by a W-mode log, and none mentions the shifted components of `σ`. -/
theorem wfAt_cut (ro : Region) (rodata : List Nat) (env env' : Key → W32)
    (σ σ1 : Nat → Int) (h9 : σ1 9 = σ 9) (m : Addr Int → Cell W32 Int) (L : CLog)
    (hL : OutLogW σ1 L) (hOut : ro ≠ rOut) (hStk : ro ≠ rStack)
    (hw : WfMemAtW ro rodata [] env σ m) :
    WfMemAtW ro rodata [] env' σ1 (view L m) :=
  wfAt_view ro rodata env env' σ1 m L hL hOut hStk (wfAt_shift ro rodata env σ σ1 h9 m hw)

/-- The region renaming does not move the input region. -/
theorem swap_mem_in (r : Region) (hr : rIn ≠ r) (m : Addr Int → Cell W32 Int) (x : Int)
    (v : W32) (h : m ⟨rIn, x⟩ = .dat v 0) :
    (swap 4 r).mem m ⟨rIn, x⟩ = .dat v 0 := by
  have hf : (swap 4 r).f rIn = rIn := swap_fixes 4 r rIn (by decide) hr
  show (swap 4 r).cell (m ((swap 4 r).addr ⟨rIn, x⟩)) = .dat v 0
  rw [show (swap 4 r).addr (⟨rIn, x⟩ : Addr Int) = ⟨rIn, x⟩ from by
    simp only [RegionRenaming.addr, hf], h]
  rfl

/-- The input bytes of the caller, seen through the log frame and the renaming. -/
theorem swap_view_in (r : Region) (hr : r ≠ rIn) (mem0c : Addr Int → Cell W32 Int)
    (L : CLog) (σ : Nat → Int) (hL : OutLogW σ L) (x : Int) (v : W32)
    (h : mem0c ⟨rIn, x⟩ = .dat v 0) :
    (swap 4 r).mem (view L mem0c) ⟨rIn, x⟩ = .dat v 0 :=
  swap_mem_in r (Ne.symm hr) (view L mem0c) x v (by rw [view_in mem0c L σ hL x]; exact h)

/-! ## The x1 post at the W-mode cut -/

/-- **The x1 post at the W-mode cut.**  `correctWAt_agree` at the resumed cut: the premise is
the log-framed agreement `x1cut_agree`, and the postcondition is the x1 all-count post on the
run's own (pre-frame) log. -/
theorem x1cut_bridge (c1 : Nat) (inp : Nat → Byte) (e' : Key → W32) (σ' : Nat → Int)
    (m1 : Addr Int → Cell W32 Int) (M' : CLog) (orcC : Nat → Bool) (r : Region)
    (hrNum : r ≠ rNum) (hrIn : r ≠ rIn) (hrOut : r ≠ rOut) (hrStack : r ≠ rStack)
    (hrG : r ≠ rG) (hrRet : r ≠ rRet)
    (hw : WfMemAtW r rodata [] (cutEnv (swap 4 r) e' (sigmaOf tau σ') m1)
      (sigmaOf tau σ') m1)
    (he : EnvMem (cutEnv (swap 4 r) e' (sigmaOf tau σ') m1) (sigmaOf tau σ')
      ((swap 4 r).mem m1))
    (hc : sigmaOf tau σ' 2 = (c1 : Int))
    (hin : ∀ o : Nat, (swap 4 r).mem m1 ⟨rIn, sigmaOf tau σ' 0 + o⟩ =
      .dat ((inp o).zeroExtend 32) 0) :
    let fin := run Hashtree.Kernels.X86.AvxX1.prog r m1 orcC (steps c1) (cutBare e' σ')
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (sigmaOf tau σ' 9) (sigmaOf tau σ' 1) (32 * c1) fin.mem ∧
      OutOk inp (sigmaOf tau σ' 1) c1 fin.mem ∧
      RegsOk (cutEnv (swap 4 r) e' (sigmaOf tau σ') m1) (sigmaOf tau σ') fin :=
  correctWAt_agree c1 inp (cutEnv (swap 4 r) e' (sigmaOf tau σ') m1) (sigmaOf tau σ')
    m1 orcC r hrNum hrIn hrOut hrStack hrG hrRet hw he hc hin _ _
    (x1cut_agree e' σ' m1 M' r)

/-- **The log-framed x1 post on the framed final state.**  The x1 link, entered at the resumed
cut `resume (fr M' (mapState e' σ' K201W))`, runs exactly as the bare cut over the framed
memory `view L mem0c`, and its postcondition holds of the bare run whose log the frame
extends. -/
theorem x1cut_framed (c1 : Nat) (inp : Nat → Byte) (e' : Key → W32) (σ' : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (M' : CLog) (orcC : Nat → Bool) (r : Region)
    (hrNum : r ≠ rNum) (hrIn : r ≠ rIn) (hrOut : r ≠ rOut) (hrStack : r ≠ rStack)
    (hrG : r ≠ rG) (hrRet : r ≠ rRet)
    (hw : WfMemAtW r rodata []
      (cutEnv (swap 4 r) e' (sigmaOf tau σ') (view (cutLog e' σ' M') mem0c))
      (sigmaOf tau σ') (view (cutLog e' σ' M') mem0c))
    (he : EnvMem (cutEnv (swap 4 r) e' (sigmaOf tau σ') (view (cutLog e' σ' M') mem0c))
      (sigmaOf tau σ') ((swap 4 r).mem (view (cutLog e' σ' M') mem0c)))
    (hc : sigmaOf tau σ' 2 = (c1 : Int))
    (hin : ∀ o : Nat, (swap 4 r).mem (view (cutLog e' σ' M') mem0c)
      ⟨rIn, sigmaOf tau σ' 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let L : CLog := cutLog e' σ' M'
    let fin : CS := run Hashtree.Kernels.X86.AvxX1.prog r (view L mem0c) orcC (steps c1)
      (cutBare e' σ')
    run Hashtree.Kernels.X86.AvxX1.prog r mem0c orcC (steps c1)
        (resume (fr M' (mapState e' σ' K201W))) = fr L fin ∧
      fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (sigmaOf tau σ' 9) (sigmaOf tau σ' 1) (32 * c1) fin.mem ∧
      OutOk inp (sigmaOf tau σ' 1) c1 fin.mem ∧
      RegsOk (cutEnv (swap 4 r) e' (sigmaOf tau σ') (view L mem0c)) (sigmaOf tau σ') fin := by
  dsimp only
  exact ⟨run_cut_fr c1 e' σ' M' mem0c orcC r,
    x1cut_bridge c1 inp e' σ' (view (cutLog e' σ' M') mem0c) M' orcC r hrNum hrIn hrOut
      hrStack hrG hrRet hw he hc hin⟩

/-! ## The full x4 -> x1 contract at the W-mode cut -/

/-- The x4 run's step count at the W-mode exit (`AvxX4LoopWAll.x4_runW`'s literal). -/
def wAllSteps (j : Nat) : Nat := ((72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 23)) + j * TURNLEN) + (68 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27))

/-- **The x4 -> x1 contract at the W-mode exit cut.**  The all-count path: after the x4 run
reaches the exit cut (whose step count, cut state and log are `x4_runW`'s), the x1 link is
entered at the resumed, log-framed cut and meets the x1 postcondition.

The x4 side is `x4_runW`; the x1 side is `x1cut_framed`, whose three cut premises are supplied
here from the x4 entry contract `hw1` and the input contract `hin1`: only the table/stack/input
clauses are needed, and none of them is shadowed by the log.  The W mode abstracts the stored
bytes, so no `OutOk` fact about the cut's own writes is claimed. -/
theorem x4_x1_W (j s c1 : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r : Region)
    (hrNum : r ≠ rNum) (hrIn : r ≠ rIn) (hrOut : r ≠ rOut) (hrStack : r ≠ rStack)
    (hrG : r ≠ rG) (hrRet : r ≠ rRet)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hs : 4 ≤ s) (hs8 : s < 8)
    (hc : σ 2 = 4 * ((j : Int) + 1) + (s : Int))
    (hw1 : WfMemAtW r rodata [] env0 σ mem0c)
    (hin1 : ∀ o : Nat, mem0c ⟨rIn, (sIt (j + 1) (upd15 σ)) 0 + 256 + o⟩ =
      .dat ((inp o).zeroExtend 32) 0)
    (hc1 : sigmaOf tau (sIt (j + 1) (upd15 σ)) 2 = (c1 : Int)) :
    ∃ (e' : Key → W32) (M' : CLog),
      run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC (wAllSteps j)
          (fr M (mapState env0 σ entryW)) =
        fr M' (mapState e' (sIt (j + 1) (upd15 σ)) K201W) ∧
      OutLogW (sIt (j + 1) (upd15 σ)) (cutLog e' (sIt (j + 1) (upd15 σ)) M') ∧
      (let σ1 : Nat → Int := sigmaOf tau (sIt (j + 1) (upd15 σ))
       let L : CLog := cutLog e' (sIt (j + 1) (upd15 σ)) M'
       let fin : CS := run Hashtree.Kernels.X86.AvxX1.prog r (view L mem0c) orcC (steps c1)
         (cutBare e' (sIt (j + 1) (upd15 σ)))
       run Hashtree.Kernels.X86.AvxX1.prog r mem0c orcC (steps c1)
           (resume (fr M' (mapState e' (sIt (j + 1) (upd15 σ)) K201W))) = fr L fin ∧
         fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
         InRange (σ1 9) (σ1 1) (32 * c1) fin.mem ∧ OutOk inp (σ1 1) c1 fin.mem ∧
         RegsOk (cutEnv (swap 4 r) e' σ1 (view L mem0c)) σ1 fin) := by
  obtain ⟨e', M', hrun, hlog⟩ := x4_runW env0 σ mem0c orcC M hw4 hM j s hs hs8 hc
  refine ⟨e', M', ?_, ?_, ?_⟩
  · unfold wAllSteps
    exact hrun
  · show OutLogW _ ((mapState e' _ K201W).mem ++ M')
    exact hlog
  · have hσ9 : sIt (j + 1) (upd15 σ) 9 = σ 9 := by rw [sIt_s9, upd15_9]
    have h9 : sigmaOf tau (sIt (j + 1) (upd15 σ)) 9 = σ 9 := by
      rw [sigmaOf_s9]; exact hσ9
    have hlog' : OutLogW (sigmaOf tau (sIt (j + 1) (upd15 σ)))
        (cutLog e' (sIt (j + 1) (upd15 σ)) M') :=
      outLogW_congr _ _ (sigmaOf_s9 _) _ (by simpa only [cutLog, mapState] using hlog)
    refine x1cut_framed c1 inp e' (sIt (j + 1) (upd15 σ)) mem0c M' orcC r hrNum hrIn
      hrOut hrStack hrG hrRet ?_ ?_ hc1 ?_
    · exact wfAt_cut r rodata env0 _ σ (sigmaOf tau (sIt (j + 1) (upd15 σ))) h9 mem0c _
        hlog' hrOut hrStack hw1
    · exact fun _ _ => rfl
    · intro o
      rw [sigmaOf_tau0]
      exact swap_view_in r hrIn mem0c _ _ hlog' _ _ (hin1 o)


end Hashtree.Proofs.AvxX4X1WAgree
