import Hashtree.Asm.X86Loop

/-!
# Loop heads of kernels that save registers on the stack

A kernel that pushes callee-saved registers in its prologue reads them back in its epilogue.
When a proof restarts at the loop head, those pushes are part of the older log, i.e. of the
initial memory of the restarted segment.  `mem0sH` makes that push area `[lo, sp0)` readable:
unknowns keyed by address, as byte `o % 4` of a stored lane (pushes store 4-aligned lanes).
`WfMemH` is the matching concrete condition; `wfH_view` establishes it from the prologue's log.
-/

namespace Hashtree.Asm.X86
open Hashtree.Asm Hashtree.Asm.X86Sym

def mem0sH (ro : Region) (rodata : List Nat) (sp0 lo : Int) : Addr Lin → Cell E Lin := fun a =>
  if a.region = rStack then
    match a.off.asInt with
    | some o => if lo ≤ o ∧ o < sp0 then .dat (.var (.m a.region a.off)) (o % 4).toNat else mem0s ro rodata sp0 a
    | none => mem0s ro rodata sp0 a
  else mem0s ro rodata sp0 a

def WfMemH (rodata : List Nat) (lo : Int) (m : Addr Int → Cell W32 Int) : Prop :=
  WfMem 4 rodata 24 m ∧ ∀ o, lo ≤ o → o < 24 → m ⟨rStack, o⟩ = .dat (cellX (m ⟨rStack, o⟩)) (o % 4).toNat

theorem mem0RelH_of_wf (rodata : List Nat) (lo : Int) (env : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (hw : WfMemH rodata lo m) (he : EnvMem env σ m) :
    Mem0Rel env σ (mem0sH 4 rodata 24 lo) m := by
  have h0 := mem0Rel_of_wf 4 rodata 24 env σ m hw.1 he
  intro a ha
  obtain ⟨r, off⟩ := a
  by_cases hr : r = rStack
  · subst hr
    cases hk : off.asInt with
    | none =>
      have e : mem0sH 4 rodata 24 lo ⟨rStack, off⟩ = mem0s 4 rodata 24 ⟨rStack, off⟩ := by
        simp only [mem0sH, ite_true, hk]
      rw [e] at ha ⊢; exact h0 _ ha
    | some o =>
      by_cases hlo : lo ≤ o ∧ o < 24
      · have e : mem0sH 4 rodata 24 lo ⟨rStack, off⟩ = .dat (.var (.m rStack off)) (o % 4).toNat := by
          simp only [mem0sH, ite_true, hk, hlo, and_self]
        rw [e]
        have hev : off.eval σ = o := Lin.eval_asInt σ off o hk
        simp only [mapCell, E.eval, mapAddr, hev]
        rw [he, hev]; exact hw.2 o hlo.1 hlo.2
      · have e : mem0sH 4 rodata 24 lo ⟨rStack, off⟩ = mem0s 4 rodata 24 ⟨rStack, off⟩ := by
          simp only [mem0sH, ite_true, hk, hlo, ite_false]
        rw [e] at ha ⊢; exact h0 _ ha
  · have e : mem0sH 4 rodata 24 lo ⟨r, off⟩ = mem0s 4 rodata 24 ⟨r, off⟩ := by
      simp only [mem0sH, hr, ite_false]
    rw [e] at ha ⊢; exact h0 _ ha

theorem mem0sH_keyed (rodata : List Nat) (lo : Int) : MemKeyed (mem0sH 4 rodata 24 lo) := by
  intro a
  have hk := mem0s_keyed 4 rodata 24 a
  simp only [mem0sH]
  split
  · split
    · split
      · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
      · exact hk
    · exact hk
  · exact hk

theorem wfH_view (rodata : List Nat) (lo : Int) (m : Addr Int → Cell W32 Int) (M : CLog) (hM : OutLog M)
    (hw : WfMem 4 rodata 24 m)
    (hp : ∀ o, lo ≤ o → o < 24 → ∃ x, lookup (⟨rStack, o⟩ : Addr Int) M = .ok (some (.dat x (o % 4).toNat))) :
    WfMemH rodata lo (view M m) := by
  refine ⟨wf_view rodata m M hM hw, fun o h1 h2 => ?_⟩
  obtain ⟨x, hx⟩ := hp o h1 h2
  simp only [view, hx, cellX]

/-- The push area of a symbolic log: every byte is byte `o % 4` of a stored lane. -/
def pushOk (K : State E Lin) (lo : Int) : Bool :=
  (List.range (24 - lo).toNat).all fun i =>
    match lookup (⟨rStack, Lin.ofInt (lo + i)⟩ : Addr Lin) K.mem with
    | .ok (some (.dat _ k)) => k == ((lo + i) % 4).toNat
    | _ => false

theorem pushOk_sound (e : Key → W32) (σ : Nat → Int) (K : State E Lin) (lo : Int) (h : pushOk K lo = true) :
    ∀ o, lo ≤ o → o < 24 → ∃ x, lookup (⟨rStack, o⟩ : Addr Int)
      (K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) = .ok (some (.dat x (o % 4).toNat)) := by
  intro o h1 h2
  simp only [pushOk, List.all_eq_true, List.mem_range] at h
  have hi := h (o - lo).toNat (by omega)
  rw [show lo + ((o - lo).toNat : Int) = o by omega] at hi
  split at hi
  · rename_i x k hl
    simp only [beq_iff_eq] at hi
    have := lookup_hom e σ _ K.mem _ hl
    have ha : mapAddr σ (⟨rStack, Lin.ofInt o⟩ : Addr Lin) = ⟨rStack, o⟩ := by
      simp [mapAddr, Lin.ofInt, Lin.eval, dotC]
    rw [ha] at this
    refine ⟨x.eval e, ?_⟩
    rw [this, hi]; rfl
  · cases hi

/-! ## A cut that is an instance of another: general registers -/

/-- General registers of `w` are those of `v`, or numbers whose halves are variables of their own
location, where `v` holds a number. -/
def gprRel : Nat → List (Val E Lin) → List (Val E Lin) → Bool
  | _, [], [] => true
  | g, y :: ys, x :: xs =>
    (y == x || (match y, x with
      | .num a b, .num c d => (a == c || a == .var (.n (gId g 0))) && (b == d || b == .var (.n (gId g 1)))
      | _, _ => false)) && gprRel (g + 1) ys xs
  | _, _, _ => false

theorem absE_eval_gloc (env : Key → W32) (R : State E Lin) (g h : Nat) (lo hi : E)
    (hv : R.gpr[g]? = some (.num lo hi)) (hg : g < 50) (hh : h < 2) :
    E.eval (envAbs env R) (absE (gId g h) (if h = 0 then lo else hi)) = envAbs env R (.n (gId g h)) := by
  have h1 : gId g h < 100 := by simp only [gId]; omega
  have h3 : gId g h / 2 = g := by simp only [gId]; omega
  have h4 : gId g h % 2 = h := by simp only [gId]; omega
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
  · cases lo with
    | const c => simp only [absE, E.eval, envAbs, if_pos h1, h3, hv, h4, ite_true]
    | _ => rfl
  · cases hi with
    | const c => simp only [absE, E.eval, envAbs, if_pos h1, h3, hv, h4]; rfl
    | _ => rfl

theorem gpr_eval (env : Key → W32) (σ : Nat → Int) (R : State E Lin) (hc : CutOk R) :
    ∀ (g : Nat) (W vs : List (Val E Lin)), (∀ j, vs[j]? = R.gpr[g + j]?) →
      gprRel g W (mapI absVal g vs) = true →
      W.map (mapVal (envAbs env R) σ) = (mapI absVal g vs).map (mapVal (envAbs env R) σ)
  | _, [], [], _, _ => rfl
  | g, w :: ws, v :: vs, hj, h => by
    simp only [mapI, gprRel, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨hw, hr⟩ := h
    simp only [List.map_cons, mapI, List.cons.injEq]
    have hv : R.gpr[g]? = some v := by
      have h0 := hj 0
      simp only [List.getElem?_cons_zero, Nat.add_zero] at h0
      exact h0.symm
    have hg : g < 50 := by obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp hv; obtain ⟨hl, _⟩ := hc; omega
    refine ⟨?_, gpr_eval env σ R hc (g + 1) ws vs (fun j => by
      rw [show g + 1 + j = g + (j + 1) by omega, ← hj (j + 1)]; rfl) hr⟩
    rcases hw with hw | hw
    · rw [hw]
    · cases v with
      | ptr a => cases w <;> simp [absVal] at hw
      | num lo hi =>
        cases w with
        | ptr _ => simp [absVal] at hw
        | num a b =>
          simp only [absVal, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hw
          obtain ⟨ha, hb⟩ := hw
          simp only [mapVal, absVal, Val.num.injEq]
          constructor
          · rcases ha with ha | ha
            · rw [ha]
            · rw [ha]; exact (absE_eval_gloc env R g 0 lo hi hv hg (by decide)).symm
          · rcases hb with hb | hb
            · rw [hb]
            · rw [hb]; exact (absE_eval_gloc env R g 1 lo hi hv hg (by decide)).symm
  | _, [], _ :: _, _, h => by simp [mapI, gprRel] at h
  | _, _ :: _, [], _, h => by simp [mapI, gprRel] at h

/-- A slice's end cut denotes the same with lanes and register halves replaced by the variables of
their locations. -/
theorem mapState_inst (env : Key → W32) (σ : Nat → Int) (prog : Array Instr) (ro : Region)
    (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool) (n : Nat) (K K' : State E Lin) (trees : List (Nat × E))
    (hs : sliceCheck prog ro mem0 orc n K K' trees = true) (G : List (Val E Lin)) (W : List (List E))
    (hG : gprRel 0 G K'.gpr = true) (hW : vrRel 0 W K'.vr = true) :
    mapState (envAbs env (run prog ro mem0 orc n K)) σ K' =
      mapState (envAbs env (run prog ro mem0 orc n K)) σ { K' with gpr := G, vr := W } := by
  have hv := mapState_vrInst env σ prog ro mem0 orc n K K' trees hs W hW
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨_, hcut⟩, habs⟩, _⟩ := hs
  subst habs
  have hg := gpr_eval env σ _ hcut 0 G (run prog ro mem0 orc n K).gpr (fun j => by simp) hG
  rw [hv]
  simp only [mapState]
  simp only [abstract] at hg ⊢
  rw [hg]

end Hashtree.Asm.X86
