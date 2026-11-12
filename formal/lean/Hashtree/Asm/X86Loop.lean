import Hashtree.Asm.X86Frame
import Hashtree.Asm.X86Sym
import Hashtree.Asm.Subst

/-!
# Loop heads: restarting a proof at a cut reached again

The facts that let a proof of one loop iteration be reused for every iteration: older writes
(all in the output buffer) leave the well-formed initial memory well formed and act as part of
it (`X86Frame`); a cut reached again with advanced pointers is the loop-head cut under shifted
symbols (`Subst`); and the memory keys can always be re-read from memory (`ecomb`).
-/

namespace Hashtree.Asm.X86
open Hashtree.Asm Hashtree.Asm.X86Sym

/-! ## Logs that only hold output bytes -/

/-- Older writes: output bytes, or stack bytes below the entry stack offset `24` (the return address
stays untouched). -/
def OutLog (M : CLog) : Prop := ∀ p ∈ M, p.1.region = rOut ∨ (p.1.region = rStack ∧ p.1.off < 24)

theorem lookup_none_ne (a : Addr Int) : ∀ (M : CLog), (∀ p ∈ M, p.1 ≠ a) → lookup a M = .ok none
  | [], _ => rfl
  | (b, c) :: rest, h => by
    have hb : b ≠ a := h (b, c) (List.mem_cons_self ..)
    simp only [lookup, AddrEq.same]
    have : (a.region == b.region && a.off == b.off) = false := by
      obtain ⟨ra, oa⟩ := a
      obtain ⟨rb, ob⟩ := b
      simp only [ne_eq, Addr.mk.injEq] at hb
      by_cases hr : ra = rb
      · subst hr
        have : oa ≠ ob := fun h => hb ⟨rfl, h.symm⟩
        simp [this]
      · simp [hr]
    rw [this]
    exact lookup_none_ne a rest (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem view_other (M : CLog) (m : Addr Int → Cell W32 Int) (a : Addr Int) (ha : ∀ p ∈ M, p.1 ≠ a) :
    view M m a = m a := by
  simp only [view, lookup_none_ne a M ha]

theorem outLog_ne (M : CLog) (hM : OutLog M) (a : Addr Int)
    (ha : a.region ≠ rOut ∧ (a.region = rStack → 24 ≤ a.off)) : ∀ p ∈ M, p.1 ≠ a := by
  intro p hp heq
  rcases hM p hp with h | ⟨h1, h2⟩
  · rw [heq] at h; exact ha.1 h
  · rw [heq] at h1 h2; have := ha.2 h1; omega

theorem wf_view (rodata : List Nat) (m : Addr Int → Cell W32 Int) (M : CLog) (hM : OutLog M)
    (hw : WfMem 4 rodata 24 m) : WfMem 4 rodata 24 (view M m) := by
  obtain ⟨h1, h2, hro, hret, hin⟩ := hw
  have v4 : ∀ o, view M m ⟨4, o⟩ = m ⟨4, o⟩ := fun o =>
    view_other M m _ (outLog_ne M hM _ ⟨show (4 : Region) ≠ rOut by decide,
      fun h => absurd (show (4 : Region) = rStack from h) (by decide)⟩)
  have vI : ∀ o, view M m ⟨rIn, o⟩ = m ⟨rIn, o⟩ := fun o =>
    view_other M m _ (outLog_ne M hM _ ⟨show rIn ≠ rOut by decide,
      fun h => absurd (show rIn = rStack from h) (by decide)⟩)
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · intro o; rw [v4]; exact hro o
  · intro o a b
    rw [view_other M m _ (outLog_ne M hM _ ⟨show rStack ≠ rOut by decide, fun _ => by simp only; omega⟩)]
    exact hret o a b
  · intro o; rw [vI]; exact hin o

/-- Numbered variables from `e`, memory keys re-read from memory `m` under `σ`. -/
def ecomb (e : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) : Key → W32
  | .n i => e (.n i)
  | .m r off => cellX (m ⟨r, off.eval σ⟩)

theorem envMem_ecomb (e : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) : EnvMem (ecomb e σ m) σ m :=
  fun _ _ => rfl

end Hashtree.Asm.X86

namespace Hashtree.Asm

/-! ## States whose lanes only use numbered variables -/

def E.nOnly : E → Bool
  | .var (.n _) => true
  | .var (.m _ _) => false
  | .const _ => true
  | .add a b | .xor a b | .and a b | .or a b => a.nOnly && b.nOnly
  | .not a | .shl a _ | .shr a _ | .sar a _ | .ror a _ => a.nOnly
  | .tern _ a b c => a.nOnly && b.nOnly && c.nOnly

theorem E.eval_nOnly (e e' : Key → W32) (he : ∀ i, e (.n i) = e' (.n i)) :
    ∀ (x : E), x.nOnly = true → x.eval e = x.eval e'
  | .var (.n i), _ => he i
  | .var (.m _ _), h => by simp [E.nOnly] at h
  | .const _, _ => rfl
  | .add a b, h | .xor a b, h | .and a b, h | .or a b, h => by
    simp only [E.nOnly, Bool.and_eq_true] at h
    simp only [E.eval, E.eval_nOnly e e' he a h.1, E.eval_nOnly e e' he b h.2]
  | .not a, h | .shl a _, h | .shr a _, h | .sar a _, h | .ror a _, h => by
    simp only [E.nOnly] at h
    simp only [E.eval, E.eval_nOnly e e' he a h]
  | .tern _ a b c, h => by
    simp only [E.nOnly, Bool.and_eq_true] at h
    simp only [E.eval, E.eval_nOnly e e' he a h.1.1, E.eval_nOnly e e' he b h.1.2, E.eval_nOnly e e' he c h.2]

def Val.nOnly : Val E Lin → Bool
  | .num lo hi => lo.nOnly && hi.nOnly
  | .ptr _ => true

def Cell.nOnly : Cell E Lin → Bool
  | .dat x _ => x.nOnly
  | .pb _ _ => true

def State.nOnly (K : State E Lin) : Bool :=
  K.gpr.all Val.nOnly && K.vr.all (·.all E.nOnly) && K.mem.all (fun p => p.2.nOnly)

theorem mapState_nOnly (e e' : Key → W32) (σ : Nat → Int) (he : ∀ i, e (.n i) = e' (.n i))
    (K : State E Lin) (hK : K.nOnly = true) : mapState e σ K = mapState e' σ K := by
  simp only [State.nOnly, Bool.and_eq_true, List.all_eq_true] at hK
  obtain ⟨⟨hg, hv⟩, hm⟩ := hK
  simp only [mapState]
  congr 1
  · apply List.map_congr_left
    intro v hv'
    have := hg v hv'
    cases v with
    | num lo hi =>
      simp only [Val.nOnly, Bool.and_eq_true] at this
      simp only [mapVal, E.eval_nOnly e e' he lo this.1, E.eval_nOnly e e' he hi this.2]
    | ptr a => rfl
  · apply List.map_congr_left
    intro l hl
    apply List.map_congr_left
    intro x hx
    exact E.eval_nOnly e e' he x (hv l hl x hx)
  · apply List.map_congr_left
    intro p hp
    have := hm p hp
    obtain ⟨a, c⟩ := p
    cases c with
    | dat x k => simp only [Cell.nOnly] at this; simp only [mapCell, E.eval_nOnly e e' he x this]
    | pb _ _ => rfl

end Hashtree.Asm

namespace Hashtree.Asm.X86
open Hashtree.Asm Hashtree.Asm.X86Sym

/-! ## A cut reached again -/

theorem mapState_reached (e : Key → W32) (σ : Nat → Int) (K K0 : State E Lin) (τ : List Lin)
    (hs : { K with mem := [], assume := [] } = K0.substL τ) :
    mapState e σ K = fr (K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) (mapState e (sigmaOf τ σ) K0) := by
  have h := congrArg (mapState e σ) hs
  rw [mapState_subst] at h
  rw [← h]
  simp only [fr, mapState, List.map_nil, List.nil_append]

/-! ## Reading output bytes through a log of several parts -/

theorem lookup_none_off (a : Addr Int) (M : CLog) (h : ∀ p ∈ M, p.1 ≠ a) : lookup a M = .ok none :=
  lookup_none_ne a M h

theorem lookup_app_left (a : Addr Int) (L M : CLog) (c : Cell W32 Int) (h : lookup a L = .ok (some c)) :
    lookup a (L ++ M) = .ok (some c) := by
  rw [lookup_append, h]

theorem lookup_app_right (a : Addr Int) (L M : CLog) (h : ∀ p ∈ L, p.1 ≠ a) :
    lookup a (L ++ M) = lookup a M := by
  rw [lookup_append, lookup_none_off a L h]

/-! ## A cut that is an instance of another: constants for variables -/

/-- Lanes of `w` are those of `v`, or the variable of their own location. -/
def lanesRel (i : Nat) : Nat → List E → List E → Bool
  | _, [], [] => true
  | l, y :: ys, x :: xs => (y == x || y == .var (.n (vId i l))) && lanesRel i (l + 1) ys xs
  | _, _, _ => false

def vrRel : Nat → List (List E) → List (List E) → Bool
  | _, [], [] => true
  | i, w :: ws, v :: vs => lanesRel i 0 w v && vrRel (i + 1) ws vs
  | _, _, _ => false

theorem absE_eval_loc (env : Key → W32) (R : State E Lin) (i l : Nat) (v : List E) (x : E)
    (hv : R.vr[i]? = some v) (hx : v[l]? = some x) (hl : l < 16) (hi : i < 56) :
    E.eval (envAbs env R) (absE (vId i l) x) = envAbs env R (.n (vId i l)) := by
  have h1 : ¬ vId i l < 100 := by simp only [vId]; omega
  have h2 : vId i l < 1000 := by simp only [vId]; omega
  have h3 : (vId i l - 100) / 16 = i := by simp only [vId]; omega
  have h4 : (vId i l - 100) % 16 = l := by simp only [vId]; omega
  cases x with
  | const c =>
    simp only [absE, E.eval, envAbs, if_neg h1, if_pos h2, h3, h4, hv, List.getD_eq_getElem?_getD, hx,
      Option.getD_some]
  | _ => rfl

theorem lanes_eval (env : Key → W32) (R : State E Lin) (i : Nat) (hi : i < 56) (V : List E) (hv : R.vr[i]? = some V)
    (hV : V.length ≤ 16) : ∀ (l : Nat) (w v : List E), (∀ j, v[j]? = V[l + j]?) →
      lanesRel i l w (mapI (fun l x => absE (vId i l) x) l v) = true →
      w.map (E.eval (envAbs env R)) = (mapI (fun l x => absE (vId i l) x) l v).map (E.eval (envAbs env R))
  | _, [], [], _, _ => rfl
  | l, y :: ys, x :: xs, hj, h => by
    simp only [mapI, lanesRel, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨hy, hr⟩ := h
    simp only [List.map_cons, mapI, List.cons.injEq]
    have hx : V[l]? = some x := by
      have h0 := hj 0
      simp only [List.getElem?_cons_zero, Nat.add_zero] at h0
      exact h0.symm
    refine ⟨?_, lanes_eval env R i hi V hv hV (l + 1) ys xs (fun j => by
      rw [show l + 1 + j = l + (j + 1) by omega, ← hj (j + 1)]; rfl) hr⟩
    have hl : l < 16 := by
      obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hx; omega
    rcases hy with hy | hy
    · rw [hy]
    · rw [hy, absE_eval_loc env R i l V x hv hx hl hi]; rfl
  | _, [], _ :: _, _, h => by simp [mapI, lanesRel] at h
  | _, _ :: _, [], _, h => by simp [mapI, lanesRel] at h

theorem vr_eval (env : Key → W32) (R : State E Lin) (hc : CutOk R) : ∀ (i : Nat) (W vs : List (List E)),
    (∀ j, vs[j]? = R.vr[i + j]?) → vrRel i W (mapI absLanes i vs) = true →
      W.map (·.map (E.eval (envAbs env R))) = (mapI absLanes i vs).map (·.map (E.eval (envAbs env R)))
  | _, [], [], _, _ => rfl
  | i, w :: ws, v :: vs, hj, h => by
    simp only [mapI, vrRel, Bool.and_eq_true] at h
    obtain ⟨hw, hr⟩ := h
    simp only [List.map_cons, mapI, List.cons.injEq]
    have hv : R.vr[i]? = some v := by
      have h0 := hj 0
      simp only [List.getElem?_cons_zero, Nat.add_zero] at h0
      exact h0.symm
    obtain ⟨hlen, hvl, hl16⟩ := hc
    have hi : i < 56 := by obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hv; omega
    have hV : v.length ≤ 16 := hl16 v (List.mem_of_getElem? hv)
    refine ⟨lanes_eval env R i hi v hv hV 0 w v (fun j => by simp) hw,
      vr_eval env R ⟨hlen, hvl, hl16⟩ (i + 1) ws vs (fun j => by
        rw [show i + 1 + j = i + (j + 1) by omega, ← hj (j + 1)]; rfl) hr⟩
  | _, [], _ :: _, _, h => by simp [mapI, vrRel] at h
  | _, _ :: _, [], _, h => by simp [mapI, vrRel] at h

/-- A slice's end cut denotes the same with any lanes replaced by the variables of their locations. -/
theorem mapState_vrInst (env : Key → W32) (σ : Nat → Int) (prog : Array Instr) (ro : Region)
    (mem0 : Addr Lin → Cell E Lin) (orc : Nat → Bool) (n : Nat) (K K' : State E Lin) (trees : List (Nat × E))
    (hs : sliceCheck prog ro mem0 orc n K K' trees = true) (W : List (List E)) (hW : vrRel 0 W K'.vr = true) :
    mapState (envAbs env (run prog ro mem0 orc n K)) σ K' =
      mapState (envAbs env (run prog ro mem0 orc n K)) σ { K' with vr := W } := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨_, hcut⟩, habs⟩, _⟩ := hs
  subst habs
  have := vr_eval env _ hcut 0 W (run prog ro mem0 orc n K).vr (fun j => by simp) hW
  simp only [mapState]
  simp only [abstract] at this ⊢
  rw [this]

end Hashtree.Asm.X86
