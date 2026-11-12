import Hashtree.Asm.Arm
import Hashtree.Asm.Hom

/-!
# Soundness of the symbolic AArch64 model: helpers

The pure helpers of `Arm.lean` (lane operations, shuffles, SHA-256 instructions) and the
state-level helpers (register reads and writes, addressing, loads and stores) commute with
evaluation.  `ArmExec.lean` lifts this to every instruction.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Asm.Arm
open Hashtree.Asm

/-! ## `Except` plumbing -/

theorem ok_of_pure {β : Type} {x y : β} (h : (pure x : Except String β) = .ok y) : x = y := by
  simpa [pure, Except.pure] using h

theorem pure_ok {β : Type} (x : β) : (pure x : Except String β) = .ok x := rfl

theorem throw_eq {β : Type} (e : String) : (throw e : Except String β) = .error e := rfl

/-- `(do let x ← m; f x) = .ok r` with `m = .ok a`. -/
theorem bind_ok {β δ : Type} {m : Except String β} {f : β → Except String δ} {r : δ} (h : (m >>= f) = .ok r) :
    ∃ a, m = .ok a ∧ f a = .ok r := by
  cases hm : m with
  | error e => rw [hm] at h; cases h
  | ok a => rw [hm] at h; exact ⟨a, rfl, h⟩

section Pure
variable (env : Key → W32)

local notation "ev" => E.eval env

theorem lane_hom (v : List E) (i : Nat) : ev (lane v i) = lane (v.map ev) i := by
  simp only [lane, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases v[i]? <;> rfl

@[simp] theorem zeroLanes_ev (n : Nat) : (zeroLanes n : List E).map ev = (zeroLanes n : List W32) := by
  simp [zeroLanes, List.map_replicate]

theorem vop_hom (op : VOp) (a b : E) : ev (vop op a b) = vop op (ev a) (ev b) := by
  cases op <;> simp [vop]

theorem wop_hom (op : WOp) (a b : E) : ev (wop op a b) = wop op (ev a) (ev b) := by
  cases op <;> simp [wop]

theorem zipWith_hom (f : E → E → E) (g : W32 → W32 → W32) (hf : ∀ a b, ev (f a b) = g (ev a) (ev b)) :
    ∀ (a b : List E), (List.zipWith f a b).map ev = List.zipWith g (a.map ev) (b.map ev)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
    simp only [List.zipWith_cons_cons, List.map_cons, hf]
    rw [zipWith_hom f g hf xs ys]

theorem shl32_hom (x : E) (k : Nat) : ev (shl32 x k) = shl32 (ev x) k := by
  simp only [shl32]; split <;> simp

theorem shr32_hom (x : E) (k : Nat) : ev (shr32 x k) = shr32 (ev x) k := by
  simp only [shr32]; split <;> simp

theorem shl64_hom (lo hi : E) (k : Nat) :
    (ev (shl64 lo hi k).1, ev (shl64 lo hi k).2) = shl64 (ev lo) (ev hi) k := by
  simp only [shl64]
  split
  · rfl
  · split
    · simp
    · split
      · simp [shl32_hom]
      · simp

theorem shr64_hom (lo hi : E) (k : Nat) :
    (ev (shr64 lo hi k).1, ev (shr64 lo hi k).2) = shr64 (ev lo) (ev hi) k := by
  simp only [shr64]
  split
  · rfl
  · split
    · simp
    · split
      · simp [shr32_hom]
      · simp

theorem shl64_fst (lo hi : E) (k : Nat) : ev (shl64 lo hi k).1 = (shl64 (ev lo) (ev hi) k).1 := by
  rw [← shl64_hom]
theorem shl64_snd (lo hi : E) (k : Nat) : ev (shl64 lo hi k).2 = (shl64 (ev lo) (ev hi) k).2 := by
  rw [← shl64_hom]
theorem shr64_fst (lo hi : E) (k : Nat) : ev (shr64 lo hi k).1 = (shr64 (ev lo) (ev hi) k).1 := by
  rw [← shr64_hom]
theorem shr64_snd (lo hi : E) (k : Nat) : ev (shr64 lo hi k).2 = (shr64 (ev lo) (ev hi) k).2 := by
  rw [← shr64_hom]

theorem vbyte_hom (v : List E) (j : Nat) : ev (vbyte v j) = vbyte (v.map ev) j := by
  simp only [vbyte, eval_byteOf, lane_hom]

theorem ofBytes_hom (a b c d : E) : ev (ofBytes a b c d) = ofBytes (ev a) (ev b) (ev c) (ev d) := by
  simp [ofBytes]

theorem bswap_hom (x : E) : ev (bswap x) = bswap (ev x) := by
  simp only [bswap, ofBytes_hom, eval_byteOf]

theorem extL_hom (n m : List E) (imm : Nat) : (extL n m imm).map ev = extL (n.map ev) (m.map ev) imm := by
  simp only [extL]
  split
  · simp only [List.map_map, Function.comp_def]
    congr 1; funext i
    split <;> simp only [lane_hom]
  · simp only [List.map_map, Function.comp_def, ofBytes_hom]
    congr 1; funext i
    congr 1 <;> (split <;> (try split) <;> simp [vbyte_hom])

/-! ### SHA-256 instructions -/

/-- Evaluation of a pair of lane lists. -/
def pmap (xy : List E × List E) : List W32 × List W32 := (xy.1.map ev, xy.2.map ev)

theorem shaStep_hom (xy : List E × List E) (w : E) : pmap env (shaStep xy w) = shaStep (pmap env xy) (ev w) := by
  simp [shaStep, pmap, lane_hom, shaChoose, shaMajority, shaSigma0, shaSigma1]

theorem foldl_shaStep_hom : ∀ (l : List E) (xy : List E × List E),
    pmap env (l.foldl shaStep xy) = (l.map ev).foldl shaStep (pmap env xy)
  | [], _ => rfl
  | w :: ws, xy => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_shaStep_hom ws, shaStep_hom]

theorem sha256hash_hom (x y w : List E) (p : Bool) :
    (sha256hash x y w p).map ev = sha256hash (x.map ev) (y.map ev) (w.map ev) p := by
  have h := foldl_shaStep_hom env [lane w 0, lane w 1, lane w 2, lane w 3] (x, y)
  simp only [List.map_cons, List.map_nil, lane_hom] at h
  cases p
  · simp only [sha256hash, Bool.false_eq_true, ite_false]
    exact congrArg Prod.snd h
  · simp only [sha256hash, ite_true]
    exact congrArg Prod.fst h

theorem su0_hom (d n : List E) : (su0 d n).map ev = su0 (d.map ev) (n.map ev) := by
  simp only [su0, List.map_map, Function.comp_def]
  congr 1; funext e
  simp [ssig0, lane_hom]

theorem su1_hom (d n m : List E) : (su1 d n m).map ev = su1 (d.map ev) (n.map ev) (m.map ev) := by
  simp [su1, ssig1, lane_hom]

end Pure

/-! ## State-level helpers -/

section St
variable (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin) (mem0c : Addr Int → Cell W32 Int)

local notation "ev" => E.eval env

theorem getQ_hom (s : State E Lin) (i : Nat) : getQ (mapState env σ s) i = (getQ s i).map ev := by
  simp only [getQ, getV_hom, List.map_cons, List.map_nil, lane_hom]

theorem getD_hom (s : State E Lin) (i : Nat) : getD (mapState env σ s) i = (getD s i).map ev := by
  simp only [getD, getV_hom, List.map_cons, List.map_nil, lane_hom]

theorem setQ_hom (s : State E Lin) (d : Nat) (v : List E) :
    mapState env σ (setQ s d v) = setQ (mapState env σ s) d (v.map ev) := by
  simp only [setQ, setV_hom, List.map_append, List.map_cons, List.map_nil, lane_hom, zeroLanes_ev]

theorem setD_hom (s : State E Lin) (d : Nat) (v : List E) :
    mapState env σ (setD s d v) = setD (mapState env σ s) d (v.map ev) := by
  simp only [setD, setV_hom, List.map_append, List.map_cons, List.map_nil, lane_hom, zeroLanes_ev]

theorem setW_hom (s : State E Lin) (d : Nat) (x : E) :
    mapState env σ (setW s d x) = setW (mapState env σ s) d (ev x) := by
  simp [setW, setG_hom, mapVal]

theorem setFlags_hom (s : State E Lin) (a b : Lin) :
    mapState env σ (setFlags s a b) = setFlags (mapState env σ s) (a.eval σ) (b.eval σ) := rfl

theorem halt_hom (s : State E Lin) : mapState env σ (halt s) = halt (mapState env σ s) := rfl

theorem getW_hom (s : State E Lin) (i : Nat) (x : E) (h : getW s i = .ok x) :
    getW (mapState env σ s) i = .ok (ev x) := by
  unfold getW at h ⊢
  by_cases hi : i = sp
  · rw [if_pos hi] at h; cases h
  rw [if_neg hi] at h; rw [if_neg hi, getG_hom]
  cases hg : s.getG i with
  | num lo hi => rw [hg] at h; simp only [pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; rfl
  | ptr q =>
    rw [hg] at h
    obtain ⟨rq, n⟩ := q
    cases rq with
    | zero =>
      simp only [mapVal, mapAddr] at h ⊢
      cases hn : (Ctl.asInt n : Option Int) with
      | none => rw [hn] at h; cases h
      | some v =>
        rw [hn] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
        subst h
        simp [Lin.eval_asInt σ n v hn]
    | succ _ => cases h

theorem getX_hom (s : State E Lin) (i : Nat) (p : E × E) (h : getX s i = .ok p) :
    getX (mapState env σ s) i = .ok (ev p.1, ev p.2) := by
  unfold getX at h ⊢
  by_cases hi : i = sp
  · rw [if_pos hi] at h; cases h
  rw [if_neg hi] at h; rw [if_neg hi, getG_hom]
  cases hg : s.getG i with
  | num lo hi => rw [hg] at h; simp only [pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; rfl
  | ptr q =>
    rw [hg] at h
    obtain ⟨rq, n⟩ := q
    cases rq with
    | zero =>
      simp only [mapVal, mapAddr] at h ⊢
      cases hn : (Ctl.asInt n : Option Int) with
      | none => rw [hn] at h; cases h
      | some v =>
        rw [hn] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
        subst h
        simp [Lin.eval_asInt σ n v hn]
    | succ _ => cases h

theorem getC_hom (s : State E Lin) (i : Nat) (a : Addr Lin) (h : getC s i = .ok a) :
    getC (mapState env σ s) i = .ok (mapAddr σ a) := by
  unfold getC at h ⊢
  rw [getG_hom]
  cases hg : s.getG i with
  | ptr q => rw [hg] at h; dsimp only at h; simp only [pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; rfl
  | num lo hi =>
    rw [hg] at h
    dsimp only at h
    simp only [mapVal]
    cases hl : (Lane.asConst lo : Option W32) with
    | none => rw [hl] at h; cases h
    | some l =>
      cases hh : (Lane.asConst hi : Option W32) with
      | none => rw [hl, hh] at h; cases h
      | some hv =>
        rw [hl, hh] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
        subst h
        simp [eval_asConst env lo l hl, eval_asConst env hi hv hh, mapAddr]

theorem baseAddr_hom (s : State E Lin) (n : Nat) (a : Addr Lin) (h : baseAddr s n = .ok a) :
    baseAddr (mapState env σ s) n = .ok (mapAddr σ a) := by
  unfold baseAddr at h ⊢
  rw [getG_hom]
  cases hg : s.getG n with
  | num _ _ => rw [hg] at h; cases h
  | ptr q =>
    rw [hg] at h
    simp only [mapVal]
    dsimp only at h ⊢
    have hreg : (mapAddr σ q).region = q.region := rfl
    rw [hreg]
    by_cases hr : q.region = rNum
    · rw [if_pos hr] at h; cases h
    rw [if_neg hr] at h; rw [if_neg hr]
    by_cases hs : n = sp
    · rw [if_pos hs] at h; rw [if_pos hs]
      cases ho : (Ctl.asInt q.off : Option Int) with
      | none => rw [ho] at h; cases h
      | some o =>
        rw [ho] at h
        have hoff : (Ctl.asInt (mapAddr σ q).off : Option Int) = some o := by
          simp [mapAddr, Lin.eval_asInt σ _ o ho]
        rw [hoff]
        dsimp only at h ⊢
        by_cases h16 : o % 16 = 0
        · rw [if_pos h16] at h; rw [if_pos h16]
          simp only [pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; rfl
        · rw [if_neg h16] at h; cases h
    · rw [if_neg hs] at h; rw [if_neg hs]
      simp only [pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; rfl

theorem addrWB_hom (s : State E Lin) (n : Nat) (i : Idx) (aw : Addr Lin × Option (Addr Lin))
    (h : addrWB s n i = .ok aw) :
    addrWB (mapState env σ s) n i = .ok (mapAddr σ aw.1, aw.2.map (mapAddr σ)) := by
  unfold addrWB at h ⊢
  cases hb : baseAddr s n with
  | error e => rw [hb] at h; cases h
  | ok b =>
    rw [hb] at h
    rw [baseAddr_hom env σ s n b hb]
    dsimp only at h ⊢
    cases i with
    | off k => cases h; simp [mapAddr_plusI]
    | pre k => cases h; simp [mapAddr_plusI]
    | post k => cases h; simp [mapAddr_plusI]
    | postR m =>
      dsimp only at h ⊢
      by_cases hm : m = sp
      · rw [if_pos hm] at h; cases h
      rw [if_neg hm] at h; rw [if_neg hm]
      cases hc : getC s m with
      | error e => rw [hc] at h; cases h
      | ok x =>
        rw [hc] at h
        rw [getC_hom env σ s m x hc]
        dsimp only at h ⊢
        by_cases hr : x.region = rNum
        · rw [if_pos hr] at h
          rw [if_pos (show (mapAddr σ x).region = rNum from hr)]
          cases h; dsimp only; rw [Option.map_some, mapAddr_plus]; rfl
        · rw [if_neg hr] at h; cases h

theorem writeBack_hom (s : State E Lin) (n : Nat) (w : Option (Addr Lin)) :
    mapState env σ (writeBack s n w) = writeBack (mapState env σ s) n (w.map (mapAddr σ)) := by
  cases w with
  | none => rfl
  | some a => simp [writeBack, setG_hom, mapVal]

theorem loadReg_hom (h0 : Mem0Rel env σ mem0s mem0c) (s0 s : State E Lin) (sz : Sz) (t : Nat) (a : Addr Lin)
    (r : State E Lin) (h : loadReg mem0s s0 s sz t a = .ok r) :
    loadReg mem0c (mapState env σ s0) (mapState env σ s) sz t (mapAddr σ a) = .ok (mapState env σ r) := by
  cases sz with
  | w =>
    simp only [loadReg] at h ⊢
    by_cases ht : t = sp
    · rw [if_pos ht] at h; cases h
    rw [if_neg ht] at h; rw [if_neg ht]
    obtain ⟨x, hx, h⟩ := bind_ok h
    rw [loadLane_hom env σ mem0s mem0c h0 s0 a x hx, ok_bind]
    have := ok_of_pure h; subst this
    rw [setW_hom]; rfl
  | x =>
    simp only [loadReg] at h ⊢
    by_cases ht : t = sp
    · rw [if_pos ht] at h; cases h
    rw [if_neg ht] at h; rw [if_neg ht]
    obtain ⟨v, hv, h⟩ := bind_ok h
    rw [loadVal_hom env σ mem0s mem0c h0 s0 a v hv, ok_bind]
    have := ok_of_pure h; subst this
    rw [setG_hom]; rfl
  | d =>
    simp only [loadReg] at h ⊢
    obtain ⟨v, hv, h⟩ := bind_ok h
    rw [loadLanes_hom env σ mem0s mem0c h0 s0 2 a v hv, ok_bind]
    have := ok_of_pure h; subst this
    rw [setD_hom]; rfl
  | q =>
    simp only [loadReg] at h ⊢
    obtain ⟨v, hv, h⟩ := bind_ok h
    rw [loadLanes_hom env σ mem0s mem0c h0 s0 4 a v hv, ok_bind]
    have := ok_of_pure h; subst this
    rw [setQ_hom]; rfl

theorem storeReg_hom (s0 s : State E Lin) (sz : Sz) (t : Nat) (a : Addr Lin)
    (r : State E Lin) (h : storeReg s0 s sz t a = .ok r) :
    storeReg (mapState env σ s0) (mapState env σ s) sz t (mapAddr σ a) = .ok (mapState env σ r) := by
  cases sz with
  | w =>
    unfold storeReg at h ⊢
    obtain ⟨x, hx, h⟩ := bind_ok h
    rw [getW_hom env σ s0 t x hx, ok_bind]
    have := ok_of_pure h; subst this
    rw [storeLane_hom]; rfl
  | x =>
    unfold storeReg at h ⊢
    by_cases ht : t = sp
    · rw [if_pos ht] at h; cases h
    rw [if_neg ht] at h; rw [if_neg ht]
    have := ok_of_pure h; subst this
    rw [storeVal_hom, getG_hom]; rfl
  | d =>
    unfold storeReg at h ⊢
    have := ok_of_pure h; subst this
    rw [storeLanes_hom, getD_hom]; rfl
  | q =>
    unfold storeReg at h ⊢
    have := ok_of_pure h; subst this
    rw [storeLanes_hom, getQ_hom]; rfl

theorem ld1Step_hom (h0 : Mem0Rel env σ mem0s mem0c) (s : State E Lin) (a : Addr Lin) (t : Nat)
    (st : State E Lin) (j : Nat) (r : State E Lin) (h : ld1Step mem0s s a t st j = .ok r) :
    ld1Step mem0c (mapState env σ s) (mapAddr σ a) t (mapState env σ st) j = .ok (mapState env σ r) := by
  unfold ld1Step at h ⊢
  obtain ⟨v, hv, h⟩ := bind_ok h
  rw [← mapAddr_plusI, loadLanes_hom env σ mem0s mem0c h0 s 4 _ v hv, ok_bind]
  have := ok_of_pure h; subst this
  rw [setQ_hom]; rfl

theorem ld4Step_hom (h0 : Mem0Rel env σ mem0s mem0c) (s : State E Lin) (a : Addr Lin) (t e : Nat)
    (st : State E Lin) (j : Nat) (r : State E Lin) (h : ld4Step mem0s s a t e st j = .ok r) :
    ld4Step mem0c (mapState env σ s) (mapAddr σ a) t e (mapState env σ st) j = .ok (mapState env σ r) := by
  unfold ld4Step at h ⊢
  obtain ⟨x, hx, h⟩ := bind_ok h
  rw [← mapAddr_plusI, loadLane_hom env σ mem0s mem0c h0 s _ x hx, ok_bind]
  have := ok_of_pure h; subst this
  rw [setQ_hom, List.map_set, getQ_hom]; rfl

theorem st1Step_hom (s : State E Lin) (a : Addr Lin) (t : Nat) (st : State E Lin) (j : Nat) :
    mapState env σ (st1Step s a t st j) = st1Step (mapState env σ s) (mapAddr σ a) t (mapState env σ st) j := by
  simp only [st1Step, storeLanes_hom, getQ_hom, mapAddr_plusI]

theorem st4Step_hom (s : State E Lin) (a : Addr Lin) (t e : Nat) (st : State E Lin) (j : Nat) :
    mapState env σ (st4Step s a t e st j) = st4Step (mapState env σ s) (mapAddr σ a) t e (mapState env σ st) j := by
  simp only [st4Step, storeLane_hom, getQ_hom, lane_hom, mapAddr_plusI]

theorem foldlM_hom {β : Type} (F : State E Lin → β → Except String (State E Lin))
    (G : State W32 Int → β → Except String (State W32 Int))
    (hFG : ∀ st j r, F st j = .ok r → G (mapState env σ st) j = .ok (mapState env σ r)) :
    ∀ (l : List β) (init r : State E Lin), l.foldlM F init = .ok r →
      l.foldlM G (mapState env σ init) = .ok (mapState env σ r)
  | [], init, r, h => by
    simp only [List.foldlM_nil] at h ⊢
    have := ok_of_pure h; subst this; rfl
  | j :: l, init, r, h => by
    simp only [List.foldlM_cons] at h ⊢
    obtain ⟨s1, h1, h⟩ := bind_ok h
    rw [hFG init j s1 h1, ok_bind]
    exact foldlM_hom F G hFG l s1 r h

theorem foldl_hom {β : Type} (F : State E Lin → β → State E Lin) (G : State W32 Int → β → State W32 Int)
    (hFG : ∀ st j, mapState env σ (F st j) = G (mapState env σ st) j) :
    ∀ (l : List β) (init : State E Lin), mapState env σ (l.foldl F init) = l.foldl G (mapState env σ init)
  | [], _ => rfl
  | j :: l, init => by
    simp only [List.foldl_cons]
    rw [foldl_hom F G hFG l, hFG]

theorem ccCond_hom (c : CC) (a b : Lin) : mapCond σ (ccCond c a b) = ccCond c (a.eval σ) (b.eval σ) := by
  cases c <;> rfl

end St

end Hashtree.Asm.Arm
