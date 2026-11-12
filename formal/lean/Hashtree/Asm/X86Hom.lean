import Hashtree.Asm.X86
import Hashtree.Asm.Hom

/-!
# Soundness of the symbolic x86 model

Every x86 instruction commutes with evaluation (`exec_hom`): running the symbolic machine and
evaluating the result is running the concrete machine on the evaluated state, whenever the
symbolic step does not fail and its recorded branch conditions hold.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Hashtree.Asm.X86
open Hashtree.Asm

section Pure
variable (env : Key → W32)

local notation "ev" => E.eval env

theorem getD_map_ev (l : List E) (i : Nat) : (l.map ev).getD i (Lane.const 0 : W32) = ev (l.getD i (Lane.const 0)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

@[simp] theorem opt_getD_map_ev (o : Option E) : (Option.map ev o).getD (0#32) = ev (o.getD (Lane.const 0)) := by
  cases o <;> rfl
@[simp] theorem opt_getD_map_ev' (o : Option E) : (Option.map ev o).getD 0 = ev (o.getD (Lane.const 0)) := by
  cases o <;> rfl

theorem take_map_ev (l : List E) (n : Nat) : (l.map ev).take n = (l.take n).map ev := (List.map_take ..).symm
theorem drop_map_ev (l : List E) (n : Nat) : (l.map ev).drop n = (l.drop n).map ev := (List.map_drop ..).symm

@[simp] theorem zeroLanes_ev (n : Nat) : (zeroLanes n : List E).map ev = (zeroLanes n : List W32) := by
  simp [zeroLanes, List.map_replicate]

theorem lop_hom (op : LOp) (a b : E) : ev (lop op a b) = lop op (ev a) (ev b) := by
  cases op <;> simp [lop]

theorem lanes2_hom (f : E → E → E) (g : W32 → W32 → W32) (hf : ∀ a b, ev (f a b) = g (ev a) (ev b)) :
    ∀ (a b : List E), (lanes2 f a b).map ev = lanes2 g (a.map ev) (b.map ev)
  | [], _ => by simp [lanes2]
  | _ :: _, [] => by simp [lanes2]
  | x :: xs, y :: ys => by
    have ih := lanes2_hom f g hf xs ys
    simp only [lanes2, List.zipWith_cons_cons, List.map_cons, hf] at ih ⊢
    rw [ih]

theorem lanes3_hom (f : E → E → E → E) (g : W32 → W32 → W32 → W32)
    (hf : ∀ a b c, ev (f a b c) = g (ev a) (ev b) (ev c)) :
    ∀ (a b c : List E), (lanes3 f a b c).map ev = lanes3 g (a.map ev) (b.map ev) (c.map ev)
  | [], _, _ => by simp [lanes3]
  | _ :: _, [], _ => by simp [lanes3]
  | _ :: _, _ :: _, [] => by simp [lanes3]
  | x :: xs, y :: ys, z :: zs => by
    simp only [lanes3, List.map_cons, hf]
    exact congrArg _ (lanes3_hom f g hf xs ys zs)

theorem shiftL_hom (k : Shift) (x : E) (n : Nat) : ev (shiftL k x n) = shiftL k (ev x) n := by
  cases k <;> simp only [shiftL] <;> (try split) <;> simp

theorem shrQ_hom (lo hi : E) (n : Nat) :
    (ev (shrQ lo hi n).1, ev (shrQ lo hi n).2) = shrQ (ev lo) (ev hi) n := by
  simp only [shrQ]
  split
  · rfl
  · split
    · simp
    · split <;> simp

theorem pairs_unpairs_hom (f : E × E → E × E) (g : W32 × W32 → W32 × W32)
    (hf : ∀ p, (ev (f p).1, ev (f p).2) = g (ev p.1, ev p.2)) :
    ∀ (l : List E), (unpairs ((pairs l).map f)).map ev = unpairs ((pairs (l.map ev)).map g)
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp only [pairs, List.map_cons, unpairs]
    rw [← hf (a, b)]
    exact congrArg _ (congrArg _ (pairs_unpairs_hom f g hf rest))

theorem vbyte_hom (v : List E) (g j : Nat) : ev (vbyte v g j) = vbyte (v.map ev) g j := by
  simp only [vbyte, eval_byteOf, getD_map_ev]

theorem ofBytes_hom (a b c d : E) : ev (ofBytes a b c d) = ofBytes (ev a) (ev b) (ev c) (ev d) := by
  simp [ofBytes]

theorem catByte_hom (hi lo : List E) (j : Nat) : ev (catByte hi lo j) = catByte (hi.map ev) (lo.map ev) j := by
  simp only [catByte]
  split
  · exact vbyte_hom env lo 0 j
  · split
    · exact vbyte_hom env hi 0 _
    · rfl

theorem palignrL_hom (hi lo : List E) (imm : Nat) :
    (palignrL hi lo imm).map ev = palignrL (hi.map ev) (lo.map ev) imm := by
  simp only [palignrL]
  split
  · simp only [List.map_map, Function.comp_def]
    congr 1; funext i
    split
    · exact (getD_map_ev env lo _).symm
    · split
      · exact (getD_map_ev env hi _).symm
      · rfl
  · simp only [List.map_map, Function.comp_def, ofBytes_hom, catByte_hom]

theorem pblendwL_hom (d s : List E) (imm : Nat) :
    (pblendwL d s imm).map ev = pblendwL (d.map ev) (s.map ev) imm := by
  simp only [pblendwL, List.map_map, Function.comp_def]
  congr 1; funext i
  simp only [getD_map_ev]
  split
  · rfl
  · split
    · rfl
    · split <;> simp

theorem rnds2_hom (d s k : List E) : (rnds2 d s k).map ev = rnds2 (d.map ev) (s.map ev) (k.map ev) := by
  simp [rnds2, getD_map_ev, chF, majF, bsig0, bsig1, rotr]

theorem msg1_hom (d s : List E) : (msg1 d s).map ev = msg1 (d.map ev) (s.map ev) := by
  simp [msg1, getD_map_ev, ssig0, rotr]

theorem msg2_hom (d s : List E) : (msg2 d s).map ev = msg2 (d.map ev) (s.map ev) := by
  simp [msg2, getD_map_ev, ssig1, rotr]

theorem constsOf_hom : ∀ (l : List E) (ms : List W32), constsOf l = .ok ms → constsOf (l.map ev) = .ok ms
  | [], ms, h => by simpa [constsOf] using h
  | x :: xs, ms, h => by
    simp only [constsOf] at h
    cases hx : (Lane.asConst x : Option W32) with
    | none => rw [hx] at h; cases h
    | some v =>
      rw [hx] at h
      cases hr : constsOf xs with
      | error e => rw [hr] at h; cases h
      | ok vs =>
        rw [hr] at h
        simp only [Except.ok.injEq] at h
        subst h
        simp only [List.map_cons, constsOf, W32_asConst, eval_asConst env x v hx, constsOf_hom xs vs hr]

theorem ctlLanes_hom (v : List E) (w : Nat) (ms : List W32) (h : ctlLanes v w = .ok ms) :
    ctlLanes (v.map ev) w = .ok ms := by
  simp only [ctlLanes] at h ⊢
  have := constsOf_hom env _ ms h
  simp only [List.map_map, Function.comp_def] at this
  simpa [getD_map_ev] using this

theorem pshufbP_hom (v : List E) (ms : List W32) : (pshufbP v ms).map ev = pshufbP (v.map ev) ms := by
  simp only [pshufbP, List.map_map, Function.comp_def, ofBytes_hom]
  congr 1; funext i
  congr 1 <;> (split <;> simp [vbyte_hom])

theorem pshufbL_hom (v mask : List E) (w : Nat) (r : List E) (h : pshufbL v mask w = .ok r) :
    pshufbL (v.map ev) (mask.map ev) w = .ok (r.map ev) := by
  simp only [pshufbL] at h ⊢
  cases hm : ctlLanes mask w with
  | error e => rw [hm] at h; cases h
  | ok ms =>
    rw [hm] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [ctlLanes_hom env mask w ms hm]
    simp only [bind, Except.bind, pure, Except.pure, pshufbP_hom]

theorem permi2dP_hom (a b : List E) (idx : List W32) :
    (permi2dP a b idx).map ev = permi2dP (a.map ev) (b.map ev) idx := by
  simp only [permi2dP, List.map_map, Function.comp_def]
  congr 1; funext k
  split <;> simp [getD_map_ev]

theorem permi2qP_hom (a b : List E) (idx : List W32) :
    (permi2qP a b idx).map ev = permi2qP (a.map ev) (b.map ev) idx := by
  simp only [permi2qP, List.map_flatten, List.map_map, Function.comp_def]
  congr 2; funext q
  split <;> simp [getD_map_ev]

end Pure

/-! ## State-level helpers -/

section St
variable (env : Key → W32) (σ : Nat → Int) (mem0s : Addr Lin → Cell E Lin) (mem0c : Addr Int → Cell W32 Int)

local notation "ev" => E.eval env

theorem setVec_hom (s : State E Lin) (vex : Bool) (w d : Nat) (v : List E) :
    mapState env σ (setVec s vex w d v) = setVec (mapState env σ s) vex w d (v.map ev) := by
  simp only [setVec, setV_hom, getV_hom]
  congr 1
  split <;> simp only [List.map_append, List.map_take, List.map_drop, zeroLanes_ev, getV_hom]

theorem regPtr_hom (s : State E Lin) (r : Nat) (a : Addr Lin) (h : regPtr s r = .ok a) :
    regPtr (mapState env σ s) r = .ok (mapAddr σ a) := by
  simp only [regPtr, getG_hom] at h ⊢
  cases hg : s.getG r with
  | num _ _ => rw [hg] at h; cases h
  | ptr q => rw [hg] at h; cases h; rfl

theorem baseAddr_hom (ro : Region) (s : State E Lin) (m : MemRef) (a : Addr Lin)
    (h : baseAddr ro s m = .ok a) : baseAddr ro (mapState env σ s) m = .ok (mapAddr σ a) := by
  simp only [baseAddr] at h ⊢
  cases hro : m.ro with
  | some o => rw [hro] at h; cases h; simp [mapAddr]
  | none =>
    rw [hro] at h
    cases hb : m.base with
    | some b => rw [hb] at h; exact regPtr_hom env σ s b a h
    | none => rw [hb] at h; cases h; simp [mapAddr]

theorem effAddr_hom (ro : Region) (s : State E Lin) (m : MemRef) (a : Addr Lin)
    (h : effAddr ro s m = .ok a) : effAddr ro (mapState env σ s) m = .ok (mapAddr σ a) := by
  simp only [effAddr] at h ⊢
  cases hb : baseAddr ro s m with
  | error e => rw [hb] at h; cases h
  | ok b =>
    rw [hb] at h
    rw [baseAddr_hom env σ ro s m b hb]
    dsimp only at h ⊢
    cases hi : m.index with
    | none => rw [hi] at h; cases h; dsimp only; rw [mapAddr_plusI]
    | some i =>
      rw [hi] at h
      dsimp only at h ⊢
      rw [getG_hom]
      cases hg : s.getG i with
      | num _ _ => rw [hg] at h; cases h
      | ptr q =>
        rw [hg] at h
        obtain ⟨rq, n⟩ := q
        cases rq with
        | zero =>
          cases h
          simp [mapVal, mapAddr, Addr.plusI, Addr.plus, Lin.eval_smul, Lin.eval_add]
        | succ _ => cases h

theorem readVSrc_hom (h0 : Mem0Rel env σ mem0s mem0c) (ro : Region) (s : State E Lin) (w : Nat) (src : VSrc)
    (r : List E) (h : readVSrc ro mem0s s w src = .ok r) :
    readVSrc ro mem0c (mapState env σ s) w src = .ok (r.map ev) := by
  cases src with
  | reg i =>
    simp only [readVSrc, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; rw [getV_hom, take_map_ev]
  | mem m =>
    simp only [readVSrc] at h ⊢
    cases ha : effAddr ro s m with
    | error e => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h
      simp only [bind, Except.bind] at h
      rw [effAddr_hom env σ ro s m a ha]
      simp only [bind, Except.bind]
      exact loadLanes_hom env σ mem0s mem0c h0 s w a r h

theorem gData32_hom (h0 : Mem0Rel env σ mem0s mem0c) (ro : Region) (s : State E Lin) (src : GSrc) (x : E)
    (h : gData32 ro mem0s s src = .ok x) : gData32 ro mem0c (mapState env σ s) src = .ok (ev x) := by
  cases src with
  | reg i =>
    simp only [gData32] at h ⊢
    rw [getG_hom]
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
  | imm v => simp only [gData32, pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; rfl
  | mem m =>
    simp only [gData32] at h ⊢
    cases ha : effAddr ro s m with
    | error e => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h
      simp only [bind, Except.bind] at h
      rw [effAddr_hom env σ ro s m a ha]
      simp only [bind, Except.bind]
      exact loadLane_hom env σ mem0s mem0c h0 s a x h

theorem gCtl_hom (s : State E Lin) (src : GSrc) (a : Addr Lin) (h : gCtl s src = .ok a) :
    gCtl (mapState env σ s) src = .ok (mapAddr σ a) := by
  cases src with
  | reg i =>
    simp only [gCtl] at h ⊢
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
  | imm v => simp only [gCtl, pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; simp [mapAddr]
  | mem _ => simp [gCtl, throw, throwThe, MonadExceptOf.throw] at h

theorem ccCond_hom (c : CC) (a b : Lin) : mapCond σ (ccCond c a b) = ccCond c (a.eval σ) (b.eval σ) := by
  cases c <;> rfl

theorem setData32_hom (s : State E Lin) (d : Nat) (x : E) :
    mapState env σ (setData32 s d x) = setData32 (mapState env σ s) d (ev x) := by
  simp [setData32, setG_hom, mapVal]

end St

end Hashtree.Asm.X86
