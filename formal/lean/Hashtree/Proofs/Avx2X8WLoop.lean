import Hashtree.Proofs.Avx2X8WStripDefs
import Hashtree.Proofs.AvxX4LoopWAll
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.Avx2X8
open Hashtree.Gen.Avx2X8P (K2 K210 T1)
open Hashtree.Proofs.AvxX4W (entryWx upd15 envM mapState_entryW wfMemW_upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW outLogW_app wfW_view logOkBW eval_stk wfMemW_s9)
open Hashtree.Proofs.AvxX4LoopWExit (upd15_9 outLogW_s9)
open Hashtree.Proofs.Avx2X8Align
open Hashtree.Proofs.Avx2X8WShift
open Hashtree.Proofs.Avx2X8WStrip

/-!
# The avx2_x8 loop at the wrapper call state, for a residue

The loop of `avx2_x8` in W mode, generic in the alignment residue `r` and in the two bundles
the residue-specific files provide:

* `CutsW r` -- the kernel-checked facts about the loop cuts at residue `r`
  (`Avx2X8WShift`, `Avx2X8WStrip`): the entry slice into the body head, the pass-1 loop tail
  and exit, the later-pass (stripped) tail and exit, the shape of each turn's end as the
  stripped invariant head under `tau8`, the log shapes, and the spilled cells' presence in the
  pass-1 log;
* `BodyW r` -- the composed body runs (`Avx2X8WBodyR{r}`, `Avx2X8WBodyR{r}S`): the first
  pass from the rebased `K2` over `m8`, every later pass from the stripped head `KHs r` over
  the push memory `m8P r`.

The first pass runs on the pilot cuts, whose logs hold the 40 spilled cells; its end is the
stripped head behind the pass's whole log (`turn_step1`).  From then on the invariant is
`WfMemW rodata (pushC r)` of the memory seen through the accumulated log (`wfP_of_pass1`
establishes it from the pass-1 log, `wfP_step` carries it over a later pass, whose writes
never touch the spilled cells), together with `OutLogW` of the log.  `x8_runW_last`
(`8 ≤ c < 16`) and `x8_runW` (`c = 8 (j + 1) + s`, `8 ≤ s < 16`) end at the exit cut (`KTE r`
after the first pass, `KTEs r` after a later one) behind a W-mode log: the tail call into
`hashtree_sha256_avx_x4` with the frame popped and the entry registers restored (`exitGpr`).
The residue enters only through `hr : r = (σ 9 - 8) % 32`; there is no bound on `σ 9`.
-/

namespace Hashtree.Proofs.Avx2X8WLoop

/-! ## The residue-specific bundles -/

/-- The kernel-checked facts about the loop cuts at residue `r`. -/
structure CutsW (r : Nat) : Prop where
  sliceE : sliceCheck prog 4 m8 orcB 10 (x8A r) (shiftK8 r K2) T1 = true
  sliceT : sliceCheck prog 4 m8 orcB 27 (shiftK8 r K210) (KT r) [] = true
  sliceX : sliceCheck prog 4 m8 orcEx 31 (shiftK8 r K210) (KTE r) [] = true
  KT_shape : ({ KT r with mem := [], assume := [] } : State E Lin) = (KHs r).substL tau8
  KT_assume : (KT r).assume = AT
  KT_logB : (KT r).mem.all logOkBW = true
  KT_push : (pushC r).all (fun p => lookupIs (⟨rStack, sAt p.1⟩ : Addr Lin) (KT r).mem p.2) = true
  KTE_assume : (KTE r).assume = AX
  KTE_logB : (KTE r).mem.all logOkBW = true
  sliceTs : sliceCheck prog 4 (m8P r) orcB 27 (stripK8 r K210) (KTs r) [] = true
  sliceXs : sliceCheck prog 4 (m8P r) orcEx 31 (stripK8 r K210) (KTEs r) [] = true
  KTs_shape : ({ KTs r with mem := [], assume := [] } : State E Lin) = (KHs r).substL tau8
  KTs_assume : (KTs r).assume = AT
  KTs_logB : (KTs r).mem.all logOkBW = true
  KTs_nopush : (KTs r).mem.all (fun p =>
    decide (p.1.region ≠ rStack ∨ p.1.off.k < -40 - (r : Int))) = true
  KHs_nOnly : (KHs r).nOnly = true
  KTEs_assume : (KTEs r).assume = AX
  KTEs_logB : (KTEs r).mem.all logOkBW = true
  m8P_keyed : MemKeyed (m8P r)

/-- The composed body runs at residue `r`. -/
structure BodyW (r : Nat) where
  Gf : (Key → W32) → (Key → W32)
  GSf : (Key → W32) → (Key → W32)
  run : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool), Mem0Rel env1 σ m8 mem0c → 8 ≤ σ 2 →
    Hashtree.Asm.X86.run prog 4 mem0c orcC BODYLEN (mapState env1 σ (shiftK8 r K2)) =
      mapState (Gf env1) σ (shiftK8 r K210)
  mem : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int),
    Mem0Rel env1 σ m8 mem0c → Mem0Rel (Gf env1) σ m8 mem0c
  runS : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool), Mem0Rel env1 σ (m8P r) mem0c → 8 ≤ σ 2 →
    Hashtree.Asm.X86.run prog 4 mem0c orcC BODYLEN (mapState env1 σ (KHs r)) =
      mapState (GSf env1) σ (stripK8 r K210)
  memS : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int),
    Mem0Rel env1 σ (m8P r) mem0c → Mem0Rel (GSf env1) σ (m8P r) mem0c

/-! ## The loop substitution -/

theorem tau8_s9 (σ : Nat → Int) : sigmaOf tau8 σ 9 = σ 9 := by
  have ht : tauAt tau8 9 = Lin.sym 9 := rfl
  rw [sigmaOf, ht, Lin.eval_sym]

theorem tau8_count (σ : Nat → Int) : sigmaOf tau8 σ 2 = σ 2 - 8 := by
  have ht : tauAt tau8 2 = (⟨-8, [0, 0, 1]⟩ : Lin) := rfl
  show (tauAt tau8 2).eval σ = σ 2 - 8
  rw [ht]
  simp [Lin.eval, dotC]
  omega

theorem tau8_in (σ : Nat → Int) : sigmaOf tau8 σ 0 = σ 0 + 512 := by
  have ht : tauAt tau8 0 = (⟨512, [1]⟩ : Lin) := rfl
  show (tauAt tau8 0).eval σ = σ 0 + 512
  rw [ht]
  simp [Lin.eval, dotC]
  omega

theorem tau8_out (σ : Nat → Int) : sigmaOf tau8 σ 1 = σ 1 + 256 := by
  have ht : tauAt tau8 1 = (⟨256, [0, 1]⟩ : Lin) := rfl
  show (tauAt tau8 1).eval σ = σ 1 + 256
  rw [ht]
  simp [Lin.eval, dotC]
  omega

theorem getD_ge {α : Type} : ∀ (l : List α) (i : Nat) (d : α), l.length ≤ i → l.getD i d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => by simp at h
  | _ :: xs, n + 1, d, h => by
    rw [List.getD_cons_succ]
    exact getD_ge xs n d (by simpa using h)

theorem tau8_hi (i : Nat) (h : 3 ≤ i) (σ : Nat → Int) : sigmaOf tau8 σ i = σ i := by
  have ht : tauAt tau8 i = Lin.sym i := getD_ge tau8 i (Lin.sym i) (by simp [tau8]; omega)
  rw [sigmaOf, ht, Lin.eval_sym]

/-- `j` turns of the substitution. -/
def sIt8 : Nat → (Nat → Int) → (Nat → Int)
  | 0, σ => σ
  | j + 1, σ => sIt8 j (sigmaOf tau8 σ)

theorem sIt8_s9 : ∀ (j : Nat) (σ : Nat → Int), sIt8 j σ 9 = σ 9
  | 0, _ => rfl
  | j + 1, σ => by
    rw [show sIt8 (j + 1) σ = sIt8 j (sigmaOf tau8 σ) from rfl, sIt8_s9 j (sigmaOf tau8 σ),
      tau8_s9]

theorem sIt8_count : ∀ (j : Nat) (σ : Nat → Int), sIt8 j σ 2 = σ 2 - 8 * (j : Int)
  | 0, σ => by simp [sIt8]
  | j + 1, σ => by
    rw [show sIt8 (j + 1) σ = sIt8 j (sigmaOf tau8 σ) from rfl, sIt8_count j (sigmaOf tau8 σ),
      tau8_count]
    omega

theorem sIt8_in : ∀ (j : Nat) (σ : Nat → Int), sIt8 j σ 0 = σ 0 + 512 * (j : Int)
  | 0, σ => by simp [sIt8]
  | j + 1, σ => by
    rw [show sIt8 (j + 1) σ = sIt8 j (sigmaOf tau8 σ) from rfl, sIt8_in j (sigmaOf tau8 σ),
      tau8_in]
    omega

theorem sIt8_out : ∀ (j : Nat) (σ : Nat → Int), sIt8 j σ 1 = σ 1 + 256 * (j : Int)
  | 0, σ => by simp [sIt8]
  | j + 1, σ => by
    rw [show sIt8 (j + 1) σ = sIt8 j (sigmaOf tau8 σ) from rfl, sIt8_out j (sigmaOf tau8 σ),
      tau8_out]
    omega

theorem sIt8_hi (i : Nat) (h : 3 ≤ i) : ∀ (j : Nat) (σ : Nat → Int), sIt8 j σ i = σ i
  | 0, _ => rfl
  | j + 1, σ => by
    rw [show sIt8 (j + 1) σ = sIt8 j (sigmaOf tau8 σ) from rfl, sIt8_hi i h j (sigmaOf tau8 σ),
      tau8_hi i h]

/-! ## Logs -/

/-- A cut whose writes pass `logOkBW` has a W-mode log at every valuation. -/
theorem outLogW_of_logB (K : State E Lin) (h : K.mem.all logOkBW = true) (σ : Nat → Int)
    (e : Key → W32) : OutLogW σ (K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hq' : logOkBW q = true := List.all_eq_true.mp h q hq
  by_cases h1 : q.1.region = rOut
  · exact Or.inl (by simpa [mapAddr] using h1)
  by_cases h2 : q.1.region = rStack
  · have hd : decide (q.1.off.c = stkC ∧ q.1.off.k < 0) = true := by
      rw [logOkBW, if_neg h1, if_pos h2] at hq'
      exact hq'
    obtain ⟨hc, hk⟩ := of_decide_eq_true hd
    refine Or.inr ⟨by simpa [mapAddr] using h2, ?_⟩
    have hoff : q.1.off.eval σ = q.1.off.k + σ 9 := eval_stk σ q.1.off hc
    show q.1.off.eval σ < σ 9
    rw [hoff]
    omega
  · exfalso
    rw [logOkBW, if_neg h1, if_neg h2] at hq'
    cases hq'

/-- Viewing through an appended log is viewing through its parts. -/
theorem view_append (L M : CLog) (m : Addr Int → Cell W32 Int) :
    view (L ++ M) m = view L (view M m) := by
  funext a
  simp only [view, lookup_append]
  obtain ⟨rl, hl⟩ := lookup_conc_ok a L
  rw [hl]
  cases rl with
  | none => rfl
  | some c => rfl

/-- Appending a log behind another. -/
theorem fr_app (M L : CLog) (s : CState) : fr M (fr L s) = fr (L ++ M) s := by
  simp only [fr, List.append_assoc]

/-- The turn length: the body and the 27-instruction loop tail. -/
def TURNLEN : Nat := BODYLEN + 27

/-! ## The spilled cells -/

/-- Every spilled cell is a pointer-byte cell on a symbol the loop substitution fixes, so its
concrete value only depends on symbols `≥ 3` (and not on the environment). -/
theorem pushC_cell_agree (r : Nat) (e e' : Key → W32) (σ σ' : Nat → Int)
    (hσ : ∀ j, 3 ≤ j → σ' j = σ j) (k : Int) (c : Cell E Lin) (h : (k, c) ∈ pushC r) :
    mapCell e' σ' c = mapCell e σ c := by
  have h6 := hσ 6 (by omega)
  have h7 := hσ 7 (by omega)
  have h8 := hσ 8 (by omega)
  have h11 := hσ 11 (by omega)
  have h12 := hσ 12 (by omega)
  simp only [pushC, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, rfl⟩
  all_goals simp [mapCell, mapAddr, Lin.eval_sym, h6, h7, h8, h11, h12]

/-- The spilled cells sit at offsets in `[-40 - r, 0)`. -/
theorem pushC_bounds (r : Nat) (k : Int) (c : Cell E Lin) (h : (k, c) ∈ pushC r) :
    -40 - (r : Int) ≤ k ∧ k < 0 := by
  simp only [pushC, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩
  all_goals omega

/-- A later pass never writes a spilled cell: its stack writes are below `sAt (-40 - r)`. -/
theorem nopush_ne {r : Nat} (C : CutsW r) (σ : Nat → Int) (e : Key → W32) (k : Int)
    (hk : -40 - (r : Int) ≤ k) :
    ∀ p ∈ (KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)),
      p.1 ≠ (⟨rStack, σ 9 + k⟩ : Addr Int) := by
  intro p hp heq
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hn : decide (q.1.region ≠ rStack ∨ q.1.off.k < -40 - (r : Int)) = true :=
    List.all_eq_true.mp C.KTs_nopush q hq
  have hb : logOkBW q = true := List.all_eq_true.mp C.KTs_logB q hq
  have hreg : q.1.region = rStack := by
    have := congrArg Addr.region heq
    simpa [mapAddr] using this
  rcases of_decide_eq_true hn with h | h
  · exact h hreg
  · have h1 : q.1.region ≠ rOut := by rw [hreg]; decide
    have hd : decide (q.1.off.c = stkC ∧ q.1.off.k < 0) = true := by
      rw [logOkBW, if_neg h1, if_pos hreg] at hb
      exact hb
    obtain ⟨hc, _⟩ := of_decide_eq_true hd
    have hoff : q.1.off.eval σ = q.1.off.k + σ 9 := eval_stk σ q.1.off hc
    have := congrArg Addr.off heq
    simp only [mapAddr] at this
    rw [hoff] at this
    omega

/-! ## The memory invariants -/

/-- The push-list memory relation after the first pass: the spilled cells are in the pass-1
log (`KT_push`), nothing in the rest of the log is above `σ 9`, and the table, marker and input
are untouched. -/
theorem wfP_of_pass1 {r : Nat} (C : CutsW r) (env e1 e' : Key → W32) (σ σ1 σ' : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (M0 : CLog)
    (hw : WfMemW rodata [] env σ mem0c) (hM0 : OutLogW σ M0)
    (h9 : σ1 9 = σ 9) (hσ : ∀ j, 3 ≤ j → σ' j = σ1 j) :
    WfMemW rodata (pushC r) e' σ'
      (view ((KT r).mem.map (fun p => (mapAddr σ1 p.1, mapCell e1 σ1 p.2)) ++ M0) mem0c) := by
  have hL : OutLogW σ1 ((KT r).mem.map (fun p => (mapAddr σ1 p.1, mapCell e1 σ1 p.2)) ++ M0) :=
    outLogW_app σ1 (outLogW_of_logB (KT r) C.KT_logB σ1 e1) (outLogW_s9 M0 h9 hM0)
  have h9' : σ' 9 = σ 9 := by rw [hσ 9 (by omega), h9]
  have hbase : WfMemW rodata [] env σ'
      (view ((KT r).mem.map (fun p => (mapAddr σ1 p.1, mapCell e1 σ1 p.2)) ++ M0) mem0c) :=
    wfW_view rodata env env σ' mem0c _ (outLogW_s9 _ (by rw [h9', h9]) hL)
      (wfMemW_s9 rodata env σ σ' mem0c hw h9')
  obtain ⟨htab, hret, hin, _⟩ := hbase
  refine ⟨htab, hret, hin, ?_⟩
  intro k c hk _ _
  have hmem : (k, c) ∈ pushC r := plookup_mem k (pushC r) c hk
  have hs : lookupIs (⟨rStack, sAt k⟩ : Addr Lin) (KT r).mem c = true :=
    List.all_eq_true.mp C.KT_push (k, c) hmem
  have hl := lookup_hom e1 σ1 (⟨rStack, sAt k⟩ : Addr Lin) (KT r).mem (some c) (lookupIs_eq hs)
  have hk : (sAt k).eval σ1 = σ' 9 + k := by
    rw [Hashtree.Proofs.WrapperAmd64.sAt_eval, h9', h9]
    omega
  have haddr : mapAddr σ1 (⟨rStack, sAt k⟩ : Addr Lin) = ⟨rStack, σ' 9 + k⟩ := by
    show (⟨rStack, (sAt k).eval σ1⟩ : Addr Int) = ⟨rStack, σ' 9 + k⟩
    rw [hk]
  rw [haddr] at hl
  simp only [Option.map] at hl
  rw [view, lookup_app_left _ _ _ _ hl]
  exact (pushC_cell_agree r e1 e' σ1 σ' hσ k c hmem).symm

/-- The push-list memory relation survives a later pass: its writes are output cells or stack
cells below the spilled cells. -/
theorem wfP_step {r : Nat} (C : CutsW r) (e e1 e' : Key → W32) (σ σ' : Nat → Int)
    (m : Addr Int → Cell W32 Int) (hσ : ∀ j, 3 ≤ j → σ' j = σ j)
    (hw : WfMemW rodata (pushC r) e σ m) :
    WfMemW rodata (pushC r) e' σ'
      (view ((KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2))) m) := by
  have h9 : σ' 9 = σ 9 := hσ 9 (by omega)
  have hL : OutLogW σ ((KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2))) :=
    outLogW_of_logB (KTs r) C.KTs_logB σ e1
  obtain ⟨htab, hret, hin, hpush⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o
    rw [view_other _ m _ (Hashtree.Proofs.AvxX4LoopWFrame.outLogW_ne _ σ hL _
      ⟨show (4 : Region) ≠ rOut by decide,
        fun h => absurd (show (4 : Region) = rStack from h) (by decide)⟩)]
    exact htab o
  · intro k h0 h8
    rw [h9, view_other _ m _ (Hashtree.Proofs.AvxX4LoopWFrame.outLogW_ne _ σ hL _
      ⟨show rStack ≠ rOut by decide, fun _ => by simp only; omega⟩)]
    exact hret k h0 h8
  · intro o
    rw [view_other _ m _ (Hashtree.Proofs.AvxX4LoopWFrame.outLogW_ne _ σ hL _
      ⟨show rIn ≠ rOut by decide,
        fun h => absurd (show (1 : Region) = rStack from h) (by decide)⟩)]
    exact hin o
  · intro k c hk h8 hok
    have hmem : (k, c) ∈ pushC r := plookup_mem k (pushC r) c hk
    have hb := pushC_bounds r k c hmem
    rw [h9, view_other _ m _ (nopush_ne C σ e1 k hb.1)]
    rw [hpush k c hk h8 hok]
    exact (pushC_cell_agree r e e' σ σ' hσ k c hmem).symm

/-! ## The entry: 16 instructions from the wrapper call state to the body head -/

/-- **The entry segment.**  From `fr M (mapState env0 σ entryW)` at any count `c ≥ 8` and the
residue `r = (σ 9 - 8) % 32`: the five-instruction prologue, the alignment, and the ten
instructions to the rebased body head `K2`, behind the caller's log, at `upd15 σ`. -/
theorem entry_runW {r : Nat} (C : CutsW r) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (hge : 8 ≤ σ 2)
    (hr : (r : Int) = (σ 9 - 8) % 32) :
    ∃ e1, run prog 4 mem0c orcC 16 (fr M (mapState env0 σ entryW)) =
        fr M (mapState e1 (upd15 σ) (shiftK8 r K2)) ∧
      Mem0Rel e1 (upd15 σ) m8 (view M mem0c) := by
  have h9 : upd15 σ 9 = σ 9 := by simp [upd15]
  have h2 : upd15 σ 2 = σ 2 := by simp [upd15]
  have hw' : WfMemW rodata [] (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) (view M mem0c) :=
    wfMemW_upd15 rodata env0 _ σ (view M mem0c) (wfW_view rodata env0 env0 σ mem0c M hM hw)
  have hrel : Mem0Rel (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) m8 (view M mem0c) := by
    rw [m8_eq]
    exact mem0RelW_of_wf rodata [] _ _ (view M mem0c) hw' (fun r off => rfl)
  have r5 := (slice_sound (envM env0 (view M mem0c) (upd15 σ)) (upd15 σ) m8 (view M mem0c)
    hrel prog 4 orcNZ orcC 5 entryWx x8P [] sliceP entryWx_err
    (assumeOk_of (upd15 σ) x8P A1nz x8P_assume (asmNZ (upd15 σ) (by rw [h2]; omega)))).1
  have hrel1 : Mem0Rel (envAbs (envM env0 (view M mem0c) (upd15 σ))
      (run prog 4 m8 orcNZ 5 entryWx)) (upd15 σ) m8 (view M mem0c) :=
    mem0Rel_envAbs _ _ _ _ m8_keyed hrel _
  have r1 := run1_align (envAbs (envM env0 (view M mem0c) (upd15 σ))
    (run prog 4 m8 orcNZ 5 entryWx)) (upd15 σ) (view M mem0c) orcC r (by rw [h9]; exact hr)
  have r10 := (slice_sound _ (upd15 σ) m8 (view M mem0c) hrel1 prog 4 orcB orcC 10 (x8A r)
    (shiftK8 r K2) T1 C.sliceE (x8A_err r)
    (assumeOk_of (upd15 σ) (shiftK8 r K2) A0 rfl (asmge (upd15 σ) (by rw [h2]; exact hge)))).1
  refine ⟨envAbs (envAbs (envM env0 (view M mem0c) (upd15 σ)) (run prog 4 m8 orcNZ 5 entryWx))
      (run prog 4 m8 orcB 10 (x8A r)), ?_,
    mem0Rel_envAbs _ _ _ _ m8_keyed hrel1 (run prog 4 m8 orcB 10 (x8A r))⟩
  rw [run_fr, ← mapState_entryW env0 (view M mem0c) σ]
  refine congrArg (fr M) ?_
  rw [show (16 : Nat) = 5 + (1 + 10) from rfl, run_add, r5, run_add, r1]
  exact r10

/-! ## The turns -/

/-- The end of the first pass is the stripped head under `tau8`, behind the pass's log. -/
theorem turn_step1 {r : Nat} (C : CutsW r) (e : Key → W32) (σ : Nat → Int) :
    mapState e σ (KT r) =
      fr ((KT r).mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)))
        (mapState e (sigmaOf tau8 σ) (KHs r)) :=
  mapState_reached e σ (KT r) (KHs r) tau8 C.KT_shape

/-- The end of a later pass is the stripped head under `tau8`, behind the pass's log. -/
theorem turn_stepS {r : Nat} (C : CutsW r) (e : Key → W32) (σ : Nat → Int) :
    mapState e σ (KTs r) =
      fr ((KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)))
        (mapState e (sigmaOf tau8 σ) (KHs r)) :=
  mapState_reached e σ (KTs r) (KHs r) tau8 C.KTs_shape

/-- The first pass from the rebased body head: the body and the loop tail (`jb` not taken,
`c ≥ 16`), ending at the stripped head under `tau8` behind the pass's log, which carries the
push-list memory relation forward. -/
theorem first_turnW {r : Nat} (C : CutsW r) (B : BodyW r) (env0 e1 : Key → W32)
    (σ0 σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ0 mem0c) (h9 : σ 9 = σ0 9) (hM : OutLogW σ M)
    (hrel : Mem0Rel e1 σ m8 (view M mem0c)) (hge : 16 ≤ σ 2) :
    ∃ e' M', run prog 4 mem0c orcC TURNLEN (fr M (mapState e1 σ (shiftK8 r K2))) =
        fr M' (mapState e' (sigmaOf tau8 σ) (KHs r)) ∧ OutLogW (sigmaOf tau8 σ) M' ∧
      WfMemW rodata (pushC r) e' (sigmaOf tau8 σ) (view M' mem0c) := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel (by omega)
  have hm := B.mem e1 σ (view M mem0c) hrel
  have hT := (slice_sound (B.Gf e1) σ m8 (view M mem0c) hm prog 4 orcB orcC 27
    (shiftK8 r K210) (KT r) [] C.sliceT rfl
    (assumeOk_of σ (KT r) AT C.KT_assume (asmT σ hge))).1
  let e2 := envAbs (B.Gf e1) (run prog 4 m8 orcB 27 (shiftK8 r K210))
  refine ⟨e2, (KT r).mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M, ?_, ?_, ?_⟩
  · rw [run_fr, TURNLEN, run_add, hB, hT, turn_step1 C e2 σ, fr_app]
  · have h := outLogW_app σ (outLogW_of_logB (KT r) C.KT_logB σ e2) hM
    intro p hp
    rw [tau8_s9]
    exact h p hp
  · exact wfP_of_pass1 C env0 e2 e2 σ0 σ (sigmaOf tau8 σ) mem0c M hw (outLogW_s9 M h9.symm hM) h9
      (fun j hj => tau8_hi j hj σ)

/-- A later pass and the loop tail: the body from the stripped head over the push memory,
`c ≥ 16`. -/
theorem turn_runS {r : Nat} (C : CutsW r) (B : BodyW r) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (h0 : Mem0Rel env σ (m8P r) mem0c)
    (hge : 16 ≤ σ 2) :
    run prog 4 mem0c orcC TURNLEN (mapState env σ (KHs r)) =
      mapState (envAbs (B.GSf env) (run prog 4 (m8P r) orcB 27 (stripK8 r K210))) σ (KTs r) := by
  have hB := B.runS env σ mem0c orcC h0 (by omega)
  have hm := B.memS env σ mem0c h0
  have hT := (slice_sound (B.GSf env) σ (m8P r) mem0c hm prog 4 orcB orcC 27 (stripK8 r K210)
    (KTs r) [] C.sliceTs rfl (assumeOk_of σ (KTs r) AT C.KTs_assume (asmT σ hge))).1
  rw [TURNLEN, run_add, hB]
  exact hT

/-- **One framed later turn.**  From the stripped head behind a log that carries the push-list
memory relation, one turn reproduces the head under `sigmaOf tau8 σ` and appends its writes. -/
theorem iter_stepS {r : Nat} (C : CutsW r) (B : BodyW r) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (e : Key → W32) (σ : Nat → Int) (M : CLog)
    (hw : WfMemW rodata (pushC r) e σ (view M mem0c)) (hM : OutLogW σ M) (hge : 16 ≤ σ 2) :
    ∃ e' M', run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ (KHs r))) =
        fr M' (mapState e' (sigmaOf tau8 σ) (KHs r)) ∧ OutLogW (sigmaOf tau8 σ) M' ∧
      WfMemW rodata (pushC r) e' (sigmaOf tau8 σ) (view M' mem0c) := by
  let E := ecomb e σ (view M mem0c)
  have hwE : WfMemW rodata (pushC r) E σ (view M mem0c) := by
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨h1, h2, h3, ?_⟩
    intro k c hk h8 hok
    rw [h4 k c hk h8 hok]
    exact (pushC_cell_agree r e E σ σ (fun _ _ => rfl) k c (plookup_mem k (pushC r) c hk)).symm
  have hrel : Mem0Rel E σ (m8P r) (view M mem0c) := by
    rw [m8P_eq]
    exact mem0RelW_of_wf rodata (pushC r) E σ (view M mem0c) hwE (envMem_ecomb E σ (view M mem0c))
  let e1 := envAbs (B.GSf E) (run prog 4 (m8P r) orcB 27 (stripK8 r K210))
  have hrun : run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ (KHs r))) =
      fr M (mapState e1 σ (KTs r)) := by
    rw [run_fr, mapState_nOnly e E σ (fun _ => rfl) (KHs r) C.KHs_nOnly]
    exact congrArg (fr M) (turn_runS C B E σ (view M mem0c) orcC hrel hge)
  refine ⟨e1, (KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M, ?_, ?_, ?_⟩
  · rw [hrun, turn_stepS C e1 σ, fr_app]
  · have h := outLogW_app σ (outLogW_of_logB (KTs r) C.KTs_logB σ e1) hM
    intro p hp
    rw [tau8_s9]
    exact h p hp
  · rw [view_append]
    exact wfP_step C e e1 e1 σ (sigmaOf tau8 σ) (view M mem0c) (fun j hj => tau8_hi j hj σ) hw

/-- **The loop iterates.**  From the stripped head at `c = 8j + s` with `8 ≤ s < 16`, `j`
framed turns leave the head at count `s`, behind a W-mode log that still carries the push-list
memory relation. -/
theorem loopW {r : Nat} (C : CutsW r) (B : BodyW r) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (s : Nat) (hs : 8 ≤ s) (hs16 : s < 16) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog),
      σ 2 = 8 * (j : Int) + (s : Int) → OutLogW σ M →
      WfMemW rodata (pushC r) e σ (view M mem0c) →
      ∃ e' M', run prog 4 mem0c orcC (j * TURNLEN) (fr M (mapState e σ (KHs r))) =
          fr M' (mapState e' (sIt8 j σ) (KHs r)) ∧ OutLogW (sIt8 j σ) M' ∧
        WfMemW rodata (pushC r) e' (sIt8 j σ) (view M' mem0c) := by
  intro j
  induction j with
  | zero =>
    intro e σ M hσ hM hw
    exact ⟨e, M, rfl, hM, hw⟩
  | succ j ih =>
    intro e σ M hσ hM hw
    have hge : 16 ≤ σ 2 := by
      rw [hσ]
      have hsj : (8 : Int) ≤ (s : Int) := by exact_mod_cast hs
      omega
    obtain ⟨e1, M1, hrun, hM1, hw1⟩ := iter_stepS C B mem0c orcC e σ M hw hM hge
    have hσ1 : sigmaOf tau8 σ 2 = 8 * (j : Int) + (s : Int) := by
      rw [tau8_count, hσ]
      omega
    obtain ⟨e2, M2, hrun2, hM2, hw2⟩ := ih e1 (sigmaOf tau8 σ) M1 hσ1 hM1 hw1
    refine ⟨e2, M2, ?_, hM2, hw2⟩
    have hlen : (j + 1) * TURNLEN = TURNLEN + j * TURNLEN := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hlen, run_add, hrun, hrun2]
    rfl

/-! ## The exits -/

/-- The first pass and the exit: `8 ≤ c < 16` after the entry. -/
theorem first_exitW {r : Nat} (C : CutsW r) (B : BodyW r) (e1 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hrel : Mem0Rel e1 σ m8 (view M mem0c)) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 31) (fr M (mapState e1 σ (shiftK8 r K2))) =
        fr M (mapState e' σ (KTE r)) ∧
      OutLogW σ ((KTE r).mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel hge
  have hm := B.mem e1 σ (view M mem0c) hrel
  have hX := (slice_sound (B.Gf e1) σ m8 (view M mem0c) hm prog 4 orcEx orcC 31
    (shiftK8 r K210) (KTE r) [] C.sliceX rfl
    (assumeOk_of σ (KTE r) AX C.KTE_assume (asmX σ hge hlt))).1
  refine ⟨envAbs (B.Gf e1) (run prog 4 m8 orcEx 31 (shiftK8 r K210)), ?_,
    outLogW_app σ (outLogW_of_logB (KTE r) C.KTE_logB σ _) hM⟩
  rw [run_fr, run_add, hB]
  exact congrArg (fr M) hX

/-- A later pass and the exit, behind the accumulated log: from the stripped head at a residual
count in `[8, 16)`, the body and the 31-instruction exit reach `KTEs r`. -/
theorem final_runW {r : Nat} (C : CutsW r) (B : BodyW r) (e : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata (pushC r) e σ (view M mem0c)) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 31) (fr M (mapState e σ (KHs r))) =
        fr M (mapState e' σ (KTEs r)) ∧
      OutLogW σ ((KTEs r).mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  let E := ecomb e σ (view M mem0c)
  have hwE : WfMemW rodata (pushC r) E σ (view M mem0c) := by
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨h1, h2, h3, ?_⟩
    intro k c hk h8 hok
    rw [h4 k c hk h8 hok]
    exact (pushC_cell_agree r e E σ σ (fun _ _ => rfl) k c (plookup_mem k (pushC r) c hk)).symm
  have hrel : Mem0Rel E σ (m8P r) (view M mem0c) := by
    rw [m8P_eq]
    exact mem0RelW_of_wf rodata (pushC r) E σ (view M mem0c) hwE (envMem_ecomb E σ (view M mem0c))
  have hB := B.runS E σ (view M mem0c) orcC hrel hge
  have hm := B.memS E σ (view M mem0c) hrel
  have hX := (slice_sound (B.GSf E) σ (m8P r) (view M mem0c) hm prog 4 orcEx orcC 31
    (stripK8 r K210) (KTEs r) [] C.sliceXs rfl
    (assumeOk_of σ (KTEs r) AX C.KTEs_assume (asmX σ hge hlt))).1
  refine ⟨envAbs (B.GSf E) (run prog 4 (m8P r) orcEx 31 (stripK8 r K210)), ?_,
    outLogW_app σ (outLogW_of_logB (KTEs r) C.KTEs_logB σ _) hM⟩
  rw [run_fr, mapState_nOnly e E σ (fun _ => rfl) (KHs r) C.KHs_nOnly, run_add, hB]
  exact congrArg (fr M) hX

/-! ## Every count -/

/-- **`8 ≤ c < 16`.**  The entry, one pass of the body and the exit reach the exit cut `KTE r`. -/
theorem x8_runW_last {r : Nat} (C : CutsW r) (B : BodyW r) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) (hr : (r : Int) = (σ 9 - 8) % 32) :
    ∃ e' M', run prog 4 mem0c orcC (16 + (BODYLEN + 31)) (fr M (mapState env0 σ entryW)) =
        fr M' (mapState e' (upd15 σ) (KTE r)) ∧
      OutLogW (upd15 σ) ((KTE r).mem.map (fun p =>
        (mapAddr (upd15 σ) p.1, mapCell e' (upd15 σ) p.2)) ++ M') := by
  have h9 : upd15 σ 9 = σ 9 := by simp [upd15]
  have h2 : upd15 σ 2 = σ 2 := by simp [upd15]
  have hM15 : OutLogW (upd15 σ) M := outLogW_s9 M h9 hM
  obtain ⟨e1, hentry, hrel⟩ := entry_runW C env0 σ mem0c orcC M hw hM hge hr
  obtain ⟨e', hfin, hlog⟩ := first_exitW C B e1 (upd15 σ) mem0c orcC M hrel hM15
    (by rw [h2]; exact hge) (by rw [h2]; exact hlt)
  refine ⟨e', M, ?_, hlog⟩
  rw [run_add, hentry]
  exact hfin

/-- **`c = 8 (j + 1) + s` with `8 ≤ s < 16`.**  The entry, the first pass with its tail, `j`
framed later passes and the final pass with the exit reach the exit cut `KTEs r` at the residual
count `s`. -/
theorem x8_runW {r : Nat} (C : CutsW r) (B : BodyW r) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (j s : Nat) (hs : 8 ≤ s)
    (hs16 : s < 16) (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int))
    (hr : (r : Int) = (σ 9 - 8) % 32) :
    ∃ e' M', run prog 4 mem0c orcC (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31))))
          (fr M (mapState env0 σ entryW)) =
        fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r)) ∧
      OutLogW (sIt8 (j + 1) (upd15 σ)) ((KTEs r).mem.map (fun p =>
        (mapAddr (sIt8 (j + 1) (upd15 σ)) p.1, mapCell e' (sIt8 (j + 1) (upd15 σ)) p.2)) ++ M') := by
  have h9 : upd15 σ 9 = σ 9 := by simp [upd15]
  have h2 : upd15 σ 2 = σ 2 := by simp [upd15]
  have hM15 : OutLogW (upd15 σ) M := outLogW_s9 M h9 hM
  have hs8 : (8 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hge : 8 ≤ σ 2 := by rw [hc]; omega
  obtain ⟨e1, hentry, hrel⟩ := entry_runW C env0 σ mem0c orcC M hw hM hge hr
  obtain ⟨e2, M2, hturn, hM2, hw2⟩ := first_turnW C B env0 e1 σ (upd15 σ) mem0c orcC M hw h9
    hM15 hrel (by rw [h2, hc]; omega)
  let σ1 : Nat → Int := sigmaOf tau8 (upd15 σ)
  have hcount : σ1 2 = 8 * (j : Int) + (s : Int) := by
    show sigmaOf tau8 (upd15 σ) 2 = 8 * (j : Int) + (s : Int)
    rw [tau8_count, h2, hc]
    omega
  obtain ⟨e3, M3, hloop, hM3, hw3⟩ := loopW C B mem0c orcC s hs hs16 j e2 σ1 M2 hcount hM2 hw2
  have h2f : sIt8 j σ1 2 = (s : Int) := by
    rw [sIt8_count, hcount]
    omega
  obtain ⟨e4, hfin, hM4⟩ := final_runW C B e3 (sIt8 j σ1) mem0c orcC M3 hw3 hM3
    (by rw [h2f]; exact hs8) (by rw [h2f]; exact_mod_cast hs16)
  refine ⟨e4, M3, ?_, ?_⟩
  · rw [run_add, hentry, run_add, hturn, run_add, hloop]
    exact hfin
  · show OutLogW (sIt8 j (sigmaOf tau8 (upd15 σ))) _
    exact hM4

end Hashtree.Proofs.Avx2X8WLoop
