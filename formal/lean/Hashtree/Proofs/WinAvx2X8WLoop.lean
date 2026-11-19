import Hashtree.Proofs.WinAvx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P (K2 K3 K211 T2)
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinLogW
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip

/-!
# The windows avx2_x8 loop at the wrapper call state, for a residue

The loop of the windows `avx2_x8` in W mode, generic in the alignment residue `r` and in the
two bundles the residue-specific files provide (the linux `Avx2X8WLoop` with the saved-cell
handling of the windows `avx_x4` loop `WinAvxX4WLoop`):

* `CutsW r` -- the kernel-checked facts about the loop cuts at residue `r`
  (`WinAvx2X8WShift.shiftOk r`, `WinAvx2X8WStrip.stripOk r`, the push-list shape);
* `BodyW r` -- the composed body runs (`WinAvx2X8WBodyR{r}`, `WinAvx2X8WBodyR{r}S`): the
  first pass from the rebased loop head `K3` over `m8W`, every later pass from the stripped
  head `KHs r` over the push memory `m8P r`.

The first pass runs on the pilot cuts, whose logs hold the 368 saved cells; its end is the
stripped head behind the pass's whole log.  From then on the invariant is the plain W-mode
memory shape `WfMemW rodata []` of the memory seen through the accumulated log, `OutLogW` of the
log, and `SaveOk8 r`: the saved cells are in that memory (data bytes of the right byte index,
pointer bytes exactly).  With the memory-keyed environment `ecomb` these give the push-list
memory relation of `m8P r` (`wfP_of_saveOk8`).  `x8w_runW_last` (`8 ≤ c < 16`) and `x8w_runW`
(`c = 8 (j + 1) + s`, `8 ≤ s < 16`) end at the exit cut (`KTE r` after the first pass, `KTEs r`
after a later one) behind a W-mode log: the tail call into `hashtree_sha256_avx_x4` with the
frame popped and the wrapper registers restored (`exitGprW`).  The residue enters only through
`hr : r = (σ 9 - 16) % 32`.
-/

namespace Hashtree.Proofs.WinAvx2X8WLoop

/-! ## The push list's shape -/

/-- A push entry is the address-keyed data byte of its own address, or a pointer byte on one of
the wrapper's fixed symbols `6, 7, 8, 11, 12`. -/
def shapeOk (p : Int × Cell E Lin) : Bool :=
  match p.2 with
  | .dat x _ => decide (x = .var (.m rStack (sAt p.1)))
  | .pb a _ => decide (a.off = Lin.sym 6 ∨ a.off = Lin.sym 7 ∨ a.off = Lin.sym 8 ∨
      a.off = Lin.sym 11 ∨ a.off = Lin.sym 12)

/-! ## The residue-specific bundles -/

/-- The kernel-checked facts about the loop cuts at residue `r`. -/
structure CutsW (r : Nat) : Prop where
  sliceE : sliceCheck prog 4 m8W orcB 9 (x8A r) (K2W r) [] = true
  sliceE2 : sliceCheck prog 4 m8W orcB 8 (K2W r) (shiftK8 r K3) T2 = true
  sliceT : sliceCheck prog 4 m8W orcB 24 (shiftK8 r K211) (KT r) [] = true
  sliceX : sliceCheck prog 4 m8W orcEx 42 (shiftK8 r K211) (KTE r) [] = true
  KT_shape : ({ KT r with mem := [], assume := [] } : State E Lin) = (KHs r).substL tau8
  KT_assume : (KT r).assume = AT
  KT_logB : (KT r).mem.all logOkBW = true
  KT_save : (pushC r).all (savedIn (KT r).mem) = true
  KTE_assume : (KTE r).assume = AX
  KTE_logB : (KTE r).mem.all logOkBW = true
  sliceTs : sliceCheck prog 4 (m8P r) orcB 24 (stripK8 r K211) (KTs r) [] = true
  sliceXs : sliceCheck prog 4 (m8P r) orcEx 42 (stripK8 r K211) (KTEs r) [] = true
  KTs_shape : ({ KTs r with mem := [], assume := [] } : State E Lin) = (KHs r).substL tau8
  KTs_assume : (KTs r).assume = AT
  KTs_logB : (KTs r).mem.all logOkBW = true
  KTs_nopush : (KTs r).mem.all (fun p =>
    decide (p.1.region ≠ rStack ∨ p.1.off.k < -368 - (r : Int))) = true
  KHs_nOnly : (KHs r).nOnly = true
  KTEs_assume : (KTEs r).assume = AX
  KTEs_logB : (KTEs r).mem.all logOkBW = true
  m8P_keyed : MemKeyed (m8P r)
  push_shape : (pushC r).all shapeOk = true
  push_bounds : (pushC r).all (fun p => decide (-368 - (r : Int) ≤ p.1 ∧ p.1 < 0)) = true

/-- The composed body runs at residue `r`. -/
structure BodyW (r : Nat) where
  Gf : (Key → W32) → (Key → W32)
  GSf : (Key → W32) → (Key → W32)
  run : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool), Mem0Rel env1 σ m8W mem0c → 8 ≤ σ 2 →
    Hashtree.Asm.X86.run prog 4 mem0c orcC BODYLEN (mapState env1 σ (shiftK8 r K3)) =
      mapState (Gf env1) σ (shiftK8 r K211)
  mem : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int),
    Mem0Rel env1 σ m8W mem0c → Mem0Rel (Gf env1) σ m8W mem0c
  runS : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool), Mem0Rel env1 σ (m8P r) mem0c → 8 ≤ σ 2 →
    Hashtree.Asm.X86.run prog 4 mem0c orcC BODYLEN (mapState env1 σ (KHs r)) =
      mapState (GSf env1) σ (stripK8 r K211)
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

/-- The turn length: the body and the 24-instruction loop tail. -/
def TURNLEN : Nat := BODYLEN + 24

/-! ## The saved cells -/

/-- A saved cell in a memory: a data byte of the push entry's byte index, or exactly the
pointer byte. -/
def SavedAt (σ : Nat → Int) (m : Addr Int → Cell W32 Int) (k : Int) : Cell E Lin → Prop
  | .dat _ j => ∃ x, m ⟨rStack, σ 9 + k⟩ = .dat x j
  | .pb a j => m ⟨rStack, σ 9 + k⟩ = .pb (mapAddr σ a) j

/-- The saved cells of a memory. -/
def SaveOk8 (r : Nat) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) : Prop :=
  ∀ (k : Int) (c : Cell E Lin), plookup k (pushC r) = some c → SavedAt σ m k c

theorem shape_of {r : Nat} (C : CutsW r) (k : Int) (c : Cell E Lin) (h : (k, c) ∈ pushC r) :
    shapeOk (k, c) = true :=
  List.all_eq_true.mp C.push_shape (k, c) h

theorem bounds_of {r : Nat} (C : CutsW r) (k : Int) (c : Cell E Lin) (h : (k, c) ∈ pushC r) :
    -368 - (r : Int) ≤ k ∧ k < 0 :=
  of_decide_eq_true (List.all_eq_true.mp C.push_bounds (k, c) h)

/-- A pointer on one of the fixed symbols does not move under a substitution that fixes them. -/
theorem fixed_addr (a : Addr Lin) (σ σ' : Nat → Int) (hσ : ∀ j, 3 ≤ j → σ' j = σ j)
    (ha : a.off = Lin.sym 6 ∨ a.off = Lin.sym 7 ∨ a.off = Lin.sym 8 ∨ a.off = Lin.sym 11 ∨
      a.off = Lin.sym 12) : mapAddr σ' a = mapAddr σ a := by
  obtain ⟨reg, off⟩ := a
  simp only at ha
  simp only [mapAddr]
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Lin.eval_sym, hσ 6 (by omega), hσ 7 (by omega), hσ 8 (by omega),
      hσ 11 (by omega), hσ 12 (by omega)]

theorem shape_pb {r : Nat} (C : CutsW r) (k : Int) (a : Addr Lin) (j : Nat)
    (h : (k, Cell.pb a j) ∈ pushC r) :
    a.off = Lin.sym 6 ∨ a.off = Lin.sym 7 ∨ a.off = Lin.sym 8 ∨ a.off = Lin.sym 11 ∨
      a.off = Lin.sym 12 :=
  of_decide_eq_true (shape_of C k _ h)

theorem shape_dat {r : Nat} (C : CutsW r) (k : Int) (x : E) (j : Nat)
    (h : (k, Cell.dat x j) ∈ pushC r) : x = .var (.m rStack (sAt k)) :=
  of_decide_eq_true (shape_of C k _ h)

/-- A later pass never writes a saved cell: its stack writes are below `sAt (-368 - r)`. -/
theorem nopush_ne {r : Nat} (C : CutsW r) (σ : Nat → Int) (e : Key → W32) (k : Int)
    (hk : -368 - (r : Int) ≤ k) :
    ∀ p ∈ (KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)),
      p.1 ≠ (⟨rStack, σ 9 + k⟩ : Addr Int) := by
  intro p hp heq
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hn : decide (q.1.region ≠ rStack ∨ q.1.off.k < -368 - (r : Int)) = true :=
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

/-- The push-list memory shape under a memory-keyed environment, from the plain shape and the
saved cells. -/
theorem wfP_of_saveOk8 {r : Nat} (C : CutsW r) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (hw : WfMemW rodata [] e σ m) (hs : SaveOk8 r σ m) :
    WfMemW rodata (pushC r) (ecomb e σ m) σ m := by
  obtain ⟨htab, hret, hin, _⟩ := hw
  refine ⟨htab, hret, hin, ?_⟩
  intro k c hk _ _
  have hmem := plookup_mem k (pushC r) c hk
  have hsv := hs k c hk
  cases c with
  | dat x j =>
    have hx := shape_dat C k x j hmem
    subst hx
    obtain ⟨y, hy⟩ := hsv
    rw [hy]
    show (.dat y j : Cell W32 Int) =
      .dat (cellX (m ⟨rStack, (⟨k, stkC⟩ : Lin).eval σ⟩)) j
    rw [sAtW_eval, show k + σ 9 = σ 9 + k from by omega, hy]
    rfl
  | pb a j =>
    exact hsv

/-- The saved cells after the first pass: they are in the pass-1 log (`KT_save`). -/
theorem saveOk8_of_pass1 {r : Nat} (C : CutsW r) (e1 : Key → W32) (σ1 σ' : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (M0 : CLog) (hσ : ∀ j, 3 ≤ j → σ' j = σ1 j) :
    SaveOk8 r σ' (view ((KT r).mem.map (fun p => (mapAddr σ1 p.1, mapCell e1 σ1 p.2)) ++ M0)
      mem0c) := by
  have h9 : σ' 9 = σ1 9 := hσ 9 (by omega)
  intro k c hk
  have hmem : (k, c) ∈ pushC r := plookup_mem k (pushC r) c hk
  have hs : savedIn (KT r).mem (k, c) = true := List.all_eq_true.mp C.KT_save (k, c) hmem
  have hk' : (sAt k).eval σ1 = σ' 9 + k := by
    rw [show sAt k = (⟨k, stkC⟩ : Lin) from rfl, sAtW_eval, h9]
    omega
  have haddr : mapAddr σ1 (⟨rStack, sAt k⟩ : Addr Lin) = ⟨rStack, σ' 9 + k⟩ := by
    show (⟨rStack, (sAt k).eval σ1⟩ : Addr Int) = ⟨rStack, σ' 9 + k⟩
    rw [hk']
  cases c with
  | dat x j =>
    have hs' : lookupDat (⟨rStack, sAt k⟩ : Addr Lin) (KT r).mem j = true := hs
    obtain ⟨y, hy⟩ := lookupDat_eq hs'
    have hl := lookup_hom e1 σ1 (⟨rStack, sAt k⟩ : Addr Lin) (KT r).mem (some (.dat y j)) hy
    rw [haddr] at hl
    simp only [Option.map] at hl
    refine ⟨y.eval e1, ?_⟩
    rw [view, lookup_app_left _ _ _ _ hl]
    rfl
  | pb a j =>
    have hs' : lookupIs (⟨rStack, sAt k⟩ : Addr Lin) (KT r).mem (.pb a j) = true := hs
    have hl := lookup_hom e1 σ1 (⟨rStack, sAt k⟩ : Addr Lin) (KT r).mem (some (.pb a j))
      (lookupIs_eq hs')
    rw [haddr] at hl
    simp only [Option.map] at hl
    show view _ mem0c ⟨rStack, σ' 9 + k⟩ = .pb (mapAddr σ' a) j
    rw [view, lookup_app_left _ _ _ _ hl]
    show (.pb (mapAddr σ1 a) j : Cell W32 Int) = .pb (mapAddr σ' a) j
    rw [fixed_addr a σ1 σ' hσ (shape_pb C k a j hmem)]

/-- The saved cells survive a later pass: its writes are output cells or stack cells below
them. -/
theorem saveOk8_step {r : Nat} (C : CutsW r) (e1 : Key → W32) (σ σ' : Nat → Int)
    (hσ : ∀ j, 3 ≤ j → σ' j = σ j) (m : Addr Int → Cell W32 Int) (hs : SaveOk8 r σ m) :
    SaveOk8 r σ' (view ((KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2))) m) := by
  have h9 : σ' 9 = σ 9 := hσ 9 (by omega)
  intro k c hk
  have hmem := plookup_mem k (pushC r) c hk
  have hb := bounds_of C k c hmem
  have hv : view ((KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2))) m
      ⟨rStack, σ' 9 + k⟩ = m ⟨rStack, σ 9 + k⟩ := by
    rw [h9, view_other _ m _ (nopush_ne C σ e1 k hb.1)]
  have hsv := hs k c hk
  cases c with
  | dat x j =>
    obtain ⟨y, hy⟩ := hsv
    exact ⟨y, by rw [hv, hy]⟩
  | pb a j =>
    show view _ m ⟨rStack, σ' 9 + k⟩ = .pb (mapAddr σ' a) j
    rw [hv, fixed_addr a σ σ' hσ (shape_pb C k a j hmem)]
    exact hsv

/-! ## The entry: 24 instructions from the wrapper call state to the loop head -/

theorem entryWin_nOnly : entryWin.nOnly = true := by decide +kernel
theorem x8P_assume : x8P.assume = A1nz := by decide +kernel
theorem K2W_assume (r : Nat) : (K2W r).assume = A1nz := by
  rw [show (K2W r).assume = K2.assume from rfl]
  decide +kernel
theorem K2W_err (r : Nat) : (K2W r).err = none := by
  rw [show (K2W r).err = K2.err from rfl]
  decide +kernel

/-- **The entry segment.**  From `fr M (mapState env0 σ entryWin)` at any count `c ≥ 8` and the
residue `r = (σ 9 - 16) % 32`: the six-instruction prologue, the alignment, the frame and saves
(nine instructions to `K2`, eight to `K3`, including `cmp r8,8; jb` not taken), to the rebased
loop head `K3`, behind the caller's log. -/
theorem entry_runW {r : Nat} (C : CutsW r) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (hge : 8 ≤ σ 2)
    (hr : (r : Int) = (σ 9 - 16) % 32) :
    ∃ e1, run prog 4 mem0c orcC 24 (fr M (mapState env0 σ entryWin)) =
        fr M (mapState e1 σ (shiftK8 r K3)) ∧
      Mem0Rel e1 σ m8W (view M mem0c) := by
  let E := ecomb env0 σ (view M mem0c)
  have hw' : WfMemW rodata [] E σ (view M mem0c) := wfW_view rodata env0 E σ mem0c M hM hw
  have hrel : Mem0Rel E σ m8W (view M mem0c) := by
    rw [m8W_eq]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c) hw' (envMem_ecomb E σ (view M mem0c))
  have r6 := (slice_sound E σ m8W (view M mem0c) hrel prog 4 orcNZ orcC 6 entryWin x8P []
    sliceP entryWin_err (assumeOk_of σ x8P A1nz x8P_assume (asmNZ σ (by omega)))).1
  have hrel1 : Mem0Rel (envAbs E (run prog 4 m8W orcNZ 6 entryWin)) σ m8W (view M mem0c) :=
    mem0Rel_envAbs _ _ _ _ m8W_keyed hrel _
  have r1 := run1_align (envAbs E (run prog 4 m8W orcNZ 6 entryWin)) σ (view M mem0c) orcC r hr
  have r9 := (slice_sound _ σ m8W (view M mem0c) hrel1 prog 4 orcB orcC 9 (x8A r) (K2W r) []
    C.sliceE (x8A_err r) (assumeOk_of σ (K2W r) A1nz (K2W_assume r) (asmNZ σ (by omega)))).1
  have hrel2 : Mem0Rel (envAbs (envAbs E (run prog 4 m8W orcNZ 6 entryWin))
      (run prog 4 m8W orcB 9 (x8A r))) σ m8W (view M mem0c) :=
    mem0Rel_envAbs _ _ _ _ m8W_keyed hrel1 _
  have r8 := (slice_sound _ σ m8W (view M mem0c) hrel2 prog 4 orcB orcC 8 (K2W r) (shiftK8 r K3)
    T2 C.sliceE2 (K2W_err r) (assumeOk_of σ (shiftK8 r K3) A0 rfl (asmge σ hge))).1
  refine ⟨_, ?_, mem0Rel_envAbs _ _ _ _ m8W_keyed hrel2 (run prog 4 m8W orcB 8 (K2W r))⟩
  rw [run_fr, mapState_nOnly env0 E σ (fun _ => rfl) entryWin entryWin_nOnly]
  refine congrArg (fr M) ?_
  rw [show (24 : Nat) = 6 + (1 + (9 + 8)) from rfl, run_add, r6, run_add, r1, run_add, r9]
  exact r8

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

/-- The first pass from the rebased loop head: the body and the loop tail (`jb` not taken,
`c ≥ 16`), ending at the stripped head under `tau8` behind the pass's log, which carries the
memory invariants forward. -/
theorem first_turnW {r : Nat} (C : CutsW r) (B : BodyW r) (env0 e1 : Key → W32)
    (σ0 σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ0 mem0c) (h9 : σ 9 = σ0 9) (hM : OutLogW σ M)
    (hrel : Mem0Rel e1 σ m8W (view M mem0c)) (hge : 16 ≤ σ 2) :
    ∃ e' M', run prog 4 mem0c orcC TURNLEN (fr M (mapState e1 σ (shiftK8 r K3))) =
        fr M' (mapState e' (sigmaOf tau8 σ) (KHs r)) ∧ OutLogW (sigmaOf tau8 σ) M' ∧
      WfMemW rodata [] e' (sigmaOf tau8 σ) (view M' mem0c) ∧
      SaveOk8 r (sigmaOf tau8 σ) (view M' mem0c) := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel (by omega)
  have hm := B.mem e1 σ (view M mem0c) hrel
  have hT := (slice_sound (B.Gf e1) σ m8W (view M mem0c) hm prog 4 orcB orcC 24
    (shiftK8 r K211) (KT r) [] C.sliceT rfl
    (assumeOk_of σ (KT r) AT C.KT_assume (asmT σ hge))).1
  let e2 := envAbs (B.Gf e1) (run prog 4 m8W orcB 24 (shiftK8 r K211))
  have hL : OutLogW σ ((KT r).mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M) :=
    outLogW_app σ (outLogW_of_logB (KT r) C.KT_logB σ e2) hM
  have hL' : OutLogW (sigmaOf tau8 σ)
      ((KT r).mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M) :=
    outLogW_s9 _ (tau8_s9 σ) hL
  refine ⟨e2, (KT r).mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M, ?_, hL', ?_, ?_⟩
  · rw [run_fr, TURNLEN, run_add, hB, hT, turn_step1 C e2 σ, fr_app]
  · exact wfW_view rodata env0 e2 (sigmaOf tau8 σ) mem0c _ hL'
      (wfMemW_s9 rodata env0 σ0 (sigmaOf tau8 σ) mem0c hw (by rw [tau8_s9, h9]))
  · exact saveOk8_of_pass1 C e2 σ (sigmaOf tau8 σ) mem0c M (fun j hj => tau8_hi j hj σ)

/-- A later pass and the loop tail: the body from the stripped head over the push memory,
`c ≥ 16`. -/
theorem turn_runS {r : Nat} (C : CutsW r) (B : BodyW r) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (h0 : Mem0Rel env σ (m8P r) mem0c)
    (hge : 16 ≤ σ 2) :
    run prog 4 mem0c orcC TURNLEN (mapState env σ (KHs r)) =
      mapState (envAbs (B.GSf env) (run prog 4 (m8P r) orcB 24 (stripK8 r K211))) σ (KTs r) := by
  have hB := B.runS env σ mem0c orcC h0 (by omega)
  have hm := B.memS env σ mem0c h0
  have hT := (slice_sound (B.GSf env) σ (m8P r) mem0c hm prog 4 orcB orcC 24 (stripK8 r K211)
    (KTs r) [] C.sliceTs rfl (assumeOk_of σ (KTs r) AT C.KTs_assume (asmT σ hge))).1
  rw [TURNLEN, run_add, hB]
  exact hT

/-- The push memory relation at a framed head. -/
theorem relP {r : Nat} (C : CutsW r) (e : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (hw : WfMemW rodata [] e σ m) (hs : SaveOk8 r σ m) :
    Mem0Rel (ecomb e σ m) σ (m8P r) m := by
  rw [m8P_eq]
  exact mem0RelW_of_wf rodata (pushC r) (ecomb e σ m) σ m (wfP_of_saveOk8 C e σ m hw hs)
    (envMem_ecomb (ecomb e σ m) σ m)

/-- **One framed later turn.**  From the stripped head behind a log that carries the memory
invariants, one turn reproduces the head under `sigmaOf tau8 σ` and appends its writes. -/
theorem iter_stepS {r : Nat} (C : CutsW r) (B : BodyW r) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (e : Key → W32) (σ : Nat → Int) (M : CLog)
    (hw : WfMemW rodata [] e σ (view M mem0c)) (hs : SaveOk8 r σ (view M mem0c))
    (hM : OutLogW σ M) (hge : 16 ≤ σ 2) :
    ∃ e' M', run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ (KHs r))) =
        fr M' (mapState e' (sigmaOf tau8 σ) (KHs r)) ∧ OutLogW (sigmaOf tau8 σ) M' ∧
      WfMemW rodata [] e' (sigmaOf tau8 σ) (view M' mem0c) ∧
      SaveOk8 r (sigmaOf tau8 σ) (view M' mem0c) := by
  let E := ecomb e σ (view M mem0c)
  have hrel : Mem0Rel E σ (m8P r) (view M mem0c) := relP C e σ (view M mem0c) hw hs
  let e1 := envAbs (B.GSf E) (run prog 4 (m8P r) orcB 24 (stripK8 r K211))
  have hrun : run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ (KHs r))) =
      fr M (mapState e1 σ (KTs r)) := by
    rw [run_fr, mapState_nOnly e E σ (fun _ => rfl) (KHs r) C.KHs_nOnly]
    exact congrArg (fr M) (turn_runS C B E σ (view M mem0c) orcC hrel hge)
  have hL : OutLogW σ ((KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M) :=
    outLogW_app σ (outLogW_of_logB (KTs r) C.KTs_logB σ e1) hM
  have hL' : OutLogW (sigmaOf tau8 σ)
      ((KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M) :=
    outLogW_s9 _ (tau8_s9 σ) hL
  refine ⟨e1, (KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M, ?_, hL', ?_, ?_⟩
  · rw [hrun, turn_stepS C e1 σ, fr_app]
  · rw [view_append]
    exact wfW_view rodata e e1 (sigmaOf tau8 σ) (view M mem0c) _
      (outLogW_s9 _ (tau8_s9 σ) (outLogW_of_logB (KTs r) C.KTs_logB σ e1))
      (wfMemW_s9 rodata e σ (sigmaOf tau8 σ) (view M mem0c) hw (tau8_s9 σ))
  · rw [view_append]
    exact saveOk8_step C e1 σ (sigmaOf tau8 σ) (fun j hj => tau8_hi j hj σ) (view M mem0c) hs

/-- **The loop iterates.**  From the stripped head at `c = 8j + s` with `8 ≤ s < 16`, `j`
framed turns leave the head at count `s`, behind a W-mode log that still carries the memory
invariants. -/
theorem loopW {r : Nat} (C : CutsW r) (B : BodyW r) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (s : Nat) (hs : 8 ≤ s) (hs16 : s < 16) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog),
      σ 2 = 8 * (j : Int) + (s : Int) → OutLogW σ M →
      WfMemW rodata [] e σ (view M mem0c) → SaveOk8 r σ (view M mem0c) →
      ∃ e' M', run prog 4 mem0c orcC (j * TURNLEN) (fr M (mapState e σ (KHs r))) =
          fr M' (mapState e' (sIt8 j σ) (KHs r)) ∧ OutLogW (sIt8 j σ) M' ∧
        WfMemW rodata [] e' (sIt8 j σ) (view M' mem0c) ∧ SaveOk8 r (sIt8 j σ) (view M' mem0c) := by
  intro j
  induction j with
  | zero =>
    intro e σ M hσ hM hw hs'
    exact ⟨e, M, rfl, hM, hw, hs'⟩
  | succ j ih =>
    intro e σ M hσ hM hw hs'
    have hge : 16 ≤ σ 2 := by
      rw [hσ]
      have hsj : (8 : Int) ≤ (s : Int) := by exact_mod_cast hs
      omega
    obtain ⟨e1, M1, hrun, hM1, hw1, hs1⟩ := iter_stepS C B mem0c orcC e σ M hw hs' hM hge
    have hσ1 : sigmaOf tau8 σ 2 = 8 * (j : Int) + (s : Int) := by
      rw [tau8_count, hσ]
      omega
    obtain ⟨e2, M2, hrun2, hM2, hw2, hs2⟩ := ih e1 (sigmaOf tau8 σ) M1 hσ1 hM1 hw1 hs1
    refine ⟨e2, M2, ?_, hM2, hw2, hs2⟩
    have hlen : (j + 1) * TURNLEN = TURNLEN + j * TURNLEN := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hlen, run_add, hrun, hrun2]
    rfl

/-! ## The exits -/

/-- The first pass and the exit: `8 ≤ c < 16` after the entry. -/
theorem first_exitW {r : Nat} (C : CutsW r) (B : BodyW r) (e1 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hrel : Mem0Rel e1 σ m8W (view M mem0c)) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 42) (fr M (mapState e1 σ (shiftK8 r K3))) =
        fr M (mapState e' σ (KTE r)) ∧
      OutLogW σ ((KTE r).mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel hge
  have hm := B.mem e1 σ (view M mem0c) hrel
  have hX := (slice_sound (B.Gf e1) σ m8W (view M mem0c) hm prog 4 orcEx orcC 42
    (shiftK8 r K211) (KTE r) [] C.sliceX rfl
    (assumeOk_of σ (KTE r) AX C.KTE_assume (asmX σ hge hlt))).1
  refine ⟨envAbs (B.Gf e1) (run prog 4 m8W orcEx 42 (shiftK8 r K211)), ?_,
    outLogW_app σ (outLogW_of_logB (KTE r) C.KTE_logB σ _) hM⟩
  rw [run_fr, run_add, hB]
  exact congrArg (fr M) hX

/-- A later pass and the exit, behind the accumulated log: from the stripped head at a residual
count in `[8, 16)`, the body and the 42-instruction exit reach `KTEs r`. -/
theorem final_runW {r : Nat} (C : CutsW r) (B : BodyW r) (e : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] e σ (view M mem0c)) (hs : SaveOk8 r σ (view M mem0c))
    (hM : OutLogW σ M) (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 42) (fr M (mapState e σ (KHs r))) =
        fr M (mapState e' σ (KTEs r)) ∧
      OutLogW σ ((KTEs r).mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  let E := ecomb e σ (view M mem0c)
  have hrel : Mem0Rel E σ (m8P r) (view M mem0c) := relP C e σ (view M mem0c) hw hs
  have hB := B.runS E σ (view M mem0c) orcC hrel hge
  have hm := B.memS E σ (view M mem0c) hrel
  have hX := (slice_sound (B.GSf E) σ (m8P r) (view M mem0c) hm prog 4 orcEx orcC 42
    (stripK8 r K211) (KTEs r) [] C.sliceXs rfl
    (assumeOk_of σ (KTEs r) AX C.KTEs_assume (asmX σ hge hlt))).1
  refine ⟨envAbs (B.GSf E) (run prog 4 (m8P r) orcEx 42 (stripK8 r K211)), ?_,
    outLogW_app σ (outLogW_of_logB (KTEs r) C.KTEs_logB σ _) hM⟩
  rw [run_fr, mapState_nOnly e E σ (fun _ => rfl) (KHs r) C.KHs_nOnly, run_add, hB]
  exact congrArg (fr M) hX

/-! ## Every count -/

/-- **`8 ≤ c < 16`.**  The entry, one pass of the body and the exit reach the exit cut `KTE r`. -/
theorem x8w_runW_last {r : Nat} (C : CutsW r) (B : BodyW r) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) (hr : (r : Int) = (σ 9 - 16) % 32) :
    ∃ e', run prog 4 mem0c orcC (24 + (BODYLEN + 42)) (fr M (mapState env0 σ entryWin)) =
        fr M (mapState e' σ (KTE r)) ∧
      OutLogW σ ((KTE r).mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  obtain ⟨e1, hentry, hrel⟩ := entry_runW C env0 σ mem0c orcC M hw hM hge hr
  obtain ⟨e', hfin, hlog⟩ := first_exitW C B e1 σ mem0c orcC M hrel hM hge hlt
  refine ⟨e', ?_, hlog⟩
  rw [run_add, hentry]
  exact hfin

/-- **`c = 8 (j + 1) + s` with `8 ≤ s < 16`.**  The entry, the first pass with its tail, `j`
framed later passes and the final pass with the exit reach the exit cut `KTEs r` at the residual
count `s`. -/
theorem x8w_runW {r : Nat} (C : CutsW r) (B : BodyW r) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (j s : Nat) (hs : 8 ≤ s)
    (hs16 : s < 16) (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int))
    (hr : (r : Int) = (σ 9 - 16) % 32) :
    ∃ e' M', run prog 4 mem0c orcC (24 + (TURNLEN + (j * TURNLEN + (BODYLEN + 42))))
          (fr M (mapState env0 σ entryWin)) =
        fr M' (mapState e' (sIt8 (j + 1) σ) (KTEs r)) ∧
      OutLogW (sIt8 (j + 1) σ) ((KTEs r).mem.map (fun p =>
        (mapAddr (sIt8 (j + 1) σ) p.1, mapCell e' (sIt8 (j + 1) σ) p.2)) ++ M') := by
  have hs8 : (8 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hge : 8 ≤ σ 2 := by rw [hc]; omega
  obtain ⟨e1, hentry, hrel⟩ := entry_runW C env0 σ mem0c orcC M hw hM hge hr
  obtain ⟨e2, M2, hturn, hM2, hw2, hs2⟩ := first_turnW C B env0 e1 σ σ mem0c orcC M hw rfl
    hM hrel (by rw [hc]; omega)
  let σ1 : Nat → Int := sigmaOf tau8 σ
  have hcount : σ1 2 = 8 * (j : Int) + (s : Int) := by
    show sigmaOf tau8 σ 2 = 8 * (j : Int) + (s : Int)
    rw [tau8_count, hc]
    omega
  obtain ⟨e3, M3, hloop, hM3, hw3, hs3⟩ :=
    loopW C B mem0c orcC s hs hs16 j e2 σ1 M2 hcount hM2 hw2 hs2
  have h2f : sIt8 j σ1 2 = (s : Int) := by
    rw [sIt8_count, hcount]
    omega
  obtain ⟨e4, hfin, hM4⟩ := final_runW C B e3 (sIt8 j σ1) mem0c orcC M3 hw3 hs3 hM3
    (by rw [h2f]; exact hs8) (by rw [h2f]; exact_mod_cast hs16)
  refine ⟨e4, M3, ?_, ?_⟩
  · rw [run_add, hentry, run_add, hturn, run_add, hloop]
    exact hfin
  · show OutLogW (sIt8 j (sigmaOf tau8 σ)) _
    exact hM4

end Hashtree.Proofs.WinAvx2X8WLoop
