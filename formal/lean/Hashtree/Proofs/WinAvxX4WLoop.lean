import Hashtree.Proofs.WinAvxX4WStripDefs
import Hashtree.Proofs.WinAvxX4WBody
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.AvxX4
open Hashtree.Gen.WinAvxX4P (K2 K203 T0 T1)
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinLogW
open Hashtree.Proofs.WinAvxX4W
open Hashtree.Proofs.WinAvxX4WStrip
open Hashtree.Proofs.WinAvxX4WBody (BODYLEN)

/-!
# The windows avx_x4 loop at the wrapper call state

The loop of the windows `avx_x4` in W mode, generic in the two bundles the kernel-checked
files provide:

* `CutsW` -- the facts about the loop cuts (`WinAvxX4WShift.tailOk`,
  `WinAvxX4WStrip.stripOk`): the pass-1 loop tail and exit, the later-pass (stripped) tail and
  exit, the shape of each turn's end as the stripped invariant head under `tauW`, the log
  shapes, and the saved bytes' presence in the pass-1 log;
* `BodyW` -- the composed body runs (`WinAvxX4WBody`, `WinAvxX4WBodyS`): the first pass from
  the rebased `K2` over `m0W`, every later pass from the stripped head `KHs` over the push
  memory `m0WP`.

The first pass runs on the pilot cuts, whose logs hold the 160 saved `xmm6..15` bytes; its end
is the stripped head behind the pass's whole log (`turn_step1`).  From then on the invariant
is `WfMemW rodata []` of the memory seen through the accumulated log together with `SaveOk`
(the saved bytes are data bytes of the right index at their addresses; `saveOk_of_pass1`
establishes it from the pass-1 log, `saveOk_step` carries it over a later pass, whose writes
never touch them), and `OutLogW` of the log.  Under a memory-keyed environment these give the
push-list memory shape `WfMemW rodata pushCW` a later pass runs over (`wfP_of_saveOk`).
`x4w_runW_last` (`4 ≤ c < 8`) and `x4w_runW` (`c = 4 (j + 1) + s`, `4 ≤ s < 8`) end at the
exit cut (`KTE` after the first pass, `KTEs` after a later one) behind a W-mode log: the tail
call into `hashtree_sha256_avx_x1` with the frame popped, `xmm6..15` restored from the saved
bytes and the entry registers restored (`exitGprW`).
-/

namespace Hashtree.Proofs.WinAvxX4WLoop

/-! ## The bundles -/

/-- The kernel-checked facts about the loop cuts. -/
structure CutsW : Prop where
  sliceT : sliceCheck prog 4 m0W orcB 25 (shiftKW K203) KT [] = true
  sliceX : sliceCheck prog 4 m0W orcEx 37 (shiftKW K203) KTE [] = true
  KT_shape : ({ KT with mem := [], assume := [] } : State E Lin) = KHs.substL tauW
  KT_assume : KT.assume = AT
  KT_logB : KT.mem.all logOkBW = true
  KT_save : pushCW.all (fun p => lookupDat (⟨rStack, sAt p.1⟩ : Addr Lin) KT.mem (byteOf p.2)) = true
  KTE_assume : KTE.assume = AX
  KTE_logB : KTE.mem.all logOkBW = true
  sliceTs : sliceCheck prog 4 m0WP orcB 25 (stripKW K203) KTs [] = true
  sliceXs : sliceCheck prog 4 m0WP orcEx 37 (stripKW K203) KTEs [] = true
  KTs_shape : ({ KTs with mem := [], assume := [] } : State E Lin) = KHs.substL tauW
  KTs_assume : KTs.assume = AT
  KTs_logB : KTs.mem.all logOkBW = true
  KTs_nopush : KTs.mem.all (fun p => decide (p.1.region ≠ rStack ∨ p.1.off.k < -184)) = true
  KHs_nOnly : KHs.nOnly = true
  KTEs_assume : KTEs.assume = AX
  KTEs_logB : KTEs.mem.all logOkBW = true

/-- The composed body runs. -/
structure BodyW where
  Gf : (Key → W32) → (Key → W32)
  GSf : (Key → W32) → (Key → W32)
  run : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool), Mem0Rel env1 σ m0W mem0c → 4 ≤ σ 2 →
    Hashtree.Asm.X86.run prog 4 mem0c orcC BODYLEN (mapState env1 σ (shiftKW K2)) =
      mapState (Gf env1) σ (shiftKW K203)
  mem : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int),
    Mem0Rel env1 σ m0W mem0c → Mem0Rel (Gf env1) σ m0W mem0c
  runS : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool), Mem0Rel env1 σ m0WP mem0c → 4 ≤ σ 2 →
    Hashtree.Asm.X86.run prog 4 mem0c orcC BODYLEN (mapState env1 σ KHs) =
      mapState (GSf env1) σ (stripKW K203)
  memS : ∀ (env1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int),
    Mem0Rel env1 σ m0WP mem0c → Mem0Rel (GSf env1) σ m0WP mem0c

/-! ## The loop substitution -/

theorem tauW_s9 (σ : Nat → Int) : sigmaOf tauW σ 9 = σ 9 := by
  have ht : tauAt tauW 9 = Lin.sym 9 := rfl
  rw [sigmaOf, ht, Lin.eval_sym]

theorem tauW_count (σ : Nat → Int) : sigmaOf tauW σ 2 = σ 2 - 4 := by
  have ht : tauAt tauW 2 = (⟨-4, [0, 0, 1]⟩ : Lin) := rfl
  show (tauAt tauW 2).eval σ = σ 2 - 4
  rw [ht]
  simp [Lin.eval, dotC]
  omega

theorem tauW_in (σ : Nat → Int) : sigmaOf tauW σ 0 = σ 0 + 256 := by
  have ht : tauAt tauW 0 = (⟨256, [1]⟩ : Lin) := rfl
  show (tauAt tauW 0).eval σ = σ 0 + 256
  rw [ht]
  simp [Lin.eval, dotC]
  omega

theorem tauW_out (σ : Nat → Int) : sigmaOf tauW σ 1 = σ 1 + 128 := by
  have ht : tauAt tauW 1 = (⟨128, [0, 1]⟩ : Lin) := rfl
  show (tauAt tauW 1).eval σ = σ 1 + 128
  rw [ht]
  simp [Lin.eval, dotC]
  omega

theorem getD_ge {α : Type} : ∀ (l : List α) (i : Nat) (d : α), l.length ≤ i → l.getD i d = d
  | [], _, _, _ => by simp
  | _ :: xs, 0, _, h => by simp at h
  | _ :: xs, i + 1, d, h => by
    simp only [List.getD_cons_succ]
    exact getD_ge xs i d (by simpa using h)

theorem tauW_hi (i : Nat) (h : 3 ≤ i) (σ : Nat → Int) : sigmaOf tauW σ i = σ i := by
  have ht : tauAt tauW i = Lin.sym i := getD_ge tauW i (Lin.sym i) (by simp [tauW]; omega)
  rw [sigmaOf, ht, Lin.eval_sym]

/-- `j` turns of the substitution. -/
def sItW : Nat → (Nat → Int) → (Nat → Int)
  | 0, σ => σ
  | j + 1, σ => sItW j (sigmaOf tauW σ)

theorem sItW_s9 : ∀ (j : Nat) (σ : Nat → Int), sItW j σ 9 = σ 9
  | 0, _ => rfl
  | j + 1, σ => by
    rw [show sItW (j + 1) σ = sItW j (sigmaOf tauW σ) from rfl, sItW_s9 j (sigmaOf tauW σ),
      tauW_s9]

theorem sItW_count : ∀ (j : Nat) (σ : Nat → Int), sItW j σ 2 = σ 2 - 4 * (j : Int)
  | 0, _ => by simp [sItW]
  | j + 1, σ => by
    rw [show sItW (j + 1) σ = sItW j (sigmaOf tauW σ) from rfl, sItW_count j (sigmaOf tauW σ),
      tauW_count]
    omega

theorem sItW_in : ∀ (j : Nat) (σ : Nat → Int), sItW j σ 0 = σ 0 + 256 * (j : Int)
  | 0, _ => by simp [sItW]
  | j + 1, σ => by
    rw [show sItW (j + 1) σ = sItW j (sigmaOf tauW σ) from rfl, sItW_in j (sigmaOf tauW σ),
      tauW_in]
    omega

theorem sItW_out : ∀ (j : Nat) (σ : Nat → Int), sItW j σ 1 = σ 1 + 128 * (j : Int)
  | 0, _ => by simp [sItW]
  | j + 1, σ => by
    rw [show sItW (j + 1) σ = sItW j (sigmaOf tauW σ) from rfl, sItW_out j (sigmaOf tauW σ),
      tauW_out]
    omega

theorem sItW_hi (i : Nat) (h : 3 ≤ i) : ∀ (j : Nat) (σ : Nat → Int), sItW j σ i = σ i
  | 0, _ => rfl
  | j + 1, σ => by
    rw [show sItW (j + 1) σ = sItW j (sigmaOf tauW σ) from rfl, sItW_hi i h j (sigmaOf tauW σ),
      tauW_hi i h]

/-- The turn length: the body and the 25-instruction loop tail. -/
def TURNLEN : Nat := BODYLEN + 25

/-! ## The saved bytes -/

/-- Every push entry is the address-keyed data byte of its own address. -/
theorem pushCW_shape_all :
    pushCW.all (fun p => decide (p.2 = (.dat (.var (.m rStack (sAt p.1))) (byteOf p.2) : Cell E Lin)))
      = true := by
  decide +kernel

theorem pushCW_bounds_all : pushCW.all (fun p => decide (-184 ≤ p.1 ∧ p.1 ≤ -25)) = true := by
  decide +kernel

theorem pushCW_shape (k : Int) (c : Cell E Lin) (h : (k, c) ∈ pushCW) :
    c = (.dat (.var (.m rStack (sAt k))) (byteOf c) : Cell E Lin) :=
  of_decide_eq_true (List.all_eq_true.mp pushCW_shape_all (k, c) h)

theorem pushCW_bounds (k : Int) (c : Cell E Lin) (h : (k, c) ∈ pushCW) :
    -184 ≤ k ∧ k ≤ -25 :=
  of_decide_eq_true (List.all_eq_true.mp pushCW_bounds_all (k, c) h)

/-- The saved bytes of a memory: data bytes of the push list's byte index at their addresses. -/
def SaveOk (σ : Nat → Int) (m : Addr Int → Cell W32 Int) : Prop :=
  ∀ (k : Int) (c : Cell E Lin), plookup k pushCW = some c →
    ∃ x, m ⟨rStack, σ 9 + k⟩ = .dat x (byteOf c)

/-- A later pass never writes a saved byte: its stack writes are below `sAt (-184)`. -/
theorem nopush_ne (C : CutsW) (σ : Nat → Int) (e : Key → W32) (k : Int) (hk : -184 ≤ k) :
    ∀ p ∈ KTs.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)),
      p.1 ≠ (⟨rStack, σ 9 + k⟩ : Addr Int) := by
  intro p hp heq
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hn : decide (q.1.region ≠ rStack ∨ q.1.off.k < -184) = true :=
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
saved bytes. -/
theorem wfP_of_saveOk (e : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (hw : WfMemW rodata [] e σ m) (hs : SaveOk σ m) :
    WfMemW rodata pushCW (ecomb e σ m) σ m := by
  obtain ⟨htab, hret, hin, _⟩ := hw
  refine ⟨htab, hret, hin, ?_⟩
  intro k c hk _ _
  obtain ⟨x, hx⟩ := hs k c hk
  have hc := pushCW_shape k c (plookup_mem k pushCW c hk)
  have hm : mapCell (ecomb e σ m) σ c =
      mapCell (ecomb e σ m) σ (.dat (.var (.m rStack (sAt k))) (byteOf c)) :=
    congrArg (mapCell (ecomb e σ m) σ) hc
  rw [hx, hm]
  show (.dat x (byteOf c) : Cell W32 Int) =
    .dat (cellX (m ⟨rStack, (⟨k, stkC⟩ : Lin).eval σ⟩)) (byteOf c)
  rw [sAtW_eval, show k + σ 9 = σ 9 + k from by omega, hx]
  rfl

/-- The saved bytes after the first pass: they are in the pass-1 log (`KT_save`), as data
bytes of the right index. -/
theorem saveOk_of_pass1 (C : CutsW) (e1 : Key → W32) (σ1 σ' : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (M0 : CLog) (h9 : σ' 9 = σ1 9) :
    SaveOk σ' (view (KT.mem.map (fun p => (mapAddr σ1 p.1, mapCell e1 σ1 p.2)) ++ M0) mem0c) := by
  intro k c hk
  have hmem : (k, c) ∈ pushCW := plookup_mem k pushCW c hk
  have hs : lookupDat (⟨rStack, sAt k⟩ : Addr Lin) KT.mem (byteOf c) = true :=
    List.all_eq_true.mp C.KT_save (k, c) hmem
  obtain ⟨x, hx⟩ := lookupDat_eq hs
  have hl := lookup_hom e1 σ1 (⟨rStack, sAt k⟩ : Addr Lin) KT.mem (some (.dat x (byteOf c))) hx
  have hk' : (sAt k).eval σ1 = σ' 9 + k := by
    rw [show sAt k = (⟨k, stkC⟩ : Lin) from rfl, sAtW_eval, h9]
    omega
  have haddr : mapAddr σ1 (⟨rStack, sAt k⟩ : Addr Lin) = ⟨rStack, σ' 9 + k⟩ := by
    show (⟨rStack, (sAt k).eval σ1⟩ : Addr Int) = ⟨rStack, σ' 9 + k⟩
    rw [hk']
  rw [haddr] at hl
  simp only [Option.map] at hl
  refine ⟨x.eval e1, ?_⟩
  rw [view, lookup_app_left _ _ _ _ hl]
  rfl

/-- The saved bytes survive a later pass: its writes are output cells or stack cells below
them. -/
theorem saveOk_step (C : CutsW) (e1 : Key → W32) (σ σ' : Nat → Int) (h9 : σ' 9 = σ 9)
    (m : Addr Int → Cell W32 Int) (hs : SaveOk σ m) :
    SaveOk σ' (view (KTs.mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2))) m) := by
  intro k c hk
  have hb := pushCW_bounds k c (plookup_mem k pushCW c hk)
  rw [h9, view_other _ m _ (nopush_ne C σ e1 k hb.1)]
  exact hs k c hk

/-! ## The entry: 16 instructions from the wrapper call state to the body head -/

theorem entryWin_nOnly : entryWin.nOnly = true := by decide +kernel
theorem K1W_assume : K1W.assume = A0e := by decide +kernel
theorem K1W_err : K1W.err = none := by decide +kernel

/-- **The entry segment.**  From `fr M (mapState env0 σ entryWin)` at any count `c ≥ 4`: the
prologue (`cmp r8,0; jne`, `sub rsp,568`, the ten `xmm` saves, `cmp r8,4; jl` not taken) to the
rebased body head `K2`, behind the caller's log. -/
theorem entry_runW (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (hge : 4 ≤ σ 2) :
    ∃ e1, run prog 4 mem0c orcC 16 (fr M (mapState env0 σ entryWin)) =
        fr M (mapState e1 σ (shiftKW K2)) ∧
      Mem0Rel e1 σ m0W (view M mem0c) := by
  let E := ecomb env0 σ (view M mem0c)
  have hw' : WfMemW rodata [] E σ (view M mem0c) := wfW_view rodata env0 E σ mem0c M hM hw
  have hrel : Mem0Rel E σ m0W (view M mem0c) := by
    rw [m0W_eq]
    exact mem0RelW_of_wf rodata [] E σ (view M mem0c) hw' (envMem_ecomb E σ (view M mem0c))
  have r8 := (slice_sound E σ m0W (view M mem0c) hrel prog 4 orcE orcC 8 entryWin K1W T0
    sliceE entryWin_err (assumeOk_of σ K1W A0e K1W_assume (asmNZ σ (by omega)))).1
  have hrel1 : Mem0Rel (envAbs E (run prog 4 m0W orcE 8 entryWin)) σ m0W (view M mem0c) :=
    mem0Rel_envAbs _ _ _ _ m0W_keyed hrel _
  have r8b := (slice_sound _ σ m0W (view M mem0c) hrel1 prog 4 orcB orcC 8 K1W (shiftKW K2) T1
    sliceE1 K1W_err (assumeOk_of σ (shiftKW K2) A0 rfl (asmge σ hge))).1
  refine ⟨envAbs (envAbs E (run prog 4 m0W orcE 8 entryWin)) (run prog 4 m0W orcB 8 K1W), ?_,
    mem0Rel_envAbs _ _ _ _ m0W_keyed hrel1 (run prog 4 m0W orcB 8 K1W)⟩
  rw [run_fr, mapState_nOnly env0 E σ (fun _ => rfl) entryWin entryWin_nOnly]
  refine congrArg (fr M) ?_
  rw [show (16 : Nat) = 8 + 8 from rfl, run_add, r8]
  exact r8b

/-! ## The turns -/

/-- The end of the first pass is the stripped head under `tauW`, behind the pass's log. -/
theorem turn_step1 (C : CutsW) (e : Key → W32) (σ : Nat → Int) :
    mapState e σ KT =
      fr (KT.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)))
        (mapState e (sigmaOf tauW σ) KHs) :=
  mapState_reached e σ KT KHs tauW C.KT_shape

/-- The end of a later pass is the stripped head under `tauW`, behind the pass's log. -/
theorem turn_stepS (C : CutsW) (e : Key → W32) (σ : Nat → Int) :
    mapState e σ KTs =
      fr (KTs.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)))
        (mapState e (sigmaOf tauW σ) KHs) :=
  mapState_reached e σ KTs KHs tauW C.KTs_shape

/-- The first pass from the rebased body head: the body and the loop tail (`jl` not taken,
`c ≥ 8`), ending at the stripped head under `tauW` behind the pass's log, which carries the
memory invariants forward. -/
theorem first_turnW (C : CutsW) (B : BodyW) (env0 e1 : Key → W32)
    (σ0 σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ0 mem0c) (h9 : σ 9 = σ0 9) (hM : OutLogW σ M)
    (hrel : Mem0Rel e1 σ m0W (view M mem0c)) (hge : 8 ≤ σ 2) :
    ∃ e' M', run prog 4 mem0c orcC TURNLEN (fr M (mapState e1 σ (shiftKW K2))) =
        fr M' (mapState e' (sigmaOf tauW σ) KHs) ∧ OutLogW (sigmaOf tauW σ) M' ∧
      WfMemW rodata [] e' (sigmaOf tauW σ) (view M' mem0c) ∧
      SaveOk (sigmaOf tauW σ) (view M' mem0c) := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel (by omega)
  have hm := B.mem e1 σ (view M mem0c) hrel
  have hT := (slice_sound (B.Gf e1) σ m0W (view M mem0c) hm prog 4 orcB orcC 25
    (shiftKW K203) KT [] C.sliceT rfl
    (assumeOk_of σ KT AT C.KT_assume (asmT σ hge))).1
  let e2 := envAbs (B.Gf e1) (run prog 4 m0W orcB 25 (shiftKW K203))
  have hL : OutLogW σ (KT.mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M) :=
    outLogW_app σ (outLogW_of_logB KT C.KT_logB σ e2) hM
  have hL' : OutLogW (sigmaOf tauW σ) (KT.mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M) :=
    outLogW_s9 _ (tauW_s9 σ) hL
  refine ⟨e2, KT.mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M, ?_, hL', ?_, ?_⟩
  · rw [run_fr, TURNLEN, run_add, hB, hT, turn_step1 C e2 σ, fr_app]
  · exact wfW_view rodata env0 e2 (sigmaOf tauW σ) mem0c _ hL'
      (wfMemW_s9 rodata env0 σ0 (sigmaOf tauW σ) mem0c hw (by rw [tauW_s9, h9]))
  · exact saveOk_of_pass1 C e2 σ (sigmaOf tauW σ) mem0c M (tauW_s9 σ)

/-- A later pass and the loop tail: the body from the stripped head over the push memory,
`c ≥ 8`. -/
theorem turn_runS (C : CutsW) (B : BodyW) (env : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (h0 : Mem0Rel env σ m0WP mem0c)
    (hge : 8 ≤ σ 2) :
    run prog 4 mem0c orcC TURNLEN (mapState env σ KHs) =
      mapState (envAbs (B.GSf env) (run prog 4 m0WP orcB 25 (stripKW K203))) σ KTs := by
  have hB := B.runS env σ mem0c orcC h0 (by omega)
  have hm := B.memS env σ mem0c h0
  have hT := (slice_sound (B.GSf env) σ m0WP mem0c hm prog 4 orcB orcC 25 (stripKW K203)
    KTs [] C.sliceTs rfl (assumeOk_of σ KTs AT C.KTs_assume (asmT σ hge))).1
  rw [TURNLEN, run_add, hB]
  exact hT

/-- **One framed later turn.**  From the stripped head behind a log that carries the memory
invariants, one turn reproduces the head under `sigmaOf tauW σ` and appends its writes. -/
theorem iter_stepS (C : CutsW) (B : BodyW) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (e : Key → W32) (σ : Nat → Int) (M : CLog)
    (hw : WfMemW rodata [] e σ (view M mem0c)) (hs : SaveOk σ (view M mem0c))
    (hM : OutLogW σ M) (hge : 8 ≤ σ 2) :
    ∃ e' M', run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHs)) =
        fr M' (mapState e' (sigmaOf tauW σ) KHs) ∧ OutLogW (sigmaOf tauW σ) M' ∧
      WfMemW rodata [] e' (sigmaOf tauW σ) (view M' mem0c) ∧
      SaveOk (sigmaOf tauW σ) (view M' mem0c) := by
  let E := ecomb e σ (view M mem0c)
  have hwE : WfMemW rodata pushCW E σ (view M mem0c) := wfP_of_saveOk e σ (view M mem0c) hw hs
  have hrel : Mem0Rel E σ m0WP (view M mem0c) := by
    rw [m0WP_eq]
    exact mem0RelW_of_wf rodata pushCW E σ (view M mem0c) hwE (envMem_ecomb E σ (view M mem0c))
  let e1 := envAbs (B.GSf E) (run prog 4 m0WP orcB 25 (stripKW K203))
  have hrun : run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHs)) =
      fr M (mapState e1 σ KTs) := by
    rw [run_fr, mapState_nOnly e E σ (fun _ => rfl) KHs C.KHs_nOnly]
    exact congrArg (fr M) (turn_runS C B E σ (view M mem0c) orcC hrel hge)
  have hL : OutLogW σ (KTs.mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M) :=
    outLogW_app σ (outLogW_of_logB KTs C.KTs_logB σ e1) hM
  have hL' : OutLogW (sigmaOf tauW σ) (KTs.mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M) :=
    outLogW_s9 _ (tauW_s9 σ) hL
  refine ⟨e1, KTs.mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M, ?_, hL', ?_, ?_⟩
  · rw [hrun, turn_stepS C e1 σ, fr_app]
  · rw [view_append]
    exact wfW_view rodata e e1 (sigmaOf tauW σ) (view M mem0c) _
      (outLogW_s9 _ (tauW_s9 σ) (outLogW_of_logB KTs C.KTs_logB σ e1))
      (wfMemW_s9 rodata e σ (sigmaOf tauW σ) (view M mem0c) hw (tauW_s9 σ))
  · rw [view_append]
    exact saveOk_step C e1 σ (sigmaOf tauW σ) (tauW_s9 σ) (view M mem0c) hs

/-- **The loop iterates.**  From the stripped head at `c = 4j + s` with `4 ≤ s < 8`, `j`
framed turns leave the head at count `s`, behind a W-mode log that still carries the memory
invariants. -/
theorem loopW (C : CutsW) (B : BodyW) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (s : Nat) (hs : 4 ≤ s) (hs8 : s < 8) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog),
      σ 2 = 4 * (j : Int) + (s : Int) → OutLogW σ M →
      WfMemW rodata [] e σ (view M mem0c) → SaveOk σ (view M mem0c) →
      ∃ e' M', run prog 4 mem0c orcC (j * TURNLEN) (fr M (mapState e σ KHs)) =
          fr M' (mapState e' (sItW j σ) KHs) ∧ OutLogW (sItW j σ) M' ∧
        WfMemW rodata [] e' (sItW j σ) (view M' mem0c) ∧ SaveOk (sItW j σ) (view M' mem0c) := by
  intro j
  induction j with
  | zero =>
    intro e σ M hσ hM hw hsv
    exact ⟨e, M, rfl, hM, hw, hsv⟩
  | succ j ih =>
    intro e σ M hσ hM hw hsv
    have hge : 8 ≤ σ 2 := by
      rw [hσ]
      have hsj : (4 : Int) ≤ (s : Int) := by exact_mod_cast hs
      omega
    obtain ⟨e1, M1, hrun, hM1, hw1, hs1⟩ := iter_stepS C B mem0c orcC e σ M hw hsv hM hge
    have hσ1 : sigmaOf tauW σ 2 = 4 * (j : Int) + (s : Int) := by
      rw [tauW_count, hσ]
      omega
    obtain ⟨e2, M2, hrun2, hM2, hw2, hs2⟩ := ih e1 (sigmaOf tauW σ) M1 hσ1 hM1 hw1 hs1
    refine ⟨e2, M2, ?_, hM2, hw2, hs2⟩
    have hlen : (j + 1) * TURNLEN = TURNLEN + j * TURNLEN := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hlen, run_add, hrun, hrun2]
    rfl

/-! ## The exits -/

/-- The first pass and the exit: `4 ≤ c < 8` after the entry. -/
theorem first_exitW (C : CutsW) (B : BodyW) (e1 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hrel : Mem0Rel e1 σ m0W (view M mem0c)) (hM : OutLogW σ M)
    (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 37) (fr M (mapState e1 σ (shiftKW K2))) =
        fr M (mapState e' σ KTE) ∧
      OutLogW σ (KTE.mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel hge
  have hm := B.mem e1 σ (view M mem0c) hrel
  have hX := (slice_sound (B.Gf e1) σ m0W (view M mem0c) hm prog 4 orcEx orcC 37
    (shiftKW K203) KTE [] C.sliceX rfl
    (assumeOk_of σ KTE AX C.KTE_assume (asmX σ hge hlt))).1
  refine ⟨envAbs (B.Gf e1) (run prog 4 m0W orcEx 37 (shiftKW K203)), ?_,
    outLogW_app σ (outLogW_of_logB KTE C.KTE_logB σ _) hM⟩
  rw [run_fr, run_add, hB]
  exact congrArg (fr M) hX

/-- A later pass and the exit, behind the accumulated log: from the stripped head at a residual
count in `[4, 8)`, the body and the 37-instruction exit reach `KTEs`. -/
theorem final_runW (C : CutsW) (B : BodyW) (e : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] e σ (view M mem0c)) (hs : SaveOk σ (view M mem0c))
    (hM : OutLogW σ M) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 37) (fr M (mapState e σ KHs)) =
        fr M (mapState e' σ KTEs) ∧
      OutLogW σ (KTEs.mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M) := by
  let E := ecomb e σ (view M mem0c)
  have hwE : WfMemW rodata pushCW E σ (view M mem0c) := wfP_of_saveOk e σ (view M mem0c) hw hs
  have hrel : Mem0Rel E σ m0WP (view M mem0c) := by
    rw [m0WP_eq]
    exact mem0RelW_of_wf rodata pushCW E σ (view M mem0c) hwE (envMem_ecomb E σ (view M mem0c))
  have hB := B.runS E σ (view M mem0c) orcC hrel hge
  have hm := B.memS E σ (view M mem0c) hrel
  have hX := (slice_sound (B.GSf E) σ m0WP (view M mem0c) hm prog 4 orcEx orcC 37
    (stripKW K203) KTEs [] C.sliceXs rfl
    (assumeOk_of σ KTEs AX C.KTEs_assume (asmX σ hge hlt))).1
  refine ⟨envAbs (B.GSf E) (run prog 4 m0WP orcEx 37 (stripKW K203)), ?_,
    outLogW_app σ (outLogW_of_logB KTEs C.KTEs_logB σ _) hM⟩
  rw [run_fr, mapState_nOnly e E σ (fun _ => rfl) KHs C.KHs_nOnly, run_add, hB]
  exact congrArg (fr M) hX

/-! ## Every count -/

/-- **`4 ≤ c < 8`.**  The entry, one pass of the body and the exit reach the exit cut `KTE`. -/
theorem x4w_runW_last (C : CutsW) (B : BodyW) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M)
    (hge : 4 ≤ σ 2) (hlt : σ 2 < 8) :
    ∃ e' M', run prog 4 mem0c orcC (16 + (BODYLEN + 37)) (fr M (mapState env0 σ entryWin)) =
        fr M' (mapState e' σ KTE) ∧
      OutLogW σ (KTE.mem.map (fun p => (mapAddr σ p.1, mapCell e' σ p.2)) ++ M') := by
  obtain ⟨e1, hentry, hrel⟩ := entry_runW env0 σ mem0c orcC M hw hM hge
  obtain ⟨e', hfin, hlog⟩ := first_exitW C B e1 σ mem0c orcC M hrel hM hge hlt
  refine ⟨e', M, ?_, hlog⟩
  rw [run_add, hentry]
  exact hfin

/-- **`c = 4 (j + 1) + s` with `4 ≤ s < 8`.**  The entry, the first pass with its tail, `j`
framed later passes and the final pass with the exit reach the exit cut `KTEs` at the residual
count `s`. -/
theorem x4w_runW (C : CutsW) (B : BodyW) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (j s : Nat) (hs : 4 ≤ s)
    (hs8 : s < 8) (hc : σ 2 = 4 * ((j : Int) + 1) + (s : Int)) :
    ∃ e' M', run prog 4 mem0c orcC (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 37))))
          (fr M (mapState env0 σ entryWin)) =
        fr M' (mapState e' (sItW (j + 1) σ) KTEs) ∧
      OutLogW (sItW (j + 1) σ) (KTEs.mem.map (fun p =>
        (mapAddr (sItW (j + 1) σ) p.1, mapCell e' (sItW (j + 1) σ) p.2)) ++ M') := by
  have hs4 : (4 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hge : 4 ≤ σ 2 := by rw [hc]; omega
  obtain ⟨e1, hentry, hrel⟩ := entry_runW env0 σ mem0c orcC M hw hM hge
  obtain ⟨e2, M2, hturn, hM2, hw2, hs2⟩ := first_turnW C B env0 e1 σ σ mem0c orcC M hw rfl hM
    hrel (by rw [hc]; omega)
  let σ1 : Nat → Int := sigmaOf tauW σ
  have hcount : σ1 2 = 4 * (j : Int) + (s : Int) := by
    show sigmaOf tauW σ 2 = 4 * (j : Int) + (s : Int)
    rw [tauW_count, hc]
    omega
  obtain ⟨e3, M3, hloop, hM3, hw3, hs3⟩ := loopW C B mem0c orcC s hs hs8 j e2 σ1 M2 hcount hM2 hw2 hs2
  have h2f : sItW j σ1 2 = (s : Int) := by
    rw [sItW_count, hcount]
    omega
  obtain ⟨e4, hfin, hM4⟩ := final_runW C B e3 (sItW j σ1) mem0c orcC M3 hw3 hs3 hM3
    (by rw [h2f]; exact hs4) (by rw [h2f]; exact_mod_cast hs8)
  refine ⟨e4, M3, ?_, ?_⟩
  · rw [run_add, hentry, run_add, hturn, run_add, hloop]
    exact hfin
  · show OutLogW (sItW j (sigmaOf tauW σ)) _
    exact hM4

end Hashtree.Proofs.WinAvxX4WLoop
