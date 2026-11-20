import Hashtree.Proofs.WinAvxX4WOutTail
import Hashtree.Proofs.WinAvxX4WOutDig1
import Hashtree.Proofs.WinAvxX4WOutDig2
import Hashtree.Proofs.WinAvxX4WAll
import Hashtree.Proofs.WinAvxX4WOut

/-!
# R2c — output correctness of the windows `avx_x4` W-mode loop (`TurnOut4W`, `TurnOut4WLast`)

Same route as `AvxX4LoopWOut` (linux): the windows pilot's invariant chain (`Gen.WinAvxX4P`) is
lifted to R2's W cuts.  R2's body slices (`WinAvxX4WBody` for the first pass, `WinAvxX4WBodyS`
for the later passes over the stripped cuts) are already checked with the pilot's trees; the
pilot's first three slices track nothing (`L3 = []`), so the lifted chains start at `L3`
(`WinAvxX4WOutInvW` / `…InvS`).  The four loop tails (turn / exit, first / later pass) are
re-checked with `T203` (`…Chk1/2`) and lifted from the pilot's exit slice (`…Tail`); every tail
cut's log is output cells of its 4 blocks plus cells of the kernel frame (`outShapeW4`), and its
digests come from the invariant at `L204` (`…Dig1/2`).  The passes compose along R2's
`WinAvxX4WLoop.x4w_runW` / `x4w_runW_last` (entry 16, first pass, `j` later passes, final pass).
`TurnOut4W` / `TurnOut4WLast` are R5's statements (`WinAvxX4WOut`), proved here; the local
`…Core` copies use `Avx512X16WOut.OutOk`, which has the text of `WinWrapper.OutOk`.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.AvxX4
open Hashtree.Gen.WinAvxX4P (K1 K2 K203 T0 T1 L203 L204)
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinLogW
open Hashtree.Proofs.WinAvxX4W
open Hashtree.Proofs.WinAvxX4WStrip (m0WP m0WP_eq stripKW KHs KTs KTEs tauW pushCW)
open Hashtree.Proofs.WinAvxX4WLoop
open Hashtree.Proofs.WinAvxX4WAll (cutsW)
open Hashtree.Proofs.WinAvxX4WBody (BODYLEN G203)
open Hashtree.Proofs.WinAvxX4WBodyS (GS203)
open Hashtree.Proofs.Avx512X16WOut (OutOk lookup_none outOk_append_left outOk_step' outOk_glue'
  hmem_of_envMem)

namespace Hashtree.Proofs.WinAvxX4WOut

/-! ## Input bytes -/

/-- A windows W-mode log never writes the input region. -/
theorem w4_view_rIn (M : CLog) (m : Addr Int → Cell W32 Int) (σ : Nat → Int) (a : Int)
    (hM : OutLogW σ M) : view M m ⟨rIn, a⟩ = m ⟨rIn, a⟩ := by
  have hn : lookup (⟨rIn, a⟩ : Addr Int) M = .ok none := by
    refine lookup_none _ M ?_
    intro p hp heq
    rcases hM p hp with h | ⟨h, _⟩
    · rw [heq] at h; simp [rIn, rOut] at h
    · rw [heq] at h; simp [rIn, rStack] at h
  simp only [view, hn]

theorem w4_hmem (e : Key → W32) (σ : Nat → Int) (M : CLog) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (hM : OutLogW σ M)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    HMem 256 inp (ecomb e σ (view M m)) :=
  hmem_of_envMem _ σ _ inp 256 (envMem_ecomb e σ (view M m))
    (fun o => by rw [w4_view_rIn M m σ _ hM]; exact hin o)

theorem w4_hmem_envAbs (inp : Nat → Byte) (e : Key → W32) (R : State E Lin)
    (h : HMem 256 inp e) : HMem 256 inp (envAbs e R) :=
  fun o ho => h o ho

theorem w4_hin_tau (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) (inp : Nat → Byte)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ o : Nat, mem0c ⟨rIn, sigmaOf tauW σ 0 + o⟩ = .dat ((inp (256 + o)).zeroExtend 32) 0 := by
  intro o
  rw [tauW_in, show σ 0 + 256 + (o : Int) = σ 0 + ((256 + o : Nat) : Int) by push_cast; omega]
  exact hin (256 + o)

/-! ## The shape of a tail cut's log -/

/-- The shape predicate of one pass's cells, relative to a symbol valuation. -/
def Cells (σ : Nat → Int) (lo : Int) (n : Int) (N : CLog) : Prop :=
  ∀ p ∈ N, (p.1.region = rOut ∧ lo ≤ p.1.off ∧ p.1.off < lo + n) ∨
    (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)

theorem w4_out_eval (σ : Nat → Int) (k : Int) : (⟨k, [0, 1]⟩ : Lin).eval σ = σ 1 + k := by
  show k + (0 * σ 0 + (1 * σ (0 + 1) + 0)) = σ 1 + k
  rw [show (0 + 1 : Nat) = 1 from rfl]
  omega

theorem outShapeW4_sound (K : State E Lin) (h : outShapeW4 K = true) (e : Key → W32)
    (σ : Nat → Int) : Cells σ (σ 1) 128 (mapState e σ K).mem := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simp only [outShapeW4, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨qr, qk, qc⟩, qcell⟩ := q
  rcases h _ hq with ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩ | ⟨⟨⟨hr, hc⟩, h0⟩, h1⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    left
    show rOut = rOut ∧ σ 1 ≤ (⟨qk, [0, 1]⟩ : Lin).eval σ ∧ (⟨qk, [0, 1]⟩ : Lin).eval σ < σ 1 + 128
    rw [w4_out_eval]
    exact ⟨rfl, by omega, by omega⟩
  · simp only at hr hc h0 h1
    subst hr; subst hc
    right
    show rStack = rStack ∧ σ 9 - 568 ≤ (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ ∧
      (⟨qk, Hashtree.Asm.X86SymW.stkC⟩ : Lin).eval σ < σ 9
    rw [sAtW_eval]
    exact ⟨rfl, by omega, by omega⟩

theorem w4_cells_ne (σ : Nat → Int) (lo n : Int) (N : CLog) (h : Cells σ lo n N) :
    ∀ p ∈ N, p.1.region = rOut → lo ≤ p.1.off := by
  intro p hp hr
  rcases h p hp with ⟨_, h2, _⟩ | ⟨h1, _, _⟩
  · exact h2
  · rw [hr] at h1; simp [rOut, rStack] at h1

/-! ## The entry (`entry_runW` with the environment kept) -/

theorem w4_entry (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (inp : Nat → Byte) (hw : WfMemW rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hge : 4 ≤ σ 2)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e1, run prog 4 mem0c orcC 16 (fr M (mapState env0 σ entryWin)) =
        fr M (mapState e1 σ (shiftKW K2)) ∧
      Mem0Rel e1 σ m0W (view M mem0c) ∧ HMem 256 inp e1 := by
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
  have hmE : HMem 256 inp E := w4_hmem env0 σ M mem0c inp hM hin
  refine ⟨envAbs (envAbs E (run prog 4 m0W orcE 8 entryWin)) (run prog 4 m0W orcB 8 K1W), ?_,
    mem0Rel_envAbs _ _ _ _ m0W_keyed hrel1 (run prog 4 m0W orcB 8 K1W),
    w4_hmem_envAbs inp _ _ (w4_hmem_envAbs inp _ _ hmE)⟩
  rw [run_fr, mapState_nOnly env0 E σ (fun _ => rfl) entryWin entryWin_nOnly]
  refine congrArg (fr M) ?_
  rw [show (16 : Nat) = 8 + 8 from rfl, run_add, r8]
  exact r8b

/-! ## The first pass -/

/-- The first pass and its loop tail (`c ≥ 8`), with the pass's cells and its 4 digests. -/
theorem w4_first_turn (env0 e1 : Key → W32) (σ0 σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (inp : Nat → Byte)
    (hw : WfMemW rodata [] env0 σ0 mem0c) (h9 : σ 9 = σ0 9) (hM : OutLogW σ M)
    (hrel : Mem0Rel e1 σ m0W (view M mem0c)) (hge : 8 ≤ σ 2) (hm : HMem 256 inp e1) :
    ∃ e' N, run prog 4 mem0c orcC TURNLEN (fr M (mapState e1 σ (shiftKW K2))) =
        fr (N ++ M) (mapState e' (sigmaOf tauW σ) KHs) ∧ OutLogW (sigmaOf tauW σ) (N ++ M) ∧
      WfMemW rodata [] e' (sigmaOf tauW σ) (view (N ++ M) mem0c) ∧
      SaveOk (sigmaOf tauW σ) (view (N ++ M) mem0c) ∧
      Cells σ (σ 1) 128 N ∧ OutOk inp (σ 1) 4 N := by
  have hB : run prog 4 (view M mem0c) orcC BODYLEN (mapState e1 σ (shiftKW K2)) =
      mapState (G203 e1) σ (shiftKW K203) :=
    Hashtree.Proofs.WinAvxX4WBody.body_runW e1 σ (view M mem0c) orcC hrel (by omega)
  have hm2 : Mem0Rel (G203 e1) σ m0W (view M mem0c) :=
    Hashtree.Proofs.WinAvxX4WBody.body_memW e1 σ (view M mem0c) hrel
  have hT := (slice_sound (G203 e1) σ m0W (view M mem0c) hm2 prog 4 orcB orcC 25
    (shiftKW K203) KT [] cutsW.sliceT rfl
    (assumeOk_of σ KT AT cutsW.KT_assume (asmT σ hge))).1
  have hI : InvC inp (envAbs (G203 e1) (run prog 4 m0W orcB 25 (shiftKW K203))) L204 :=
    w4stepT_turn inp (G203 e1) (w4invW_body inp e1 hm) hm
  obtain ⟨e2, he2⟩ : ∃ e2, e2 = envAbs (G203 e1) (run prog 4 m0W orcB 25 (shiftKW K203)) :=
    ⟨_, rfl⟩
  rw [← he2] at hT hI
  have hL : OutLogW σ (KT.mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M) :=
    outLogW_app σ (outLogW_of_logB KT cutsW.KT_logB σ e2) hM
  have hL' : OutLogW (sigmaOf tauW σ)
      (KT.mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M) :=
    outLogW_s9 _ (tauW_s9 σ) hL
  refine ⟨e2, KT.mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)), ?_, hL', ?_, ?_, ?_, ?_⟩
  · rw [run_fr, TURNLEN, run_add, hB, hT, turn_step1 cutsW e2 σ, fr_app]
  · exact wfW_view rodata env0 e2 (sigmaOf tauW σ) mem0c _ hL'
      (wfMemW_s9 rodata env0 σ0 (sigmaOf tauW σ) mem0c hw (by rw [tauW_s9, h9]))
  · exact saveOk_of_pass1 cutsW e2 σ (sigmaOf tauW σ) mem0c M (tauW_s9 σ)
  · exact outShapeW4_sound KT w4shape_KT e2 σ
  · exact w4outOk_KT inp e2 σ hI

/-- The first pass and the exit (`4 ≤ c < 8`), with its cells and its 4 digests. -/
theorem w4_first_exit (e1 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (inp : Nat → Byte)
    (hrel : Mem0Rel e1 σ m0W (view M mem0c)) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8)
    (hm : HMem 256 inp e1) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 37) (fr M (mapState e1 σ (shiftKW K2))) =
        fr M (mapState e' σ KTE) ∧
      Cells σ (σ 1) 128 (mapState e' σ KTE).mem ∧ OutOk inp (σ 1) 4 (mapState e' σ KTE).mem := by
  have hB : run prog 4 (view M mem0c) orcC BODYLEN (mapState e1 σ (shiftKW K2)) =
      mapState (G203 e1) σ (shiftKW K203) :=
    Hashtree.Proofs.WinAvxX4WBody.body_runW e1 σ (view M mem0c) orcC hrel hge
  have hm2 : Mem0Rel (G203 e1) σ m0W (view M mem0c) :=
    Hashtree.Proofs.WinAvxX4WBody.body_memW e1 σ (view M mem0c) hrel
  have hX := (slice_sound (G203 e1) σ m0W (view M mem0c) hm2 prog 4 orcEx orcC 37
    (shiftKW K203) KTE [] cutsW.sliceX rfl
    (assumeOk_of σ KTE AX cutsW.KTE_assume (asmX σ hge hlt))).1
  have hI : InvC inp (envAbs (G203 e1) (run prog 4 m0W orcEx 37 (shiftKW K203))) L204 :=
    w4stepT_exit inp (G203 e1) (w4invW_body inp e1 hm) hm
  obtain ⟨e2, he2⟩ : ∃ e2, e2 = envAbs (G203 e1) (run prog 4 m0W orcEx 37 (shiftKW K203)) :=
    ⟨_, rfl⟩
  rw [← he2] at hX hI
  refine ⟨e2, ?_, outShapeW4_sound KTE w4shape_KTE e2 σ, w4outOk_KTE inp e2 σ hI⟩
  rw [run_fr, run_add, hB]
  exact congrArg (fr M) hX

/-! ## The later passes -/

/-- One framed later pass and its loop tail (`c ≥ 8`), with the pass's cells and 4 digests. -/
theorem w4_iter (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (e : Key → W32)
    (σ : Nat → Int) (M : CLog) (inp : Nat → Byte)
    (hw : WfMemW rodata [] e σ (view M mem0c)) (hs : SaveOk σ (view M mem0c))
    (hM : OutLogW σ M) (hge : 8 ≤ σ 2)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e' N, run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHs)) =
        fr (N ++ M) (mapState e' (sigmaOf tauW σ) KHs) ∧ OutLogW (sigmaOf tauW σ) (N ++ M) ∧
      WfMemW rodata [] e' (sigmaOf tauW σ) (view (N ++ M) mem0c) ∧
      SaveOk (sigmaOf tauW σ) (view (N ++ M) mem0c) ∧
      Cells σ (σ 1) 128 N ∧ OutOk inp (σ 1) 4 N := by
  obtain ⟨E, hE⟩ : ∃ E, E = ecomb e σ (view M mem0c) := ⟨_, rfl⟩
  have hwE : WfMemW rodata pushCW E σ (view M mem0c) := by
    rw [hE]; exact wfP_of_saveOk e σ (view M mem0c) hw hs
  have hrel : Mem0Rel E σ m0WP (view M mem0c) := by
    rw [m0WP_eq]
    have h := mem0RelW_of_wf rodata pushCW E σ (view M mem0c) hwE
      (by rw [hE]; exact envMem_ecomb e σ (view M mem0c))
    exact h
  have hmE : HMem 256 inp E := by rw [hE]; exact w4_hmem e σ M mem0c inp hM hin
  have hB : run prog 4 (view M mem0c) orcC BODYLEN (mapState E σ KHs) =
      mapState (GS203 E) σ (stripKW K203) :=
    Hashtree.Proofs.WinAvxX4WBodyS.bodyS_runW E σ (view M mem0c) orcC hrel (by omega)
  have hm2 : Mem0Rel (GS203 E) σ m0WP (view M mem0c) :=
    Hashtree.Proofs.WinAvxX4WBodyS.bodyS_memW E σ (view M mem0c) hrel
  have hT := (slice_sound (GS203 E) σ m0WP (view M mem0c) hm2 prog 4 orcB orcC 25 (stripKW K203)
    KTs [] cutsW.sliceTs rfl (assumeOk_of σ KTs AT cutsW.KTs_assume (asmT σ hge))).1
  have hI : InvC inp (envAbs (GS203 E) (run prog 4 m0WP orcB 25 (stripKW K203))) L204 :=
    w4stepT_turnS inp (GS203 E) (w4invS_body inp E hmE) hmE
  obtain ⟨e1, he1⟩ : ∃ e1, e1 = envAbs (GS203 E) (run prog 4 m0WP orcB 25 (stripKW K203)) :=
    ⟨_, rfl⟩
  rw [← he1] at hT hI
  have hne : ∀ i, e (.n i) = E (.n i) := by intro i; rw [hE]; rfl
  have hrun : run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ KHs)) =
      fr M (mapState e1 σ KTs) := by
    rw [run_fr, mapState_nOnly e E σ hne KHs cutsW.KHs_nOnly, TURNLEN, run_add, hB]
    exact congrArg (fr M) hT
  have hL : OutLogW σ (KTs.mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M) :=
    outLogW_app σ (outLogW_of_logB KTs cutsW.KTs_logB σ e1) hM
  have hL' : OutLogW (sigmaOf tauW σ)
      (KTs.mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M) :=
    outLogW_s9 _ (tauW_s9 σ) hL
  refine ⟨e1, KTs.mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)), ?_, hL', ?_, ?_, ?_, ?_⟩
  · rw [hrun, turn_stepS cutsW e1 σ, fr_app]
  · rw [view_append]
    exact wfW_view rodata e e1 (sigmaOf tauW σ) (view M mem0c) _
      (outLogW_s9 _ (tauW_s9 σ) (outLogW_of_logB KTs cutsW.KTs_logB σ e1))
      (wfMemW_s9 rodata e σ (sigmaOf tauW σ) (view M mem0c) hw (tauW_s9 σ))
  · rw [view_append]
    exact saveOk_step cutsW e1 σ (sigmaOf tauW σ) (tauW_s9 σ) (view M mem0c) hs
  · exact outShapeW4_sound KTs w4shape_KTs e1 σ
  · exact w4outOk_KTs inp e1 σ hI

/-- The final later pass and the exit (`4 ≤ c < 8`), with its cells and its 4 digests. -/
theorem w4_final (e : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (M : CLog) (inp : Nat → Byte)
    (hw : WfMemW rodata [] e σ (view M mem0c)) (hs : SaveOk σ (view M mem0c))
    (hM : OutLogW σ M) (hge : 4 ≤ σ 2) (hlt : σ 2 < 8)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 37) (fr M (mapState e σ KHs)) =
        fr M (mapState e' σ KTEs) ∧
      Cells σ (σ 1) 128 (mapState e' σ KTEs).mem ∧ OutOk inp (σ 1) 4 (mapState e' σ KTEs).mem := by
  obtain ⟨E, hE⟩ : ∃ E, E = ecomb e σ (view M mem0c) := ⟨_, rfl⟩
  have hwE : WfMemW rodata pushCW E σ (view M mem0c) := by
    rw [hE]; exact wfP_of_saveOk e σ (view M mem0c) hw hs
  have hrel : Mem0Rel E σ m0WP (view M mem0c) := by
    rw [m0WP_eq]
    have h := mem0RelW_of_wf rodata pushCW E σ (view M mem0c) hwE
      (by rw [hE]; exact envMem_ecomb e σ (view M mem0c))
    exact h
  have hmE : HMem 256 inp E := by rw [hE]; exact w4_hmem e σ M mem0c inp hM hin
  have hB : run prog 4 (view M mem0c) orcC BODYLEN (mapState E σ KHs) =
      mapState (GS203 E) σ (stripKW K203) :=
    Hashtree.Proofs.WinAvxX4WBodyS.bodyS_runW E σ (view M mem0c) orcC hrel hge
  have hm2 : Mem0Rel (GS203 E) σ m0WP (view M mem0c) :=
    Hashtree.Proofs.WinAvxX4WBodyS.bodyS_memW E σ (view M mem0c) hrel
  have hX := (slice_sound (GS203 E) σ m0WP (view M mem0c) hm2 prog 4 orcEx orcC 37
    (stripKW K203) KTEs [] cutsW.sliceXs rfl
    (assumeOk_of σ KTEs AX cutsW.KTEs_assume (asmX σ hge hlt))).1
  have hI : InvC inp (envAbs (GS203 E) (run prog 4 m0WP orcEx 37 (stripKW K203))) L204 :=
    w4stepT_exitS inp (GS203 E) (w4invS_body inp E hmE) hmE
  obtain ⟨e1, he1⟩ : ∃ e1, e1 = envAbs (GS203 E) (run prog 4 m0WP orcEx 37 (stripKW K203)) :=
    ⟨_, rfl⟩
  rw [← he1] at hX hI
  have hne : ∀ i, e (.n i) = E (.n i) := by intro i; rw [hE]; rfl
  refine ⟨e1, ?_, outShapeW4_sound KTEs w4shape_KTEs e1 σ, w4outOk_KTEs inp e1 σ hI⟩
  rw [run_fr, mapState_nOnly e E σ hne KHs cutsW.KHs_nOnly, run_add, hB]
  exact congrArg (fr M) hX

/-- `j` framed later passes from the stripped head at `c = 4 j + s`, `4 ≤ s < 8`: the passes'
cells are the output cells `[σ 1, σ 1 + 128 j)` and frame cells, holding blocks `0 .. 4 j - 1`. -/
theorem w4_loop (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (s : Nat) (hs : 4 ≤ s)
    (hs8 : s < 8) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog) (inp : Nat → Byte),
      σ 2 = 4 * (j : Int) + (s : Int) → OutLogW σ M →
      WfMemW rodata [] e σ (view M mem0c) → SaveOk σ (view M mem0c) →
      (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
      ∃ e' N, run prog 4 mem0c orcC (j * TURNLEN) (fr M (mapState e σ KHs)) =
          fr (N ++ M) (mapState e' (sItW j σ) KHs) ∧ OutLogW (sItW j σ) (N ++ M) ∧
        WfMemW rodata [] e' (sItW j σ) (view (N ++ M) mem0c) ∧
        SaveOk (sItW j σ) (view (N ++ M) mem0c) ∧
        Cells σ (σ 1) (128 * (j : Int)) N ∧ OutOk inp (σ 1) (4 * j) N := by
  intro j
  induction j with
  | zero =>
    intro e σ M inp hσ hM hw hsv hin
    refine ⟨e, [], rfl, hM, hw, hsv, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro n i b hn
      exact absurd hn (Nat.not_lt_zero n)
  | succ j ih =>
    intro e σ M inp hσ hM hw hsv hin
    have hge : 8 ≤ σ 2 := by
      rw [hσ]
      have hsj : (4 : Int) ≤ (s : Int) := by exact_mod_cast hs
      push_cast
      omega
    obtain ⟨e1, N1, hrun, hM1, hw1, hs1, hsh1, hout1⟩ := w4_iter mem0c orcC e σ M inp hw hsv hM hge hin
    have hσ1 : sigmaOf tauW σ 2 = 4 * (j : Int) + (s : Int) := by
      rw [tauW_count, hσ]
      push_cast
      omega
    obtain ⟨e2, N2, hrun2, hM2, hw2, hs2, hsh2, hout2⟩ :=
      ih e1 (sigmaOf tauW σ) (N1 ++ M) (fun o => inp (256 + o)) hσ1 hM1 hw1 hs1
        (w4_hin_tau mem0c σ inp hin)
    have hassoc : N2 ++ N1 ++ M = N2 ++ (N1 ++ M) := List.append_assoc N2 N1 M
    refine ⟨e2, N2 ++ N1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hlen : (j + 1) * TURNLEN = TURNLEN + j * TURNLEN := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [hlen, run_add, hrun, hrun2, hassoc]
      rfl
    · rw [hassoc]; exact hM2
    · rw [hassoc]; exact hw2
    · rw [hassoc]; exact hs2
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · rcases hsh2 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rw [tauW_out] at h2 h3
          left; refine ⟨h1, ?_, ?_⟩ <;> push_cast <;> omega
        · rw [tauW_s9] at h2 h3
          right; exact ⟨h1, h2, h3⟩
      · rcases hsh1 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · left; refine ⟨h1, ?_, ?_⟩ <;> push_cast <;> omega
        · right; exact ⟨h1, h2, h3⟩
    · rw [show 4 * (j + 1) = 4 + 4 * j by omega]
      refine outOk_glue' inp (σ 1) 4 (4 * j) N2 N1 ?_ hout1 ?_
      · intro p hp hr
        have h := w4_cells_ne _ _ _ N2 hsh2 p hp hr
        rw [tauW_out] at h; push_cast; omega
      · rw [tauW_out] at hout2
        have : (σ 1 + 128 : Int) = σ 1 + 32 * ((4 : Nat) : Int) := by push_cast; omega
        rw [this] at hout2
        exact hout2

/-! ## The statements, with `Avx512X16WOut.OutOk` -/

def TurnOut4WCore : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (j s : Nat) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86Win.AvxX4.rodata [] env0 σ mem0c →
    Hashtree.Proofs.WinLogW.OutLogW σ M → 4 ≤ s → s < 8 →
    σ 2 = 4 * ((j : Int) + 1) + (s : Int) →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86Win.AvxX4.prog 4 mem0c orcC (x4wRunSteps j)
        (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 128 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (4 * (j + 2))
      (run Hashtree.Kernels.X86Win.AvxX4.prog 4 mem0c orcC (x4wRunSteps j)
        (fr M (mapState env0 σ entryWin))).mem

def TurnOut4WLastCore : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Byte),
    WfMemW Hashtree.Kernels.X86Win.AvxX4.rodata [] env0 σ mem0c →
    Hashtree.Proofs.WinLogW.OutLogW σ M → 4 ≤ σ 2 → σ 2 < 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86Win.AvxX4.prog 4 mem0c orcC x4wLastSteps
        (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 128) ∨
        (p.1.region = rStack ∧ σ 9 - 568 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 4
      (run Hashtree.Kernels.X86Win.AvxX4.prog 4 mem0c orcC x4wLastSteps
        (fr M (mapState env0 σ entryWin))).mem

/-! ## `4 ≤ c < 8` -/

theorem turnOut4WLastCore : TurnOut4WLastCore := by
  intro env0 σ mem0c orcC M inp hw hM hge hlt hin
  obtain ⟨e1, hentry, hrel, hm1⟩ := w4_entry env0 σ mem0c orcC M inp hw hM hge hin
  obtain ⟨e', hfin, hsh, hout⟩ := w4_first_exit e1 σ mem0c orcC M inp hrel hge hlt hm1
  have hall : run prog 4 mem0c orcC x4wLastSteps (fr M (mapState env0 σ entryWin)) =
      fr M (mapState e' σ KTE) := by
    show run prog 4 mem0c orcC (16 + (BODYLEN + 37)) (fr M (mapState env0 σ entryWin)) = _
    have sA := run_add prog 4 mem0c orcC 16 (BODYLEN + 37) (fr M (mapState env0 σ entryWin))
    rw [sA, hentry]
    exact hfin
  rw [hall]
  show (∀ p ∈ (mapState e' σ KTE).mem ++ M, _) ∧ OutOk inp (σ 1) 4 ((mapState e' σ KTE).mem ++ M)
  refine ⟨?_, outOk_append_left inp (σ 1) 4 _ M hout⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · rcases hsh p h with h1 | h1
    · right; left; exact h1
    · right; right; exact h1
  · left; exact h

/-! ## `c = 4 (j + 1) + s`, `4 ≤ s < 8` -/

theorem turnOut4WCore : TurnOut4WCore := by
  intro env0 σ mem0c orcC M j s inp hw hM hs hs8 hc hin
  have hs4 : (4 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hge : 4 ≤ σ 2 := by rw [hc]; omega
  -- the entry and the first pass
  obtain ⟨e1, hentry, hrel, hm1⟩ := w4_entry env0 σ mem0c orcC M inp hw hM hge hin
  obtain ⟨e2, N1, hturn, hM2, hw2, hs2, hsh1, hout1⟩ :=
    w4_first_turn env0 e1 σ σ mem0c orcC M inp hw rfl hM hrel (by rw [hc]; omega) hm1
  -- the later passes
  have hcount : sigmaOf tauW σ 2 = 4 * (j : Int) + (s : Int) := by
    rw [tauW_count, hc]
    omega
  obtain ⟨e3, N2, hloop, hM3, hw3, hs3, hsh2, hout2⟩ :=
    w4_loop mem0c orcC s hs hs8 j e2 (sigmaOf tauW σ) (N1 ++ M) (fun o => inp (256 + o))
      hcount hM2 hw2 hs2 (w4_hin_tau mem0c σ inp hin)
  -- the final pass
  obtain ⟨σ2, hσ2def⟩ : ∃ σ2 : Nat → Int, σ2 = sItW j (sigmaOf tauW σ) := ⟨_, rfl⟩
  rw [← hσ2def] at hloop hM3 hw3 hs3
  have hσ2_2 : σ2 2 = (s : Int) := by rw [hσ2def, sItW_count, hcount]; omega
  have hin2 : ∀ o : Nat,
      mem0c ⟨rIn, σ2 0 + o⟩ = .dat ((inp (256 * (j + 1) + o)).zeroExtend 32) 0 := by
    intro o
    rw [hσ2def, sItW_in, tauW_in,
      show σ 0 + 256 + 256 * (j : Int) + (o : Int) = σ 0 + ((256 * (j + 1) + o : Nat) : Int) by
        push_cast; omega]
    exact hin _
  obtain ⟨e4, hfin, hsh3, hout3⟩ :=
    w4_final e3 σ2 mem0c orcC (N2 ++ (N1 ++ M)) (fun o => inp (256 * (j + 1) + o)) hw3 hs3 hM3
      (by rw [hσ2_2]; exact hs4) (by rw [hσ2_2]; exact_mod_cast hs8) hin2
  -- the whole run
  have hall : run prog 4 mem0c orcC (x4wRunSteps j) (fr M (mapState env0 σ entryWin)) =
      fr (N2 ++ (N1 ++ M)) (mapState e4 σ2 KTEs) := by
    show run prog 4 mem0c orcC (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 37))))
      (fr M (mapState env0 σ entryWin)) = _
    have sA := run_add prog 4 mem0c orcC 16 (TURNLEN + (j * TURNLEN + (BODYLEN + 37)))
      (fr M (mapState env0 σ entryWin))
    have sB := run_add prog 4 mem0c orcC TURNLEN (j * TURNLEN + (BODYLEN + 37))
      (fr M (mapState e1 σ (shiftKW K2)))
    have sC := run_add prog 4 mem0c orcC (j * TURNLEN) (BODYLEN + 37)
      (fr (N1 ++ M) (mapState e2 (sigmaOf tauW σ) KHs))
    rw [sA, hentry, sB, hturn, sC, hloop]
    exact hfin
  -- symbols of the cuts
  have hσ2_1 : σ2 1 = σ 1 + 128 * ((j + 1 : Nat) : Int) := by
    rw [hσ2def, sItW_out, tauW_out]
    push_cast
    omega
  have hσ1_1 : sigmaOf tauW σ 1 = σ 1 + 128 := tauW_out σ
  have hσ2_9 : σ2 9 = σ 9 := by rw [hσ2def, sItW_s9, tauW_s9]
  have hσ1_9 : sigmaOf tauW σ 9 = σ 9 := tauW_s9 σ
  rw [hall]
  show (∀ p ∈ (mapState e4 σ2 KTEs).mem ++ (N2 ++ (N1 ++ M)), _) ∧
    OutOk inp (σ 1) (4 * (j + 2)) ((mapState e4 σ2 KTEs).mem ++ (N2 ++ (N1 ++ M)))
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · rcases hsh3 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [hσ2_1] at h2 h3
        right; left; refine ⟨h1, ?_, ?_⟩ <;> push_cast at h2 h3 ⊢ <;> omega
      · rw [hσ2_9] at h2 h3
        right; right; exact ⟨h1, h2, h3⟩
    · rcases List.mem_append.mp h with h | h
      · rcases hsh2 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rw [hσ1_1] at h2 h3
          right; left; refine ⟨h1, ?_, ?_⟩ <;> push_cast at h3 ⊢ <;> omega
        · rw [hσ1_9] at h2 h3
          right; right; exact ⟨h1, h2, h3⟩
      · rcases List.mem_append.mp h with h | h
        · rcases hsh1 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · right; left; refine ⟨h1, ?_, ?_⟩ <;> push_cast <;> omega
          · right; right; exact ⟨h1, h2, h3⟩
        · left; exact h
  · have hlow : OutOk inp (σ 1) (4 * (j + 1)) (N2 ++ (N1 ++ M)) := by
      rw [show 4 * (j + 1) = 4 + 4 * j by omega]
      refine outOk_glue' inp (σ 1) 4 (4 * j) N2 (N1 ++ M) ?_
        (outOk_append_left inp (σ 1) 4 N1 M hout1) ?_
      · intro p hp hr
        have h := w4_cells_ne _ _ _ N2 hsh2 p hp hr
        rw [hσ1_1] at h; push_cast; omega
      · rw [hσ1_1] at hout2
        have : (σ 1 + 128 : Int) = σ 1 + 32 * ((4 : Nat) : Int) := by push_cast; omega
        rw [this] at hout2
        exact hout2
    rw [show 4 * (j + 2) = 4 * (j + 1) + 4 by omega]
    refine outOk_step' inp (σ 1) (4 * (j + 1)) 4 _ (N2 ++ (N1 ++ M)) ?_ hlow ?_
    · intro p hp hr
      have h := w4_cells_ne _ _ _ _ hsh3 p hp hr
      rw [hσ2_1] at h; push_cast at h ⊢; omega
    · rw [hσ2_1] at hout3
      have : (σ 1 + 128 * ((j + 1 : Nat) : Int) : Int) = σ 1 + 32 * ((4 * (j + 1) : Nat) : Int) := by
        push_cast; omega
      rw [this] at hout3
      have h64 : (fun o => inp (256 * (j + 1) + o)) = (fun o => inp (64 * (4 * (j + 1)) + o)) := by
        funext o; exact congrArg inp (by omega)
      rw [h64] at hout3
      exact hout3

/-! ## R5's statements -/

/-- **`TurnOut4W`** (R5's statement, `WinWrapper.OutOk`). -/
theorem turnOut4W : TurnOut4W := by
  unfold TurnOut4W Hashtree.Proofs.WinWrapper.OutOk
  have h := turnOut4WCore
  unfold TurnOut4WCore OutOk at h
  exact h

/-- **`TurnOut4WLast`** (R5's statement, `WinWrapper.OutOk`). -/
theorem turnOut4WLast : TurnOut4WLast := by
  unfold TurnOut4WLast Hashtree.Proofs.WinWrapper.OutOk
  have h := turnOut4WLastCore
  unfold TurnOut4WLastCore OutOk at h
  exact h

end Hashtree.Proofs.WinAvxX4WOut
