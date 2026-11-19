import Hashtree.Proofs.WinAvx2X8WOutInvR8
import Hashtree.Proofs.WinAvx2X8WOutInvR24
import Hashtree.Proofs.WinAvx2X8WOutCelT8
import Hashtree.Proofs.WinAvx2X8WOutCelX8
import Hashtree.Proofs.WinAvx2X8WOutCelTS8
import Hashtree.Proofs.WinAvx2X8WOutCelXS8
import Hashtree.Proofs.WinAvx2X8WOutCelT24
import Hashtree.Proofs.WinAvx2X8WOutCelX24
import Hashtree.Proofs.WinAvx2X8WOutCelTS24
import Hashtree.Proofs.WinAvx2X8WOutCelXS24
import Hashtree.Proofs.WinAvx2X8WOutShpT8
import Hashtree.Proofs.WinAvx2X8WOutShpX8
import Hashtree.Proofs.WinAvx2X8WOutShpTS8
import Hashtree.Proofs.WinAvx2X8WOutShpXS8
import Hashtree.Proofs.WinAvx2X8WOutShpT24
import Hashtree.Proofs.WinAvx2X8WOutShpX24
import Hashtree.Proofs.WinAvx2X8WOutShpTS24
import Hashtree.Proofs.WinAvx2X8WOutShpXS24
import Hashtree.Proofs.WinAvx2X8WAll
import Hashtree.Proofs.WinAvx2X8WOut

/-!
# R2c — output correctness of the windows `avx2_x8` W-mode loop (`TurnOut8W`, `TurnOut8WLast`)

Same route as the linux `Avx2X8WOut` and the windows `WinAvxX4WOutAll`: the windows pilot's
invariant chain (`Gen.WinAvx2X8P`) is lifted to R5's W cuts at both ABI residues
(`WinAvx2X8WOutInvR{8,24}`: R5's body slices are already checked with the pilot's trees, the
pilot tracks nothing up to `K4`, so the chains start at `L3`; only the four tails per residue are
re-checked with `T211`, `WinAvx2X8WOutChk*`).  One pass's log is output cells of its 8 blocks plus
cells of the kernel frame (`outShape8W`, `WinAvx2X8WOutShp*`), the digests come from the invariant at
`L212` through one table of the pilot's 256 output cells (`outOk_tab8w`, cells `WinAvx2X8WOutCel*`),
and the passes compose along R5's `WinAvx2X8WLoop.x8w_runW` / `x8w_runW_last` (entry 24, first
pass, `j` later passes, final pass) for a residue `r`; the residue is selected by
`WinAvx2X8WAll.residue_cases`.  `TurnOut8W` / `TurnOut8WLast` are R5's statements
(`WinAvx2X8WOut`), proved here; the local `…Core` copies use `Avx512X16WOut.OutOk`, which has
the text of `WinWrapper.OutOk`.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P (K2 K3 K211 T2 L212)
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinLogW
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip
open Hashtree.Proofs.WinAvx2X8WLoop
open Hashtree.Proofs.WinAvx2X8WAll (cutsW_8 bodyW_8 cutsW_24 bodyW_24 residue_cases)
open Hashtree.Proofs.Avx512X16WOut (OutOk lookup_none outOk_append_left outOk_step' outOk_glue'
  hmem_of_envMem)

namespace Hashtree.Proofs.WinAvx2X8WOut

/-! ## Input bytes -/

/-- A windows W-mode log never writes the input region. -/
theorem w8_view_rIn (M : CLog) (m : Addr Int → Cell W32 Int) (σ : Nat → Int) (a : Int)
    (hM : OutLogW σ M) : view M m ⟨rIn, a⟩ = m ⟨rIn, a⟩ := by
  have hn : lookup (⟨rIn, a⟩ : Addr Int) M = .ok none := by
    refine lookup_none _ M ?_
    intro p hp heq
    rcases hM p hp with h | ⟨h, _⟩
    · rw [heq] at h; simp [rIn, rOut] at h
    · rw [heq] at h; simp [rIn, rStack] at h
  simp only [view, hn]

theorem w8_hmem (e : Key → W32) (σ : Nat → Int) (M : CLog) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (hM : OutLogW σ M)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    HMem 512 inp (ecomb e σ (view M m)) :=
  hmem_of_envMem _ σ _ inp 512 (envMem_ecomb e σ (view M m))
    (fun o => by rw [w8_view_rIn M m σ _ hM]; exact hin o)

theorem w8_hmem_envAbs (inp : Nat → Byte) (e : Key → W32) (R : State E Lin)
    (h : HMem 512 inp e) : HMem 512 inp (envAbs e R) :=
  fun o ho => h o ho

theorem w8_hin_tau (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) (inp : Nat → Byte)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ o : Nat, mem0c ⟨rIn, sigmaOf tau8 σ 0 + o⟩ = .dat ((inp (512 + o)).zeroExtend 32) 0 := by
  intro o
  rw [tau8_in, show σ 0 + 512 + (o : Int) = σ 0 + ((512 + o : Nat) : Int) by push_cast; omega]
  exact hin (512 + o)

/-- The write log of a mapped cut (stated once, for a variable cut, so that the concrete cuts are
never unfolded). -/
theorem w8_mapState_mem (e : Key → W32) (σ : Nat → Int) (K : State E Lin) :
    (mapState e σ K).mem = K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)) := rfl

/-! ## The shape of a pass's log -/

/-- The shape predicate of one pass's cells, relative to a symbol valuation. -/
def Cells8 (σ : Nat → Int) (lo : Int) (n : Int) (N : CLog) : Prop :=
  ∀ p ∈ N, (p.1.region = rOut ∧ lo ≤ p.1.off ∧ p.1.off < lo + n) ∨
    (p.1.region = rStack ∧ σ 9 - 1296 ≤ p.1.off ∧ p.1.off < σ 9)

theorem cells8_ne (σ : Nat → Int) (lo n : Int) (N : CLog) (h : Cells8 σ lo n N) :
    ∀ p ∈ N, p.1.region = rOut → lo ≤ p.1.off := by
  intro p hp hr
  rcases h p hp with ⟨_, h2, _⟩ | ⟨h1, _, _⟩
  · exact h2
  · rw [hr] at h1; simp [rOut, rStack] at h1

/-! ## The output facts of a residue -/

/-- The four tails of residue `r` reach `L212` from the lifted pass chains, and their cuts have
the pilot's output cells and a log of a pass's shape. -/
structure OutR8 (r : Nat) (B : BodyW r) : Prop where
  invT : ∀ (inp : Nat → Byte) (e1 : Key → W32), HMem 512 inp e1 →
    InvC inp (envAbs (B.Gf e1) (run prog 4 m8W orcB 24 (shiftK8 r K211))) L212
  invX : ∀ (inp : Nat → Byte) (e1 : Key → W32), HMem 512 inp e1 →
    InvC inp (envAbs (B.Gf e1) (run prog 4 m8W orcEx 42 (shiftK8 r K211))) L212
  invTS : ∀ (inp : Nat → Byte) (e1 : Key → W32), HMem 512 inp e1 →
    InvC inp (envAbs (B.GSf e1) (run prog 4 (m8P r) orcB 24 (stripK8 r K211))) L212
  invXS : ∀ (inp : Nat → Byte) (e1 : Key → W32), HMem 512 inp e1 →
    InvC inp (envAbs (B.GSf e1) (run prog 4 (m8P r) orcEx 42 (stripK8 r K211))) L212
  cT : tab8w.all (fun t => outCell (KT r) t.1 t.2.1 t.2.2) = true
  cX : tab8w.all (fun t => outCell (KTE r) t.1 t.2.1 t.2.2) = true
  cTS : tab8w.all (fun t => outCell (KTs r) t.1 t.2.1 t.2.2) = true
  cXS : tab8w.all (fun t => outCell (KTEs r) t.1 t.2.1 t.2.2) = true
  sT : outShape8W (KT r) = true
  sX : outShape8W (KTE r) = true
  sTS : outShape8W (KTs r) = true
  sXS : outShape8W (KTEs r) = true

theorem outR_8 : OutR8 8 bodyW_8 :=
  { invT := invT8, invX := invX8, invTS := invTS8, invXS := invXS8,
    cT := cellsT_8, cX := cellsX_8, cTS := cellsTS_8, cXS := cellsXS_8,
    sT := shapeT_8, sX := shapeX_8, sTS := shapeTS_8, sXS := shapeXS_8 }

theorem outR_24 : OutR8 24 bodyW_24 :=
  { invT := invT24, invX := invX24, invTS := invTS24, invXS := invXS24,
    cT := cellsT_24, cX := cellsX_24, cTS := cellsTS_24, cXS := cellsXS_24,
    sT := shapeT_24, sX := shapeX_24, sTS := shapeTS_24, sXS := shapeXS_24 }

/-! ## The entry (`entry_runW` with the input bytes of the environment) -/

theorem w8_entry {r : Nat} (C : CutsW r) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (inp : Nat → Byte)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (hge : 8 ≤ σ 2)
    (hr : (r : Int) = (σ 9 - 16) % 32)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e1, run prog 4 mem0c orcC 24 (fr M (mapState env0 σ entryWin)) =
        fr M (mapState e1 σ (shiftK8 r K3)) ∧
      Mem0Rel e1 σ m8W (view M mem0c) ∧ HMem 512 inp e1 := by
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
  have hmE : HMem 512 inp E := w8_hmem env0 σ M mem0c inp hM hin
  refine ⟨envAbs (envAbs (envAbs E (run prog 4 m8W orcNZ 6 entryWin))
      (run prog 4 m8W orcB 9 (x8A r))) (run prog 4 m8W orcB 8 (K2W r)), ?_,
    mem0Rel_envAbs _ _ _ _ m8W_keyed hrel2 (run prog 4 m8W orcB 8 (K2W r)),
    w8_hmem_envAbs inp _ _ (w8_hmem_envAbs inp _ _ (w8_hmem_envAbs inp _ _ hmE))⟩
  rw [run_fr, mapState_nOnly env0 E σ (fun _ => rfl) entryWin entryWin_nOnly]
  refine congrArg (fr M) ?_
  rw [show (24 : Nat) = 6 + (1 + (9 + 8)) from rfl, run_add, r6, run_add, r1, run_add, r9]
  exact r8

/-! ## The first pass -/

/-- The first pass and its loop tail (`c ≥ 16`, mirrors `first_turnW`), with the pass's cells
and its 8 digests. -/
theorem w8_first_turn {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR8 r B) (env0 e1 : Key → W32)
    (σ0 σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (inp : Nat → Byte)
    (hw : WfMemW rodata [] env0 σ0 mem0c) (h9 : σ 9 = σ0 9) (hM : OutLogW σ M)
    (hrel : Mem0Rel e1 σ m8W (view M mem0c)) (hge : 16 ≤ σ 2) (hm : HMem 512 inp e1) :
    ∃ e' N, run prog 4 mem0c orcC TURNLEN (fr M (mapState e1 σ (shiftK8 r K3))) =
        fr (N ++ M) (mapState e' (sigmaOf tau8 σ) (KHs r)) ∧ OutLogW (sigmaOf tau8 σ) (N ++ M) ∧
      WfMemW rodata [] e' (sigmaOf tau8 σ) (view (N ++ M) mem0c) ∧
      SaveOk8 r (sigmaOf tau8 σ) (view (N ++ M) mem0c) ∧
      Cells8 σ (σ 1) 256 N ∧ OutOk inp (σ 1) 8 N := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel (by omega)
  have hm2 := B.mem e1 σ (view M mem0c) hrel
  have hT := (slice_sound (B.Gf e1) σ m8W (view M mem0c) hm2 prog 4 orcB orcC 24
    (shiftK8 r K211) (KT r) [] C.sliceT rfl
    (assumeOk_of σ (KT r) AT C.KT_assume (asmT σ hge))).1
  have hI := O.invT inp e1 hm
  obtain ⟨e2, he2⟩ : ∃ e2, e2 = envAbs (B.Gf e1) (run prog 4 m8W orcB 24 (shiftK8 r K211)) :=
    ⟨_, rfl⟩
  rw [← he2] at hT hI
  have hL : OutLogW σ ((KT r).mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M) :=
    outLogW_app σ (outLogW_of_logB (KT r) C.KT_logB σ e2) hM
  have hL' : OutLogW (sigmaOf tau8 σ)
      ((KT r).mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)) ++ M) :=
    outLogW_s9 _ (tau8_s9 σ) hL
  refine ⟨e2, (KT r).mem.map (fun p => (mapAddr σ p.1, mapCell e2 σ p.2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_fr, TURNLEN, run_add, hB, hT, turn_step1 C e2 σ, fr_app]
  · exact hL'
  · exact wfW_view rodata env0 e2 (sigmaOf tau8 σ) mem0c _ hL'
      (wfMemW_s9 rodata env0 σ0 (sigmaOf tau8 σ) mem0c hw (by rw [tau8_s9, h9]))
  · exact saveOk8_of_pass1 C e2 σ (sigmaOf tau8 σ) mem0c M (fun j hj => tau8_hi j hj σ)
  · have h := outShape8W_sound (KT r) O.sT e2 σ
    rw [w8_mapState_mem] at h
    exact h
  · have h := outOk_tab8w (KT r) O.cT inp e2 σ hI
    rw [w8_mapState_mem] at h
    exact h

/-- The first pass and the exit (`8 ≤ c < 16`, mirrors `first_exitW`), with its cells and its
8 digests. -/
theorem w8_first_exit {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR8 r B) (e1 : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (inp : Nat → Byte) (hrel : Mem0Rel e1 σ m8W (view M mem0c))
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) (hm : HMem 512 inp e1) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 42) (fr M (mapState e1 σ (shiftK8 r K3))) =
        fr M (mapState e' σ (KTE r)) ∧
      Cells8 σ (σ 1) 256 (mapState e' σ (KTE r)).mem ∧
      OutOk inp (σ 1) 8 (mapState e' σ (KTE r)).mem := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel hge
  have hm2 := B.mem e1 σ (view M mem0c) hrel
  have hX := (slice_sound (B.Gf e1) σ m8W (view M mem0c) hm2 prog 4 orcEx orcC 42
    (shiftK8 r K211) (KTE r) [] C.sliceX rfl
    (assumeOk_of σ (KTE r) AX C.KTE_assume (asmX σ hge hlt))).1
  have hI := O.invX inp e1 hm
  obtain ⟨e2, he2⟩ : ∃ e2, e2 = envAbs (B.Gf e1) (run prog 4 m8W orcEx 42 (shiftK8 r K211)) :=
    ⟨_, rfl⟩
  rw [← he2] at hX hI
  refine ⟨e2, ?_, outShape8W_sound (KTE r) O.sX e2 σ, outOk_tab8w (KTE r) O.cX inp e2 σ hI⟩
  rw [run_fr, run_add, hB]
  exact congrArg (fr M) hX

/-! ## The later passes -/

/-- One framed later pass and its loop tail (`c ≥ 16`, mirrors `iter_stepS`), with the pass's
cells and its 8 digests. -/
theorem w8_iter {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR8 r B)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (e : Key → W32) (σ : Nat → Int)
    (M : CLog) (inp : Nat → Byte)
    (hw : WfMemW rodata [] e σ (view M mem0c)) (hs : SaveOk8 r σ (view M mem0c))
    (hM : OutLogW σ M) (hge : 16 ≤ σ 2)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e' N, run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ (KHs r))) =
        fr (N ++ M) (mapState e' (sigmaOf tau8 σ) (KHs r)) ∧ OutLogW (sigmaOf tau8 σ) (N ++ M) ∧
      WfMemW rodata [] e' (sigmaOf tau8 σ) (view (N ++ M) mem0c) ∧
      SaveOk8 r (sigmaOf tau8 σ) (view (N ++ M) mem0c) ∧
      Cells8 σ (σ 1) 256 N ∧ OutOk inp (σ 1) 8 N := by
  obtain ⟨E, hE⟩ : ∃ E, E = ecomb e σ (view M mem0c) := ⟨_, rfl⟩
  have hrel : Mem0Rel E σ (m8P r) (view M mem0c) := by
    rw [hE]; exact relP C e σ (view M mem0c) hw hs
  have hmE : HMem 512 inp E := by rw [hE]; exact w8_hmem e σ M mem0c inp hM hin
  have hB := B.runS E σ (view M mem0c) orcC hrel (by omega)
  have hm2 := B.memS E σ (view M mem0c) hrel
  have hT := (slice_sound (B.GSf E) σ (m8P r) (view M mem0c) hm2 prog 4 orcB orcC 24
    (stripK8 r K211) (KTs r) [] C.sliceTs rfl (assumeOk_of σ (KTs r) AT C.KTs_assume (asmT σ hge))).1
  have hI := O.invTS inp E hmE
  obtain ⟨e1, he1⟩ : ∃ e1, e1 = envAbs (B.GSf E) (run prog 4 (m8P r) orcB 24 (stripK8 r K211)) :=
    ⟨_, rfl⟩
  rw [← he1] at hT hI
  have hne : ∀ i, e (.n i) = E (.n i) := by intro i; rw [hE]; rfl
  have hrun : run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ (KHs r))) =
      fr M (mapState e1 σ (KTs r)) := by
    rw [run_fr, mapState_nOnly e E σ hne (KHs r) C.KHs_nOnly, TURNLEN, run_add, hB]
    exact congrArg (fr M) hT
  have hL : OutLogW σ ((KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M) :=
    outLogW_app σ (outLogW_of_logB (KTs r) C.KTs_logB σ e1) hM
  have hL' : OutLogW (sigmaOf tau8 σ)
      ((KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)) ++ M) :=
    outLogW_s9 _ (tau8_s9 σ) hL
  refine ⟨e1, (KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell e1 σ p.2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrun, turn_stepS C e1 σ, fr_app]
  · exact hL'
  · rw [view_append]
    exact wfW_view rodata e e1 (sigmaOf tau8 σ) (view M mem0c) _
      (outLogW_s9 _ (tau8_s9 σ) (outLogW_of_logB (KTs r) C.KTs_logB σ e1))
      (wfMemW_s9 rodata e σ (sigmaOf tau8 σ) (view M mem0c) hw (tau8_s9 σ))
  · rw [view_append]
    exact saveOk8_step C e1 σ (sigmaOf tau8 σ) (fun j hj => tau8_hi j hj σ) (view M mem0c) hs
  · have h := outShape8W_sound (KTs r) O.sTS e1 σ
    rw [w8_mapState_mem] at h
    exact h
  · have h := outOk_tab8w (KTs r) O.cTS inp e1 σ hI
    rw [w8_mapState_mem] at h
    exact h

/-- The final later pass and the exit (`8 ≤ c < 16`, mirrors `final_runW`), with its cells and
its 8 digests. -/
theorem w8_final {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR8 r B) (e : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (inp : Nat → Byte)
    (hw : WfMemW rodata [] e σ (view M mem0c)) (hs : SaveOk8 r σ (view M mem0c))
    (hM : OutLogW σ M) (hge : 8 ≤ σ 2) (hlt : σ 2 < 16)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 42) (fr M (mapState e σ (KHs r))) =
        fr M (mapState e' σ (KTEs r)) ∧
      Cells8 σ (σ 1) 256 (mapState e' σ (KTEs r)).mem ∧
      OutOk inp (σ 1) 8 (mapState e' σ (KTEs r)).mem := by
  obtain ⟨E, hE⟩ : ∃ E, E = ecomb e σ (view M mem0c) := ⟨_, rfl⟩
  have hrel : Mem0Rel E σ (m8P r) (view M mem0c) := by
    rw [hE]; exact relP C e σ (view M mem0c) hw hs
  have hmE : HMem 512 inp E := by rw [hE]; exact w8_hmem e σ M mem0c inp hM hin
  have hB := B.runS E σ (view M mem0c) orcC hrel hge
  have hm2 := B.memS E σ (view M mem0c) hrel
  have hX := (slice_sound (B.GSf E) σ (m8P r) (view M mem0c) hm2 prog 4 orcEx orcC 42
    (stripK8 r K211) (KTEs r) [] C.sliceXs rfl
    (assumeOk_of σ (KTEs r) AX C.KTEs_assume (asmX σ hge hlt))).1
  have hI := O.invXS inp E hmE
  obtain ⟨e1, he1⟩ : ∃ e1, e1 = envAbs (B.GSf E) (run prog 4 (m8P r) orcEx 42 (stripK8 r K211)) :=
    ⟨_, rfl⟩
  rw [← he1] at hX hI
  have hne : ∀ i, e (.n i) = E (.n i) := by intro i; rw [hE]; rfl
  refine ⟨e1, ?_, outShape8W_sound (KTEs r) O.sXS e1 σ, outOk_tab8w (KTEs r) O.cXS inp e1 σ hI⟩
  rw [run_fr, mapState_nOnly e E σ hne (KHs r) C.KHs_nOnly, run_add, hB]
  exact congrArg (fr M) hX

/-- `j` framed later passes from the stripped head at `c = 8 j + s`, `8 ≤ s < 16`: the passes'
cells are the output cells `[σ 1, σ 1 + 256 j)` and frame cells, holding blocks `0 .. 8 j - 1`. -/
theorem w8_loop {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR8 r B)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (s : Nat) (hs : 8 ≤ s) (hs16 : s < 16) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog) (inp : Nat → Byte),
      σ 2 = 8 * (j : Int) + (s : Int) → OutLogW σ M →
      WfMemW rodata [] e σ (view M mem0c) → SaveOk8 r σ (view M mem0c) →
      (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
      ∃ e' N, run prog 4 mem0c orcC (j * TURNLEN) (fr M (mapState e σ (KHs r))) =
          fr (N ++ M) (mapState e' (sIt8 j σ) (KHs r)) ∧ OutLogW (sIt8 j σ) (N ++ M) ∧
        WfMemW rodata [] e' (sIt8 j σ) (view (N ++ M) mem0c) ∧
        SaveOk8 r (sIt8 j σ) (view (N ++ M) mem0c) ∧
        Cells8 σ (σ 1) (256 * (j : Int)) N ∧ OutOk inp (σ 1) (8 * j) N := by
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
    have hge : 16 ≤ σ 2 := by
      rw [hσ]
      have hsj : (8 : Int) ≤ (s : Int) := by exact_mod_cast hs
      push_cast
      omega
    obtain ⟨e1, N1, hrun, hM1, hw1, hs1, hsh1, hout1⟩ :=
      w8_iter C B O mem0c orcC e σ M inp hw hsv hM hge hin
    have hσ1 : sigmaOf tau8 σ 2 = 8 * (j : Int) + (s : Int) := by
      rw [tau8_count, hσ]
      push_cast
      omega
    obtain ⟨e2, N2, hrun2, hM2, hw2, hs2, hsh2, hout2⟩ :=
      ih e1 (sigmaOf tau8 σ) (N1 ++ M) (fun o => inp (512 + o)) hσ1 hM1 hw1 hs1
        (w8_hin_tau mem0c σ inp hin)
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
        · rw [tau8_out] at h2 h3
          left; refine ⟨h1, ?_, ?_⟩ <;> push_cast <;> omega
        · rw [tau8_s9] at h2 h3
          right; exact ⟨h1, h2, h3⟩
      · rcases hsh1 p h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · left; refine ⟨h1, ?_, ?_⟩ <;> push_cast <;> omega
        · right; exact ⟨h1, h2, h3⟩
    · rw [show 8 * (j + 1) = 8 + 8 * j by omega]
      refine outOk_glue' inp (σ 1) 8 (8 * j) N2 N1 ?_ hout1 ?_
      · intro p hp hr
        have h := cells8_ne _ _ _ N2 hsh2 p hp hr
        rw [tau8_out] at h; push_cast; omega
      · rw [tau8_out] at hout2
        have : (σ 1 + 256 : Int) = σ 1 + 32 * ((8 : Nat) : Int) := by push_cast; omega
        rw [this] at hout2
        exact hout2

/-! ## Every count, for a residue -/

theorem turnOut8W_r {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR8 r B) (env0 : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (j s : Nat)
    (inp : Nat → Byte)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (hs : 8 ≤ s) (hs16 : s < 16)
    (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int)) (hr : (r : Int) = (σ 9 - 16) % 32)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (∀ p ∈ (run prog 4 mem0c orcC (24 + (TURNLEN + (j * TURNLEN + (BODYLEN + 42))))
        (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - 1296 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (8 * (j + 2))
      (run prog 4 mem0c orcC (24 + (TURNLEN + (j * TURNLEN + (BODYLEN + 42))))
        (fr M (mapState env0 σ entryWin))).mem := by
  have hs8 : (8 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hge : 8 ≤ σ 2 := by rw [hc]; omega
  -- the entry and the first pass
  obtain ⟨e1, hentry, hrel, hm1⟩ := w8_entry C env0 σ mem0c orcC M inp hw hM hge hr hin
  obtain ⟨e2, N1, hturn, hM2, hw2, hs2, hsh1, hout1⟩ :=
    w8_first_turn C B O env0 e1 σ σ mem0c orcC M inp hw rfl hM hrel (by rw [hc]; omega) hm1
  -- the later passes
  have hcount : sigmaOf tau8 σ 2 = 8 * (j : Int) + (s : Int) := by
    rw [tau8_count, hc]
    omega
  obtain ⟨e3, N2, hloop, hM3, hw3, hs3, hsh2, hout2⟩ :=
    w8_loop C B O mem0c orcC s hs hs16 j e2 (sigmaOf tau8 σ) (N1 ++ M) (fun o => inp (512 + o))
      hcount hM2 hw2 hs2 (w8_hin_tau mem0c σ inp hin)
  -- the final pass
  obtain ⟨σ2, hσ2def⟩ : ∃ σ2 : Nat → Int, σ2 = sIt8 j (sigmaOf tau8 σ) := ⟨_, rfl⟩
  rw [← hσ2def] at hloop hM3 hw3 hs3
  have hσ2_2 : σ2 2 = (s : Int) := by rw [hσ2def, sIt8_count, hcount]; omega
  have hin2 : ∀ o : Nat,
      mem0c ⟨rIn, σ2 0 + o⟩ = .dat ((inp (512 * (j + 1) + o)).zeroExtend 32) 0 := by
    intro o
    rw [hσ2def, sIt8_in, tau8_in,
      show σ 0 + 512 + 512 * (j : Int) + (o : Int) = σ 0 + ((512 * (j + 1) + o : Nat) : Int) by
        push_cast; omega]
    exact hin _
  obtain ⟨e4, hfin, hsh3, hout3⟩ :=
    w8_final C B O e3 σ2 mem0c orcC (N2 ++ (N1 ++ M)) (fun o => inp (512 * (j + 1) + o)) hw3 hs3
      hM3 (by rw [hσ2_2]; exact hs8) (by rw [hσ2_2]; exact_mod_cast hs16) hin2
  -- the whole run
  have hall : run prog 4 mem0c orcC (24 + (TURNLEN + (j * TURNLEN + (BODYLEN + 42))))
      (fr M (mapState env0 σ entryWin)) = fr (N2 ++ (N1 ++ M)) (mapState e4 σ2 (KTEs r)) := by
    have sA := run_add prog 4 mem0c orcC 24 (TURNLEN + (j * TURNLEN + (BODYLEN + 42)))
      (fr M (mapState env0 σ entryWin))
    have sB := run_add prog 4 mem0c orcC TURNLEN (j * TURNLEN + (BODYLEN + 42))
      (fr M (mapState e1 σ (shiftK8 r K3)))
    have sC := run_add prog 4 mem0c orcC (j * TURNLEN) (BODYLEN + 42)
      (fr (N1 ++ M) (mapState e2 (sigmaOf tau8 σ) (KHs r)))
    rw [sA, hentry, sB, hturn, sC, hloop]
    exact hfin
  -- symbols of the cuts
  have hσ2_1 : σ2 1 = σ 1 + 256 * ((j + 1 : Nat) : Int) := by
    rw [hσ2def, sIt8_out, tau8_out]
    push_cast
    omega
  have hσ1_1 : sigmaOf tau8 σ 1 = σ 1 + 256 := tau8_out σ
  have hσ2_9 : σ2 9 = σ 9 := by rw [hσ2def, sIt8_s9, tau8_s9]
  have hσ1_9 : sigmaOf tau8 σ 9 = σ 9 := tau8_s9 σ
  rw [hall]
  show (∀ p ∈ (mapState e4 σ2 (KTEs r)).mem ++ (N2 ++ (N1 ++ M)), _) ∧
    OutOk inp (σ 1) (8 * (j + 2)) ((mapState e4 σ2 (KTEs r)).mem ++ (N2 ++ (N1 ++ M)))
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
  · have hlow : OutOk inp (σ 1) (8 * (j + 1)) (N2 ++ (N1 ++ M)) := by
      rw [show 8 * (j + 1) = 8 + 8 * j by omega]
      refine outOk_glue' inp (σ 1) 8 (8 * j) N2 (N1 ++ M) ?_
        (outOk_append_left inp (σ 1) 8 N1 M hout1) ?_
      · intro p hp hr'
        have h := cells8_ne _ _ _ N2 hsh2 p hp hr'
        rw [hσ1_1] at h; push_cast; omega
      · rw [hσ1_1] at hout2
        have : (σ 1 + 256 : Int) = σ 1 + 32 * ((8 : Nat) : Int) := by push_cast; omega
        rw [this] at hout2
        exact hout2
    rw [show 8 * (j + 2) = 8 * (j + 1) + 8 by omega]
    refine outOk_step' inp (σ 1) (8 * (j + 1)) 8 _ (N2 ++ (N1 ++ M)) ?_ hlow ?_
    · intro p hp hr'
      have h := cells8_ne _ _ _ _ hsh3 p hp hr'
      rw [hσ2_1] at h; push_cast at h ⊢; omega
    · rw [hσ2_1] at hout3
      have : (σ 1 + 256 * ((j + 1 : Nat) : Int) : Int) = σ 1 + 32 * ((8 * (j + 1) : Nat) : Int) := by
        push_cast; omega
      rw [this] at hout3
      have h64 : (fun o => inp (512 * (j + 1) + o)) = (fun o => inp (64 * (8 * (j + 1)) + o)) := by
        funext o; exact congrArg inp (by omega)
      rw [h64] at hout3
      exact hout3

theorem turnOut8WLast_r {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR8 r B) (env0 : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (inp : Nat → Byte)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (hge : 8 ≤ σ 2) (hlt : σ 2 < 16)
    (hr : (r : Int) = (σ 9 - 16) % 32)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (∀ p ∈ (run prog 4 mem0c orcC (24 + (BODYLEN + 42)) (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
        (p.1.region = rStack ∧ σ 9 - 1296 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 8
      (run prog 4 mem0c orcC (24 + (BODYLEN + 42)) (fr M (mapState env0 σ entryWin))).mem := by
  obtain ⟨e1, hentry, hrel, hm1⟩ := w8_entry C env0 σ mem0c orcC M inp hw hM hge hr hin
  obtain ⟨e', hfin, hsh, hout⟩ := w8_first_exit C B O e1 σ mem0c orcC M inp hrel hge hlt hm1
  have hall : run prog 4 mem0c orcC (24 + (BODYLEN + 42)) (fr M (mapState env0 σ entryWin)) =
      fr M (mapState e' σ (KTE r)) := by
    have sA := run_add prog 4 mem0c orcC 24 (BODYLEN + 42) (fr M (mapState env0 σ entryWin))
    rw [sA, hentry]
    exact hfin
  rw [hall]
  show (∀ p ∈ (mapState e' σ (KTE r)).mem ++ M, _) ∧
    OutOk inp (σ 1) 8 ((mapState e' σ (KTE r)).mem ++ M)
  refine ⟨?_, outOk_append_left inp (σ 1) 8 _ M hout⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · rcases hsh p h with h1 | h1
    · right; left; exact h1
    · right; right; exact h1
  · left; exact h

/-! ## The statements, with `Avx512X16WOut.OutOk` (R5's text otherwise) -/

def TurnOut8WCore : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (j s : Nat) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86Win.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.WinLogW.OutLogW σ M → 8 ≤ s → s < 16 →
    σ 2 = 8 * ((j : Int) + 1) + (s : Int) → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0c orcC (x8wRunSteps j)
        (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - D8 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (8 * (j + 2))
      (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0c orcC (x8wRunSteps j)
        (fr M (mapState env0 σ entryWin))).mem

def TurnOut8WLastCore : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86Win.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.WinLogW.OutLogW σ M → 8 ≤ σ 2 → σ 2 < 16 → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0c orcC x8wLastSteps
        (fr M (mapState env0 σ entryWin))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
        (p.1.region = rStack ∧ σ 9 - D8 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 8
      (run Hashtree.Kernels.X86Win.Avx2X8.prog 4 mem0c orcC x8wLastSteps
        (fr M (mapState env0 σ entryWin))).mem

theorem D8_int : ((D8 : Nat) : Int) = 1296 := rfl

theorem turnOut8WCore : TurnOut8WCore := by
  intro env0 σ mem0c orcC M j s inp hw hM hs hs16 hc habi hin
  rw [x8wRunSteps_eq, D8_int]
  rcases residue_cases σ habi with h8 | h24
  · exact turnOut8W_r cutsW_8 bodyW_8 outR_8 env0 σ mem0c orcC M j s inp hw hM hs hs16 hc h8 hin
  · exact turnOut8W_r cutsW_24 bodyW_24 outR_24 env0 σ mem0c orcC M j s inp hw hM hs hs16 hc h24 hin

theorem turnOut8WLastCore : TurnOut8WLastCore := by
  intro env0 σ mem0c orcC M inp hw hM hge hlt habi hin
  rw [x8wLastSteps_eq, D8_int]
  rcases residue_cases σ habi with h8 | h24
  · exact turnOut8WLast_r cutsW_8 bodyW_8 outR_8 env0 σ mem0c orcC M inp hw hM hge hlt h8 hin
  · exact turnOut8WLast_r cutsW_24 bodyW_24 outR_24 env0 σ mem0c orcC M inp hw hM hge hlt h24 hin

/-! ## R5's statements -/

/-- **`TurnOut8W`** (R5's statement, `WinWrapper.OutOk`). -/
theorem turnOut8W : TurnOut8W := by
  unfold TurnOut8W Hashtree.Proofs.WinWrapper.OutOk
  have h := turnOut8WCore
  unfold TurnOut8WCore OutOk at h
  exact h

/-- **`TurnOut8WLast`** (R5's statement, `WinWrapper.OutOk`). -/
theorem turnOut8WLast : TurnOut8WLast := by
  unfold TurnOut8WLast Hashtree.Proofs.WinWrapper.OutOk
  have h := turnOut8WLastCore
  unfold TurnOut8WLastCore OutOk at h
  exact h

end Hashtree.Proofs.WinAvx2X8WOut
