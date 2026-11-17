import Hashtree.Proofs.Avx2X8WOutInvR0
import Hashtree.Proofs.Avx2X8WOutInvR16
import Hashtree.Proofs.Avx2X8WAll

/-!
# R2c — output correctness of the `avx2_x8` W-mode loop (`TurnOut8`, `TurnOut8Last`)

Same route as `AvxX4LoopWOut`: the pilot's invariant chain (`Gen.Avx2X8P`) is lifted to R2's W
cuts at both residues (`Avx2X8WOutInvR{0,16}`: R2's body slices are already checked with the
pilot's trees; only the four tails are re-checked with `T210`, `Avx2X8WOutCut*`), one pass's log
is output cells of its 8 blocks plus the kernel's own stack frame (`outShape8`), the digests come
from the invariant at `L211t` (the pilot's `L211` without the 16 register labels a turn tail overwrites) through one table of the pilot's 256 output cells (`outOk_tab`), and
the passes compose along `Avx2X8WLoop.x8_runW` / `x8_runW_last` (entry, first pass, `j` later
passes, final pass) for a residue `r`; `turnOut8` / `turnOut8Last` select the residue by
`Avx2X8WAll.residue_cases`.  `TurnOut8`, `TurnOut8Last`, `x8RunSteps`, `x8LastSteps` and `D8L`
are R5's text (`WinAvx2X8Bridge`), copied verbatim.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Kernels.X86.Avx2X8
open Hashtree.Gen.Avx2X8P (K2 K210)
open Hashtree.Proofs.AvxX4W (upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW outLogW_app)
open Hashtree.Proofs.AvxX4LoopWExit (outLogW_s9)
open Hashtree.Proofs.Avx2X8Align
open Hashtree.Proofs.Avx2X8WShift
open Hashtree.Proofs.Avx2X8WStrip
open Hashtree.Proofs.Avx2X8WLoop
open Hashtree.Proofs.Avx2X8WAll (cutsW_0 bodyW_0 cutsW_16 bodyW_16 residue_cases)
open Hashtree.Proofs.Avx512X16WOut (OutOk lookup_none outOk_append_left outOk_step' outOk_glue'
  hmem_of_envMem in_eval)

namespace Hashtree.Proofs.Avx2X8WOut

/-! ## The statements (R5's `WinAvx2X8Bridge`, verbatim) -/

/-- The step count of `Avx2X8WAll.x8_runW_abi` for `j` further turns:
`16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31)))`. -/
def x8RunSteps (j : Nat) : Nat := 16 + (6062 + (j * 6062 + (6035 + 31)))

/-- The step count of `Avx2X8WAll.x8_runW_last_abi` (`8 ≤ c < 16`): `16 + (BODYLEN + 31)`. -/
def x8LastSteps : Nat := 16 + (6035 + 31)

/-- The linux avx2_x8 frame below the return marker: `push rbp`, `and rsp,-32`, `sub rsp,928`
(generous bound). -/
def D8L : Nat := 984

/-- **`TurnOut8` (to be proved by R2c):** under the hypotheses of `Avx2X8WAll.x8_runW_abi` and the
input bytes, the final write log of the linux avx2_x8 loop at `c = 8 (j + 1) + s`, `8 ≤ s < 16`,
over the caller log `M`, holds only cells of `M`, output cells of the finished `8 (j + 2)` blocks,
or the kernel's own frame below `σ 9`, and the finished blocks hold their SHA-256 bytes. -/
def TurnOut8 : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (j s : Nat) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.AvxX4LoopWFrame.OutLogW σ M → 8 ≤ s → s < 16 →
    σ 2 = 8 * ((j : Int) + 1) + (s : Int) → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC (x8RunSteps j)
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (8 * (j + 2))
      (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC (x8RunSteps j)
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem

/-- **`TurnOut8Last` (to be proved by R2c):** the same for `x8_runW_last_abi`, `8 ≤ c < 16`
(one pass, 8 blocks). -/
def TurnOut8Last : Prop :=
  ∀ (env0 : Key → W32) (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (M : CLog) (inp : Nat → Spec.Byte),
    WfMemW Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c →
    Hashtree.Proofs.AvxX4LoopWFrame.OutLogW σ M → 8 ≤ σ 2 → σ 2 < 16 → σ 9 % 16 = 8 →
    (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    (∀ p ∈ (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC x8LastSteps
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
        (p.1.region = rStack ∧ σ 9 - D8L ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 8
      (run Hashtree.Kernels.X86.Avx2X8.prog 4 mem0c orcC x8LastSteps
        (fr M (mapState env0 σ Hashtree.Asm.X86SymW.entryW))).mem

theorem x8RunSteps_eq (j : Nat) :
    x8RunSteps j = 16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31))) := by
  unfold x8RunSteps TURNLEN BODYLEN
  omega

theorem x8LastSteps_eq : x8LastSteps = 16 + (BODYLEN + 31) := by
  unfold x8LastSteps BODYLEN
  rfl

theorem D8L_int : ((D8L : Nat) : Int) = 984 := rfl

/-! ## Symbols and input bytes -/

theorem upd15_0 (σ : Nat → Int) : upd15 σ 0 = σ 0 := by simp [upd15]
theorem upd15_1 (σ : Nat → Int) : upd15 σ 1 = σ 1 := by simp [upd15]
theorem upd15_2 (σ : Nat → Int) : upd15 σ 2 = σ 2 := by simp [upd15]
theorem upd15_9' (σ : Nat → Int) : upd15 σ 9 = σ 9 := by simp [upd15]

/-- An `OutLogW` log never writes the input region. -/
theorem view_rIn_W (M : CLog) (m : Addr Int → Cell W32 Int) (σ : Nat → Int) (a : Int)
    (hM : OutLogW σ M) : view M m ⟨rIn, a⟩ = m ⟨rIn, a⟩ := by
  have hn : lookup (⟨rIn, a⟩ : Addr Int) M = .ok none := by
    refine lookup_none _ M ?_
    intro p hp heq
    rcases hM p hp with h | ⟨h, _⟩
    · rw [heq] at h; simp [rIn, rOut] at h
    · rw [heq] at h; simp [rIn, rStack] at h
  simp only [view, hn]

/-- `HMem` for a turn environment, which reads the concrete memory behind a W-mode log. -/
theorem hmem_viewW (e : Key → W32) (σ : Nat → Int) (M : CLog) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (hM : OutLogW σ M)
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    HMem 512 inp (ecomb e σ (view M m)) :=
  hmem_of_envMem _ σ _ inp 512 (envMem_ecomb e σ (view M m))
    (fun o => by rw [view_rIn_W M m σ _ hM]; exact hin o)

/-- `HMem` for the entry environment, from its memory relation on `m8`. -/
theorem hmem_rel (e : Key → W32) (σ : Nat → Int) (M : CLog) (m : Addr Int → Cell W32 Int)
    (inp : Nat → Byte) (hM : OutLogW σ M) (h0 : Mem0Rel e σ m8 (view M m))
    (hin : ∀ o : Nat, m ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    HMem 512 inp e := by
  intro o _
  have hW : m8 ⟨rIn, ⟨(o : Int), [1]⟩⟩ = .dat (.var (.m rIn ⟨(o : Int), [1]⟩)) 0 := by
    rw [m8_eq]; rfl
  have hc := h0 ⟨rIn, ⟨(o : Int), [1]⟩⟩ (by rw [hW]; trivial)
  rw [hW] at hc
  simp only [mapAddr, mapCell, in_eval, E.eval] at hc
  rw [view_rIn_W M m σ _ hM, hin o] at hc
  exact (Cell.dat.inj hc).1.symm

/-- The write log of a mapped cut (stated once, for a variable cut, so that the concrete cuts are
never unfolded). -/
theorem mapState_mem (e : Key → W32) (σ : Nat → Int) (K : State E Lin) :
    (mapState e σ K).mem = K.mem.map (fun p => (mapAddr σ p.1, mapCell e σ p.2)) := rfl

/-- The shape predicate of one pass's cells, relative to a symbol valuation. -/
def Cells (σ : Nat → Int) (lo : Int) (n : Int) (N : CLog) : Prop :=
  ∀ p ∈ N, (p.1.region = rOut ∧ lo ≤ p.1.off ∧ p.1.off < lo + n) ∨
    (p.1.region = rStack ∧ σ 9 - 984 ≤ p.1.off ∧ p.1.off < σ 9)

theorem outLogW_of_cells (σ : Nat → Int) (lo n : Int) (N : CLog) (h : Cells σ lo n N) :
    OutLogW σ N := by
  intro p hp
  rcases h p hp with ⟨h1, _⟩ | ⟨h1, _, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, h3⟩

/-! ## The output facts of a residue -/

/-- The four tails of residue `r` reach `L211` from the lifted pass chains, and their cuts have the
pilot's output cells and a log of the turn's shape. -/
structure OutR (r : Nat) (B : BodyW r) : Prop where
  invT : ∀ (inp : Nat → Byte) (e1 : Key → W32), HMem 512 inp e1 →
    InvC inp (envAbs (B.Gf e1) (run prog 4 m8 orcB 27 (shiftK8 r K210))) L211t
  invX : ∀ (inp : Nat → Byte) (e1 : Key → W32), HMem 512 inp e1 →
    InvC inp (envAbs (B.Gf e1) (run prog 4 m8 orcEx 31 (shiftK8 r K210))) L211t
  invTS : ∀ (inp : Nat → Byte) (e1 : Key → W32), HMem 512 inp e1 →
    InvC inp (envAbs (B.GSf e1) (run prog 4 (m8P r) orcB 27 (stripK8 r K210))) L211t
  invXS : ∀ (inp : Nat → Byte) (e1 : Key → W32), HMem 512 inp e1 →
    InvC inp (envAbs (B.GSf e1) (run prog 4 (m8P r) orcEx 31 (stripK8 r K210))) L211t
  cT : tab8.all (fun t => outCell (KT r) t.1 t.2.1 t.2.2) = true
  cX : tab8.all (fun t => outCell (KTE r) t.1 t.2.1 t.2.2) = true
  cTS : tab8.all (fun t => outCell (KTs r) t.1 t.2.1 t.2.2) = true
  cXS : tab8.all (fun t => outCell (KTEs r) t.1 t.2.1 t.2.2) = true
  sT : outShape8 (KT r) = true
  sX : outShape8 (KTE r) = true
  sTS : outShape8 (KTs r) = true
  sXS : outShape8 (KTEs r) = true

theorem outR_0 : OutR 0 bodyW_0 :=
  { invT := invT0, invX := invX0, invTS := invTS0, invXS := invXS0,
    cT := cellsT_0, cX := cellsX_0, cTS := cellsTS_0, cXS := cellsXS_0,
    sT := shapeT_0, sX := shapeX_0, sTS := shapeTS_0, sXS := shapeXS_0 }

theorem outR_16 : OutR 16 bodyW_16 :=
  { invT := invT16, invX := invX16, invTS := invTS16, invXS := invXS16,
    cT := cellsT_16, cX := cellsX_16, cTS := cellsTS_16, cXS := cellsXS_16,
    sT := shapeT_16, sX := shapeX_16, sTS := shapeTS_16, sXS := shapeXS_16 }

/-! ## One pass, with its output -/

/-- The first pass with the loop tail (mirrors `first_turnW`), its log exposed: the 8 digests of
the blocks at the input pointer in `[σ 1, σ 1 + 256)`. -/
theorem first_out {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR r B) (env0 e1 : Key → W32)
    (σ0 σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (inp : Nat → Byte)
    (hw : WfMemW rodata [] env0 σ0 mem0c) (h9 : σ 9 = σ0 9) (hM : OutLogW σ M)
    (hrel : Mem0Rel e1 σ m8 (view M mem0c)) (hge : 16 ≤ σ 2)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e' N, run prog 4 mem0c orcC TURNLEN (fr M (mapState e1 σ (shiftK8 r K2))) =
        fr (N ++ M) (mapState e' (sigmaOf tau8 σ) (KHs r)) ∧
      WfMemW rodata (pushC r) e' (sigmaOf tau8 σ) (view (N ++ M) mem0c) ∧
      Cells σ (σ 1) 256 N ∧ OutOk inp (σ 1) 8 N := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel (by omega)
  have hm := B.mem e1 σ (view M mem0c) hrel
  have hT := (slice_sound (B.Gf e1) σ m8 (view M mem0c) hm prog 4 orcB orcC 27
    (shiftK8 r K210) (KT r) [] C.sliceT rfl
    (assumeOk_of σ (KT r) AT C.KT_assume (asmT σ hge))).1
  have hmE : HMem 512 inp e1 := hmem_rel e1 σ M mem0c inp hM hrel hin
  refine ⟨envAbs (B.Gf e1) (run prog 4 m8 orcB 27 (shiftK8 r K210)),
    (KT r).mem.map (fun p => (mapAddr σ p.1,
      mapCell (envAbs (B.Gf e1) (run prog 4 m8 orcB 27 (shiftK8 r K210))) σ p.2)), ?_, ?_, ?_, ?_⟩
  · rw [run_fr, TURNLEN, run_add, hB, hT, turn_step1 C _ σ, fr_app]
  · exact wfP_of_pass1 C env0 _ _ σ0 σ (sigmaOf tau8 σ) mem0c M hw (outLogW_s9 M h9.symm hM) h9
      (fun j hj => tau8_hi j hj σ)
  · have h := outShape8_sound (KT r) O.sT (envAbs (B.Gf e1) (run prog 4 m8 orcB 27 (shiftK8 r K210))) σ
    rw [mapState_mem] at h
    exact h
  · have h := outOk_tab (KT r) O.cT inp (envAbs (B.Gf e1) (run prog 4 m8 orcB 27 (shiftK8 r K210))) σ (O.invT inp e1 hmE)
    rw [mapState_mem] at h
    exact h

/-- A later pass with the loop tail (mirrors `iter_stepS`), its log exposed. -/
theorem iter_out {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR r B)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (e : Key → W32) (σ : Nat → Int)
    (M : CLog) (inp : Nat → Byte)
    (hw : WfMemW rodata (pushC r) e σ (view M mem0c)) (hM : OutLogW σ M) (hge : 16 ≤ σ 2)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e' N, run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ (KHs r))) =
        fr (N ++ M) (mapState e' (sigmaOf tau8 σ) (KHs r)) ∧
      WfMemW rodata (pushC r) e' (sigmaOf tau8 σ) (view (N ++ M) mem0c) ∧
      Cells σ (σ 1) 256 N ∧ OutOk inp (σ 1) 8 N := by
  have hwE : WfMemW rodata (pushC r) (ecomb e σ (view M mem0c)) σ (view M mem0c) := by
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨h1, h2, h3, ?_⟩
    intro k c hk h8 hok
    rw [h4 k c hk h8 hok]
    exact (pushC_cell_agree r e (ecomb e σ (view M mem0c)) σ σ (fun _ _ => rfl) k c
      (plookup_mem k (pushC r) c hk)).symm
  have hrel : Mem0Rel (ecomb e σ (view M mem0c)) σ (m8P r) (view M mem0c) := by
    rw [m8P_eq]
    exact mem0RelW_of_wf rodata (pushC r) _ σ (view M mem0c) hwE
      (envMem_ecomb (ecomb e σ (view M mem0c)) σ (view M mem0c))
  have hrun : run prog 4 mem0c orcC TURNLEN (fr M (mapState e σ (KHs r))) =
      fr M (mapState (envAbs (B.GSf (ecomb e σ (view M mem0c)))
        (run prog 4 (m8P r) orcB 27 (stripK8 r K210))) σ (KTs r)) := by
    rw [run_fr, mapState_nOnly e (ecomb e σ (view M mem0c)) σ (fun _ => rfl) (KHs r) C.KHs_nOnly]
    exact congrArg (fr M) (turn_runS C B _ σ (view M mem0c) orcC hrel hge)
  have hmE : HMem 512 inp (ecomb e σ (view M mem0c)) := hmem_viewW e σ M mem0c inp hM hin
  refine ⟨envAbs (B.GSf (ecomb e σ (view M mem0c))) (run prog 4 (m8P r) orcB 27 (stripK8 r K210)),
    (KTs r).mem.map (fun p => (mapAddr σ p.1, mapCell (envAbs (B.GSf (ecomb e σ (view M mem0c)))
      (run prog 4 (m8P r) orcB 27 (stripK8 r K210))) σ p.2)), ?_, ?_, ?_, ?_⟩
  · rw [hrun, turn_stepS C _ σ, fr_app]
  · rw [view_append]
    exact wfP_step C e _ _ σ (sigmaOf tau8 σ) (view M mem0c) (fun j hj => tau8_hi j hj σ) hw
  · have h := outShape8_sound (KTs r) O.sTS (envAbs (B.GSf (ecomb e σ (view M mem0c))) (run prog 4 (m8P r) orcB 27 (stripK8 r K210))) σ
    rw [mapState_mem] at h
    exact h
  · have h := outOk_tab (KTs r) O.cTS inp (envAbs (B.GSf (ecomb e σ (view M mem0c))) (run prog 4 (m8P r) orcB 27 (stripK8 r K210))) σ (O.invTS inp _ hmE)
    rw [mapState_mem] at h
    exact h

/-- The first pass and the exit (mirrors `first_exitW`), `8 ≤ c < 16`. -/
theorem first_exit_out {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR r B) (e1 : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (inp : Nat → Byte) (hrel : Mem0Rel e1 σ m8 (view M mem0c)) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 31) (fr M (mapState e1 σ (shiftK8 r K2))) =
        fr M (mapState e' σ (KTE r)) ∧
      Cells σ (σ 1) 256 (mapState e' σ (KTE r)).mem ∧ OutOk inp (σ 1) 8 (mapState e' σ (KTE r)).mem := by
  have hB := B.run e1 σ (view M mem0c) orcC hrel hge
  have hm := B.mem e1 σ (view M mem0c) hrel
  have hX := (slice_sound (B.Gf e1) σ m8 (view M mem0c) hm prog 4 orcEx orcC 31
    (shiftK8 r K210) (KTE r) [] C.sliceX rfl
    (assumeOk_of σ (KTE r) AX C.KTE_assume (asmX σ hge hlt))).1
  have hmE : HMem 512 inp e1 := hmem_rel e1 σ M mem0c inp hM hrel hin
  refine ⟨envAbs (B.Gf e1) (run prog 4 m8 orcEx 31 (shiftK8 r K210)), ?_,
    outShape8_sound (KTE r) O.sX _ σ, outOk_tab (KTE r) O.cX inp _ σ (O.invX inp e1 hmE)⟩
  rw [run_fr, run_add, hB]
  exact congrArg (fr M) hX

/-- A later pass and the exit (mirrors `final_runW`), behind the accumulated log. -/
theorem final_out {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR r B) (e : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (inp : Nat → Byte)
    (hw : WfMemW rodata (pushC r) e σ (view M mem0c)) (hM : OutLogW σ M)
    (hge : 8 ≤ σ 2) (hlt : σ 2 < 16)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∃ e', run prog 4 mem0c orcC (BODYLEN + 31) (fr M (mapState e σ (KHs r))) =
        fr M (mapState e' σ (KTEs r)) ∧
      Cells σ (σ 1) 256 (mapState e' σ (KTEs r)).mem ∧
      OutOk inp (σ 1) 8 (mapState e' σ (KTEs r)).mem := by
  have hwE : WfMemW rodata (pushC r) (ecomb e σ (view M mem0c)) σ (view M mem0c) := by
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨h1, h2, h3, ?_⟩
    intro k c hk h8 hok
    rw [h4 k c hk h8 hok]
    exact (pushC_cell_agree r e (ecomb e σ (view M mem0c)) σ σ (fun _ _ => rfl) k c
      (plookup_mem k (pushC r) c hk)).symm
  have hrel : Mem0Rel (ecomb e σ (view M mem0c)) σ (m8P r) (view M mem0c) := by
    rw [m8P_eq]
    exact mem0RelW_of_wf rodata (pushC r) _ σ (view M mem0c) hwE
      (envMem_ecomb (ecomb e σ (view M mem0c)) σ (view M mem0c))
  have hB := B.runS (ecomb e σ (view M mem0c)) σ (view M mem0c) orcC hrel hge
  have hm := B.memS (ecomb e σ (view M mem0c)) σ (view M mem0c) hrel
  have hX := (slice_sound (B.GSf (ecomb e σ (view M mem0c))) σ (m8P r) (view M mem0c) hm prog 4
    orcEx orcC 31 (stripK8 r K210) (KTEs r) [] C.sliceXs rfl
    (assumeOk_of σ (KTEs r) AX C.KTEs_assume (asmX σ hge hlt))).1
  have hmE : HMem 512 inp (ecomb e σ (view M mem0c)) := hmem_viewW e σ M mem0c inp hM hin
  refine ⟨envAbs (B.GSf (ecomb e σ (view M mem0c))) (run prog 4 (m8P r) orcEx 31 (stripK8 r K210)),
    ?_, outShape8_sound (KTEs r) O.sXS _ σ, outOk_tab (KTEs r) O.cXS inp _ σ (O.invXS inp _ hmE)⟩
  rw [run_fr, mapState_nOnly e (ecomb e σ (view M mem0c)) σ (fun _ => rfl) (KHs r) C.KHs_nOnly,
    run_add, hB]
  exact congrArg (fr M) hX

/-! ## The later passes -/

theorem hin_tau8 (mem0c : Addr Int → Cell W32 Int) (σ : Nat → Int) (inp : Nat → Byte)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ o : Nat, mem0c ⟨rIn, sigmaOf tau8 σ 0 + o⟩ = .dat ((inp (512 + o)).zeroExtend 32) 0 := by
  intro o
  rw [tau8_in, show σ 0 + 512 + (o : Int) = σ 0 + ((512 + o : Nat) : Int) by push_cast; omega]
  exact hin (512 + o)

theorem loop_out {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR r B)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (s : Nat) (hs : 8 ≤ s) (hs16 : s < 16) :
    ∀ (j : Nat) (e : Key → W32) (σ : Nat → Int) (M : CLog) (inp : Nat → Byte),
      σ 2 = 8 * (j : Int) + (s : Int) → OutLogW σ M →
      WfMemW rodata (pushC r) e σ (view M mem0c) →
      (∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
      ∃ e' N, run prog 4 mem0c orcC (j * TURNLEN) (fr M (mapState e σ (KHs r))) =
          fr (N ++ M) (mapState e' (sIt8 j σ) (KHs r)) ∧
        WfMemW rodata (pushC r) e' (sIt8 j σ) (view (N ++ M) mem0c) ∧
        Cells σ (σ 1) (256 * (j : Int)) N ∧ OutOk inp (σ 1) (8 * j) N := by
  intro j
  induction j with
  | zero =>
    intro e σ M inp hσ hM hw hin
    refine ⟨e, [], rfl, hw, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro n i b hn
      exact absurd hn (Nat.not_lt_zero n)
  | succ j ih =>
    intro e σ M inp hσ hM hw hin
    have hge : 16 ≤ σ 2 := by
      rw [hσ]
      have hsj : (8 : Int) ≤ (s : Int) := by exact_mod_cast hs
      push_cast
      omega
    obtain ⟨e1, N1, hrun, hw1, hsh1, hout1⟩ := iter_out C B O mem0c orcC e σ M inp hw hM hge hin
    have hσ1 : sigmaOf tau8 σ 2 = 8 * (j : Int) + (s : Int) := by
      rw [tau8_count, hσ]
      push_cast
      omega
    have hM1 : OutLogW (sigmaOf tau8 σ) (N1 ++ M) :=
      outLogW_app _ (outLogW_s9 N1 (tau8_s9 σ) (outLogW_of_cells σ _ _ N1 hsh1))
        (outLogW_s9 M (tau8_s9 σ) hM)
    obtain ⟨e2, N2, hrun2, hw2, hsh2, hout2⟩ :=
      ih e1 (sigmaOf tau8 σ) (N1 ++ M) (fun o => inp (512 + o)) hσ1 hM1 hw1
        (hin_tau8 mem0c σ inp hin)
    refine ⟨e2, N2 ++ N1, ?_, ?_, ?_, ?_⟩
    · have hlen : (j + 1) * TURNLEN = TURNLEN + j * TURNLEN := by
        rw [Nat.succ_mul, Nat.add_comm]
      rw [hlen, run_add, hrun, hrun2, List.append_assoc]
      rfl
    · rw [List.append_assoc]
      exact hw2
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
        rcases hsh2 p hp with ⟨_, h2, _⟩ | ⟨h1, _, _⟩
        · rw [tau8_out] at h2; push_cast; omega
        · rw [hr] at h1; simp [rOut, rStack] at h1
      · rw [tau8_out] at hout2
        have : (σ 1 + 256 : Int) = σ 1 + 32 * ((8 : Nat) : Int) := by push_cast; omega
        rw [this] at hout2
        exact hout2

/-! ## Every count, for a residue -/

theorem turnOut8_r {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR r B) (env0 : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (j s : Nat)
    (inp : Nat → Byte)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (hs : 8 ≤ s) (hs16 : s < 16)
    (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int)) (hr : (r : Int) = (σ 9 - 8) % 32)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (∀ p ∈ (run prog 4 mem0c orcC (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31))))
        (fr M (mapState env0 σ entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256 * ((j : Int) + 2)) ∨
        (p.1.region = rStack ∧ σ 9 - 984 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) (8 * (j + 2))
      (run prog 4 mem0c orcC (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31))))
        (fr M (mapState env0 σ entryW))).mem := by
  have h9 : upd15 σ 9 = σ 9 := upd15_9' σ
  have h2 : upd15 σ 2 = σ 2 := upd15_2 σ
  have h0 : upd15 σ 0 = σ 0 := upd15_0 σ
  have h1 : upd15 σ 1 = σ 1 := upd15_1 σ
  have hM15 : OutLogW (upd15 σ) M := outLogW_s9 M h9 hM
  have hs8 : (8 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hge : 8 ≤ σ 2 := by rw [hc]; omega
  have hin15 : ∀ o : Nat, mem0c ⟨rIn, upd15 σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
    intro o; rw [h0]; exact hin o
  obtain ⟨e1, hentry, hrel⟩ := entry_runW C env0 σ mem0c orcC M hw hM hge hr
  obtain ⟨e2, N1, hturn, hw2, hsh1, hout1⟩ := first_out C B O env0 e1 σ (upd15 σ) mem0c orcC M
    inp hw h9 hM15 hrel (by rw [h2, hc]; omega) hin15
  obtain ⟨σ1, hσ1def⟩ : ∃ σ1 : Nat → Int, σ1 = sigmaOf tau8 (upd15 σ) := ⟨_, rfl⟩
  rw [← hσ1def] at hturn hw2
  have hσ1_2 : σ1 2 = 8 * (j : Int) + (s : Int) := by
    rw [hσ1def, tau8_count, h2, hc]
    omega
  have hσ1_0 : σ1 0 = σ 0 + 512 := by rw [hσ1def, tau8_in, h0]
  have hσ1_1 : σ1 1 = σ 1 + 256 := by rw [hσ1def, tau8_out, h1]
  have hσ1_9 : σ1 9 = σ 9 := by rw [hσ1def, tau8_s9, h9]
  have hM1 : OutLogW σ1 (N1 ++ M) :=
    outLogW_s9 _ (by rw [hσ1_9, h9]) (outLogW_app (upd15 σ) (outLogW_of_cells _ _ _ N1 hsh1) hM15)
  have hin1 : ∀ o : Nat, mem0c ⟨rIn, σ1 0 + o⟩ = .dat ((inp (512 + o)).zeroExtend 32) 0 := by
    intro o
    rw [hσ1_0, show σ 0 + 512 + (o : Int) = σ 0 + ((512 + o : Nat) : Int) by push_cast; omega]
    exact hin (512 + o)
  obtain ⟨e3, N2, hloop, hw3, hsh2, hout2⟩ :=
    loop_out C B O mem0c orcC s hs hs16 j e2 σ1 (N1 ++ M) (fun o => inp (512 + o)) hσ1_2 hM1 hw2 hin1
  obtain ⟨σ2, hσ2def⟩ : ∃ σ2 : Nat → Int, σ2 = sIt8 j σ1 := ⟨_, rfl⟩
  rw [← hσ2def] at hloop hw3
  have hσ2_2 : σ2 2 = (s : Int) := by rw [hσ2def, sIt8_count, hσ1_2]; omega
  have hσ2_9 : σ2 9 = σ 9 := by rw [hσ2def, sIt8_s9, hσ1_9]
  have hσ2_1 : σ2 1 = σ 1 + 256 * ((j + 1 : Nat) : Int) := by
    rw [hσ2def, sIt8_out, hσ1_1]
    push_cast
    omega
  have hM2 : OutLogW σ2 (N2 ++ (N1 ++ M)) :=
    outLogW_s9 _ (by rw [hσ2_9, hσ1_9]) (outLogW_app σ1 (outLogW_of_cells _ _ _ N2 hsh2) hM1)
  have hin2 : ∀ o : Nat,
      mem0c ⟨rIn, σ2 0 + o⟩ = .dat ((inp (512 * (j + 1) + o)).zeroExtend 32) 0 := by
    intro o
    rw [hσ2def, sIt8_in, hσ1_0,
      show σ 0 + 512 + 512 * (j : Int) + (o : Int) = σ 0 + ((512 * (j + 1) + o : Nat) : Int) by
        push_cast; omega]
    exact hin _
  obtain ⟨e4, hfin, hsh3, hout3⟩ :=
    final_out C B O e3 σ2 mem0c orcC (N2 ++ (N1 ++ M)) (fun o => inp (512 * (j + 1) + o)) hw3 hM2
      (by rw [hσ2_2]; exact hs8) (by rw [hσ2_2]; exact_mod_cast hs16) hin2
  have hall : run prog 4 mem0c orcC (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31))))
      (fr M (mapState env0 σ entryW)) = fr (N2 ++ (N1 ++ M)) (mapState e4 σ2 (KTEs r)) := by
    have sA := run_add prog 4 mem0c orcC 16 (TURNLEN + (j * TURNLEN + (BODYLEN + 31)))
      (fr M (mapState env0 σ entryW))
    have sB := run_add prog 4 mem0c orcC TURNLEN (j * TURNLEN + (BODYLEN + 31))
      (run prog 4 mem0c orcC 16 (fr M (mapState env0 σ entryW)))
    rw [sA, sB, hentry, hturn]
    have sC := run_add prog 4 mem0c orcC (j * TURNLEN) (BODYLEN + 31)
      (fr (N1 ++ M) (mapState e2 σ1 (KHs r)))
    rw [sC, hloop]
    exact hfin
  rw [hall]
  show (∀ p ∈ (mapState e4 σ2 (KTEs r)).mem ++ (N2 ++ (N1 ++ M)), _) ∧
    OutOk inp (σ 1) (8 * (j + 2)) ((mapState e4 σ2 (KTEs r)).mem ++ (N2 ++ (N1 ++ M)))
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · rcases hsh3 p h with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
      · rw [hσ2_1] at h2' h3'
        right; left; refine ⟨h1', ?_, ?_⟩ <;> push_cast at h2' h3' ⊢ <;> omega
      · rw [hσ2_9] at h2' h3'
        right; right; exact ⟨h1', h2', h3'⟩
    · rcases List.mem_append.mp h with h | h
      · rcases hsh2 p h with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
        · rw [hσ1_1] at h2' h3'
          right; left; refine ⟨h1', ?_, ?_⟩ <;> push_cast at h3' ⊢ <;> omega
        · rw [hσ1_9] at h2' h3'
          right; right; exact ⟨h1', h2', h3'⟩
      · rcases List.mem_append.mp h with h | h
        · rcases hsh1 p h with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
          · rw [h1] at h2' h3'
            right; left; refine ⟨h1', ?_, ?_⟩ <;> push_cast <;> omega
          · rw [h9] at h2' h3'
            right; right; exact ⟨h1', h2', h3'⟩
        · left; exact h
  · have hout1' : OutOk inp (σ 1) 8 N1 := by rw [h1] at hout1; exact hout1
    have hlow : OutOk inp (σ 1) (8 * (j + 1)) (N2 ++ (N1 ++ M)) := by
      rw [show 8 * (j + 1) = 8 + 8 * j by omega]
      refine outOk_glue' inp (σ 1) 8 (8 * j) N2 (N1 ++ M) ?_
        (outOk_append_left inp (σ 1) 8 N1 M hout1') ?_
      · intro p hp hr'
        rcases hsh2 p hp with ⟨_, h2', _⟩ | ⟨h1', _, _⟩
        · rw [hσ1_1] at h2'; push_cast; omega
        · rw [hr'] at h1'; simp [rOut, rStack] at h1'
      · rw [hσ1_1] at hout2
        have : (σ 1 + 256 : Int) = σ 1 + 32 * ((8 : Nat) : Int) := by push_cast; omega
        rw [this] at hout2
        exact hout2
    rw [show 8 * (j + 2) = 8 * (j + 1) + 8 by omega]
    refine outOk_step' inp (σ 1) (8 * (j + 1)) 8 _ (N2 ++ (N1 ++ M)) ?_ hlow ?_
    · intro p hp hr'
      rcases hsh3 p hp with ⟨_, h2', _⟩ | ⟨h1', _, _⟩
      · rw [hσ2_1] at h2'; push_cast at h2' ⊢; omega
      · rw [hr'] at h1'; simp [rOut, rStack] at h1'
    · rw [hσ2_1] at hout3
      have : (σ 1 + 256 * ((j + 1 : Nat) : Int) : Int) = σ 1 + 32 * ((8 * (j + 1) : Nat) : Int) := by
        push_cast; omega
      rw [this] at hout3
      have h64 : (fun o => inp (512 * (j + 1) + o)) = (fun o => inp (64 * (8 * (j + 1)) + o)) := by
        funext o; exact congrArg inp (by omega)
      rw [h64] at hout3
      exact hout3

theorem turnOut8Last_r {r : Nat} (C : CutsW r) (B : BodyW r) (O : OutR r B) (env0 : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog)
    (inp : Nat → Byte)
    (hw : WfMemW rodata [] env0 σ mem0c) (hM : OutLogW σ M) (hge : 8 ≤ σ 2) (hlt : σ 2 < 16)
    (hr : (r : Int) = (σ 9 - 8) % 32)
    (hin : ∀ o : Nat, mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (∀ p ∈ (run prog 4 mem0c orcC (16 + (BODYLEN + 31)) (fr M (mapState env0 σ entryW))).mem,
      p ∈ M ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 256) ∨
        (p.1.region = rStack ∧ σ 9 - 984 ≤ p.1.off ∧ p.1.off < σ 9)) ∧
    OutOk inp (σ 1) 8
      (run prog 4 mem0c orcC (16 + (BODYLEN + 31)) (fr M (mapState env0 σ entryW))).mem := by
  have h9 : upd15 σ 9 = σ 9 := upd15_9' σ
  have h2 : upd15 σ 2 = σ 2 := upd15_2 σ
  have h0 : upd15 σ 0 = σ 0 := upd15_0 σ
  have h1 : upd15 σ 1 = σ 1 := upd15_1 σ
  have hM15 : OutLogW (upd15 σ) M := outLogW_s9 M h9 hM
  have hin15 : ∀ o : Nat, mem0c ⟨rIn, upd15 σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
    intro o; rw [h0]; exact hin o
  obtain ⟨e1, hentry, hrel⟩ := entry_runW C env0 σ mem0c orcC M hw hM hge hr
  obtain ⟨e', hfin, hsh, hout⟩ := first_exit_out C B O e1 (upd15 σ) mem0c orcC M inp hrel hM15
    (by rw [h2]; exact hge) (by rw [h2]; exact hlt) hin15
  have hall : run prog 4 mem0c orcC (16 + (BODYLEN + 31)) (fr M (mapState env0 σ entryW)) =
      fr M (mapState e' (upd15 σ) (KTE r)) := by
    rw [run_add prog 4 mem0c orcC 16 (BODYLEN + 31), hentry]
    exact hfin
  rw [hall]
  show (∀ p ∈ (mapState e' (upd15 σ) (KTE r)).mem ++ M, _) ∧
    OutOk inp (σ 1) 8 ((mapState e' (upd15 σ) (KTE r)).mem ++ M)
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · rcases hsh p h with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
      · rw [h1] at h2' h3'
        right; left; exact ⟨h1', h2', h3'⟩
      · rw [h9] at h2' h3'
        right; right; exact ⟨h1', h2', h3'⟩
    · left; exact h
  · rw [h1] at hout
    exact outOk_append_left inp (σ 1) 8 _ M hout

/-! ## The theorems -/

/-- **`TurnOut8`.** -/
theorem turnOut8 : TurnOut8 := by
  intro env0 σ mem0c orcC M j s inp hw hM hs hs16 hc habi hin
  rw [x8RunSteps_eq, D8L_int]
  rcases residue_cases σ habi with h0 | h16
  · exact turnOut8_r cutsW_0 bodyW_0 outR_0 env0 σ mem0c orcC M j s inp hw hM hs hs16 hc h0 hin
  · exact turnOut8_r cutsW_16 bodyW_16 outR_16 env0 σ mem0c orcC M j s inp hw hM hs hs16 hc h16 hin

/-- **`TurnOut8Last`.** -/
theorem turnOut8Last : TurnOut8Last := by
  intro env0 σ mem0c orcC M inp hw hM hge hlt habi hin
  rw [x8LastSteps_eq, D8L_int]
  rcases residue_cases σ habi with h0 | h16
  · exact turnOut8Last_r cutsW_0 bodyW_0 outR_0 env0 σ mem0c orcC M inp hw hM hge hlt h0 hin
  · exact turnOut8Last_r cutsW_16 bodyW_16 outR_16 env0 σ mem0c orcC M inp hw hM hge hlt h16 hin

end Hashtree.Proofs.Avx2X8WOut
