import Hashtree.Proofs.Avx2X8X4WAgree

/-!
# avx2_x8 -> avx_x4 -> avx_x1 at the W-mode exit cuts

`x8_x4_x1_W_last`: for `c = 8 (j + 1) + s`, `12 ≤ s < 16`, the x8 run (table at `r8`) reaches
its exit cut, the x4 link (table at region 4) entered at the resumed cut reaches its exit cut
`K201W` up to `{rax, rcx}` (`Avx2X8X4WAgree.x8_x4_W_last`), and the x1 link (table at `r1`)
entered at the resumed x4 state returns: its run is, outside `Dsx`, the run from the exact
framed cut that `AvxX4X1WAgree.x1cut_framed` speaks about, so it halts without error with the
x1 all-count post on its own log (`InRange`, `OutOk` of the `s - 12` remaining blocks, the
callee-saved registers).  The x1 run's log is its own writes over the x4 cut log, the x4 log and
the (renamed) x8 log.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.X86Chain (CS resume)
open Hashtree.Proofs.AvxX4W (upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW outLogW_app sIt_s9)
open Hashtree.Proofs.AvxX4LoopFrame (sIt)
open Hashtree.Proofs.AvxX4LoopTurn (tau)
open Hashtree.Proofs.AvxX4LoopWExit (K201W upd15_9)
open Hashtree.Proofs.AvxX4Exit (sigmaOf_tau0)
open Hashtree.Proofs.AvxX4X1WAgree (cutLog cutBare cutEnv wfAt_cut swap_view_in outLogW_congr
  sigmaOf_s9 x1cut_framed)
open Hashtree.Proofs.AvxX1W (steps InRange)
open Hashtree.Proofs.ShaniW (OutOk RegsOk fr_fr)
open Hashtree.Proofs.AvxX1Agree (Dsx hsound not_mem_Dsx regsOk_agree)
open Hashtree.Proofs.Avx2X8WShift (tau8)
open Hashtree.Proofs.Avx2X8WStrip (KTEs)
open Hashtree.Proofs.Avx2X8WLoop (sIt8 tau8_s9 sIt8_s9)
open Hashtree.Proofs.Avx2X8X4WAgree (x8_x4_W_last cutLog8 cutLog8_outLogW x4LastSteps mapState_mem_eq)
open Hashtree.Proofs.Avx2X8WAt (swap_fix)
open Hashtree.Spec

namespace Hashtree.Proofs.Avx2X8X1WAgree

theorem agreeOn_resume {S : List Nat} {s1 s2 : CS} (h : AgreeOn S s1 s2) :
    AgreeOn S (resume s1) (resume s2) where
  pc := rfl
  halted := rfl
  tail := rfl
  err := h.err
  mem := h.mem
  vr := h.vr
  assume := h.assume
  flags := h.flags
  glen := h.glen
  gpr := h.gpr
  gpr16 := h.gpr16

/-- The x4 cut's symbols after the x8 loop at `c = 8 (j + 1) + s`. -/
def tau48 (j : Nat) (σ : Nat → Int) : Nat → Int := sIt 0 (upd15 (sigmaOf tau8 (sIt8 (j + 1) (upd15 σ))))

theorem tau48_9 (j : Nat) (σ : Nat → Int) : tau48 j σ 9 = σ 9 := by
  simp only [tau48]
  rw [sIt_s9, upd15_9, tau8_s9, sIt8_s9, upd15_9]

/-- **x8 -> x4 -> x1, `c = 8 (j + 1) + s` with `12 ≤ s < 16`.** -/
theorem x8_x4_x1_W_last (j s : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hs : 12 ≤ s) (hs16 : s < 16)
    (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int)) (habi : σ 9 % 16 = 8)
    (hin1 : ∀ o : Nat, mem0c ⟨rIn, tau48 j σ 0 + 256 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hc1 : sigmaOf tau (tau48 j σ) 2 = ((s - 12 : Nat) : Int)) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
          (16 + (Hashtree.Proofs.Avx2X8WLoop.TURNLEN + (j * Hashtree.Proofs.Avx2X8WLoop.TURNLEN +
            (Hashtree.Proofs.Avx2X8WShift.BODYLEN + 31)))) (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r))) ∧
      ∃ (e4 : Key → W32) (M4 : CLog),
        let L : CLog := cutLog8 (swap 4 r8) (KTEs r) e' (sIt8 (j + 1) (upd15 σ)) M'
        let L1 : CLog := cutLog e4 (tau48 j σ) (M4 ++ L)
        let σ1 : Nat → Int := sigmaOf tau (tau48 j σ)
        let fin : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 (view L1 mem0c) orcC (steps (s - 12))
          (cutBare e4 (tau48 j σ))
        let g : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (s - 12))
          (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
            (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r)))))))
        g.halted = true ∧ g.err = none ∧ g.tail = none ∧ g.mem = fin.mem ++ L1 ∧
          InRange (σ1 9) (σ1 1) (32 * (s - 12)) fin.mem ∧ OutOk inp (σ1 1) (s - 12) fin.mem ∧
          RegsOk (cutEnv (swap 4 r1) e4 σ1 (view L1 mem0c)) σ1 g := by
  obtain ⟨r, e', M', hr, hrun, hlog, h3⟩ := x8_x4_W_last j s env0 σ mem0c orcC M r8 hrNum hrIn
    hrOut hrStack hrG hrRet hw8 hw4 hM hs hs16 hc habi
  obtain ⟨_, _, f2, f3, _⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  dsimp only at h3
  obtain ⟨e4, M4, hag, hlog4⟩ := h3
  refine ⟨r, e', M', hr, hrun, e4, M4, ?_⟩
  intro L L1 σ1 fin g
  -- the logs
  have hL : OutLogW (sigmaOf tau8 (sIt8 (j + 1) (upd15 σ))) L :=
    cutLog8_outLogW (swap 4 r8) f2 f3 (KTEs r) e' _ M' hlog
  have hLτ : OutLogW (tau48 j σ) L :=
    outLogW_congr _ _ (by simp only [tau48]; rw [sIt_s9, upd15_9]) L hL
  have h4log : OutLogW (tau48 j σ) ((mapState e4 (tau48 j σ) K201W).mem ++ M4) := by
    rw [mapState_mem_eq]; exact hlog4
  have hL1 : OutLogW σ1 L1 := by
    refine outLogW_congr (tau48 j σ) σ1 (sigmaOf_s9 _) L1 ?_
    show OutLogW (tau48 j σ) ((mapState e4 (tau48 j σ) K201W).mem ++ (M4 ++ L))
    rw [← List.append_assoc]
    exact outLogW_app _ h4log hLτ
  have h9 : σ1 9 = σ 9 := by
    show sigmaOf tau (tau48 j σ) 9 = σ 9
    rw [sigmaOf_s9, tau48_9]
  -- the x1 post at the exact framed cut
  have hX := x1cut_framed (s - 12) inp e4 (tau48 j σ) mem0c (M4 ++ L) orcC r1 h1Num h1In h1Out
    h1Stack h1G h1Ret
    (wfAt_cut r1 Hashtree.Kernels.X86.AvxX1.rodata env0 _ σ σ1 h9 mem0c _ hL1 h1Out h1Stack hw1)
    (fun _ _ => rfl) hc1
    (fun o => by rw [sigmaOf_tau0]; exact swap_view_in r1 h1In mem0c _ _ hL1 _ _ (hin1 o))
  dsimp only at hX
  obtain ⟨hrunX, hhalt, herr, htail, hR, hO, hRegs⟩ := hX
  -- the actual x1 run agrees with it outside `Dsx`
  have hag' : AgreeOn [0, 1]
      (resume (fr (M4 ++ L) (mapState e4 (tau48 j σ) K201W)))
      (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
        (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r))))))) := by
    rw [← fr_fr]; exact agreeOn_resume hag
  have hpre : AgreeOn (Dsx (resume (fr (M4 ++ L) (mapState e4 (tau48 j σ) K201W))).pc)
      (resume (fr (M4 ++ L) (mapState e4 (tau48 j σ) K201W)))
      (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
        (resume ((swap 4 r8).state (fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r))))))) :=
    hag'.mono (fun i hi => by
      show i ∈ Dsx 0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> decide)
  have herr1 : (run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (s - 12))
      (resume (fr (M4 ++ L) (mapState e4 (tau48 j σ) K201W)))).err = none :=
    (congrArg State.err hrunX).trans herr
  have hA := run_agree Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC Dsx hsound
    (steps (s - 12)) _ _ hpre herr1
  rw [hrunX] at hA
  refine ⟨hA.halted ▸ hhalt, hA.err ▸ herr, hA.tail ▸ htail, hA.mem.symm, hR, hO,
    regsOk_agree hA (fun i hi => not_mem_Dsx i _ hi) hRegs⟩

end Hashtree.Proofs.Avx2X8X1WAgree
