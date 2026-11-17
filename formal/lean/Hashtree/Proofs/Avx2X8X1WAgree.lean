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


/-! ## The x4 small path into x1 (`9 ≤ s < 12`) and the single-pass cases -/

open Hashtree.Proofs.Avx2X8X4WAgree (x8_x4_W_small x8_x4_W1_last x8_x4_W1_small sIt8_count8
  sIt8_9 upd15_count8 cutEnv8)
open Hashtree.Proofs.Avx2X8WShift (KTE BODYLEN)
open Hashtree.Proofs.Avx2X8WLoop (tau8_count TURNLEN)
open Hashtree.Proofs.AvxX4Small (KSm orcK)
open Hashtree.Proofs.AvxX1W (resume_KSm correctWAt_entry)

/-- An expression without memory keys. -/
def noMk : E → Bool
  | .var (.n _) => true
  | .var (.m _ _) => false
  | .const _ => true
  | .add a b => noMk a && noMk b
  | .xor a b => noMk a && noMk b
  | .and a b => noMk a && noMk b
  | .or a b => noMk a && noMk b
  | .not a => noMk a
  | .shl a _ => noMk a
  | .shr a _ => noMk a
  | .sar a _ => noMk a
  | .ror a _ => noMk a
  | .tern _ a b c => noMk a && noMk b && noMk c

theorem eval_noMk (e e' : Key → W32) (h : ∀ i, e (.n i) = e' (.n i)) :
    ∀ x : E, noMk x = true → x.eval e = x.eval e'
  | .var (.n i), _ => h i
  | .var (.m _ _), hx => by simp [noMk] at hx
  | .const _, _ => rfl
  | .add a b, hx => by
      simp only [noMk, Bool.and_eq_true] at hx
      simp only [E.eval, eval_noMk e e' h a hx.1, eval_noMk e e' h b hx.2]
  | .xor a b, hx => by
      simp only [noMk, Bool.and_eq_true] at hx
      simp only [E.eval, eval_noMk e e' h a hx.1, eval_noMk e e' h b hx.2]
  | .and a b, hx => by
      simp only [noMk, Bool.and_eq_true] at hx
      simp only [E.eval, eval_noMk e e' h a hx.1, eval_noMk e e' h b hx.2]
  | .or a b, hx => by
      simp only [noMk, Bool.and_eq_true] at hx
      simp only [E.eval, eval_noMk e e' h a hx.1, eval_noMk e e' h b hx.2]
  | .not a, hx => by simp only [noMk] at hx; simp only [E.eval, eval_noMk e e' h a hx]
  | .shl a _, hx => by simp only [noMk] at hx; simp only [E.eval, eval_noMk e e' h a hx]
  | .shr a _, hx => by simp only [noMk] at hx; simp only [E.eval, eval_noMk e e' h a hx]
  | .sar a _, hx => by simp only [noMk] at hx; simp only [E.eval, eval_noMk e e' h a hx]
  | .ror a _, hx => by simp only [noMk] at hx; simp only [E.eval, eval_noMk e e' h a hx]
  | .tern _ a b c, hx => by
      simp only [noMk, Bool.and_eq_true] at hx
      simp only [E.eval, eval_noMk e e' h a hx.1.1, eval_noMk e e' h b hx.1.2,
        eval_noMk e e' h c hx.2]

def valNoMk : Val E Lin → Bool
  | .num lo hi => noMk lo && noMk hi
  | .ptr _ => true

theorem entryW_gpr_noMk : entryW.gpr.all valNoMk = true := by decide +kernel
theorem entryW_vr_noMk : entryW.vr.all (fun l => l.all noMk) = true := by decide +kernel
theorem entryW_mem_nil : entryW.mem = [] := rfl

/-- `mapState` of `entryW` reads its environment only on numbered variables. -/
theorem mapState_entryW_congr (e e' : Key → W32) (σ : Nat → Int)
    (h : ∀ i, e (.n i) = e' (.n i)) : mapState e σ entryW = mapState e' σ entryW := by
  have hg : entryW.gpr.map (mapVal e σ) = entryW.gpr.map (mapVal e' σ) := by
    apply List.map_congr_left
    intro v hv
    have hn := List.all_eq_true.mp entryW_gpr_noMk v hv
    cases v with
    | num lo hi =>
        simp only [valNoMk, Bool.and_eq_true] at hn
        simp only [mapVal, eval_noMk e e' h lo hn.1, eval_noMk e e' h hi hn.2]
    | ptr a => rfl
  have hv : entryW.vr.map (·.map (E.eval e)) = entryW.vr.map (·.map (E.eval e')) := by
    apply List.map_congr_left
    intro l hl
    have hn := List.all_eq_true.mp entryW_vr_noMk l hl
    apply List.map_congr_left
    intro x hx
    exact eval_noMk e e' h x (List.all_eq_true.mp hn x hx)
  unfold mapState
  simp only [hg, hv, entryW_mem_nil, List.map_nil]

theorem resume_fr (L : CLog) (s : CS) : resume (fr L s) = fr L (resume s) := by
  simp only [resume, fr]

/-- The x1 environment at the x4 small-path cut: the cut's numbered variables, the memory keys
read through the given (swapped, viewed) memory. -/
def envSw (e : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int) : Key → W32
  | .n i => e (.n i)
  | .m r off => cellX (m ⟨r, off.eval σ⟩)

/-- The x1 post from the resumed x4 small-path cut `KSm` behind a W-mode log `L`, for any
actual state that agrees with it outside `{rax, rcx}`. -/
theorem x1_ksm_framed (c1 : Nat) (inp : Nat → Byte) (env' : Key → W32) (σ4 : Nat → Int)
    (σ : Nat → Int) (env0 : Key → W32) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (L : CLog) (r1 : Region) (t : CS)
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hL : OutLogW σ4 L) (h9 : σ4 9 = σ 9) (hc1 : σ4 2 = (c1 : Int))
    (hin1 : ∀ o : Nat, mem0c ⟨rIn, σ4 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hag : AgreeOn [0, 1] (fr L (mapState env' σ4 KSm)) t) :
    let env1 : Key → W32 := envSw env' σ4 ((swap 4 r1).mem (view L mem0c))
    let fin : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 (view L mem0c) orcC (steps c1)
      (resume (mapState env' σ4 KSm))
    let g : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps c1) (resume t)
    g.halted = true ∧ g.err = none ∧ g.tail = none ∧ g.mem = fin.mem ++ L ∧
      InRange (σ4 9) (σ4 1) (32 * c1) fin.mem ∧ OutOk inp (σ4 1) c1 fin.mem ∧
      RegsOk env1 σ4 g := by
  intro env1 fin g
  have hw1' : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env1 σ4 (view L mem0c) :=
    wfAt_cut r1 _ env0 env1 σ σ4 h9 mem0c L hL h1Out h1Stack hw1
  have he1 : EnvMem env1 σ4 ((swap 4 r1).mem (view L mem0c)) := fun _ _ => rfl
  have hin : ∀ o : Nat, (swap 4 r1).mem (view L mem0c) ⟨rIn, σ4 0 + o⟩ =
      .dat ((inp o).zeroExtend 32) 0 :=
    fun o => swap_view_in r1 h1In mem0c L σ4 hL _ _ (hin1 o)
  have hP := correctWAt_entry c1 inp env1 σ4 (view L mem0c) orcC r1 h1Num h1In h1Out h1Stack
    h1G h1Ret hw1' he1 hc1 hin (mapState env' σ4 KSm).flags
  dsimp only at hP
  obtain ⟨hhalt, herr, htail, hR, hO, hRegs⟩ := hP
  have href : resume (mapState env' σ4 KSm) =
      {mapState env1 σ4 entryW with flags := (mapState env' σ4 KSm).flags} := by
    rw [resume_KSm, mapState_entryW_congr env' env1 σ4 (fun _ => rfl)]
  have hfin : fin = run Hashtree.Kernels.X86.AvxX1.prog r1 (view L mem0c) orcC (steps c1)
      {mapState env1 σ4 entryW with flags := (mapState env' σ4 KSm).flags} := by
    show run Hashtree.Kernels.X86.AvxX1.prog r1 (view L mem0c) orcC (steps c1)
      (resume (mapState env' σ4 KSm)) = _
    rw [href]
  have hag2 : AgreeOn [0, 1]
      (fr L {mapState env1 σ4 entryW with flags := (mapState env' σ4 KSm).flags})
      (resume t) := by
    have h := agreeOn_resume hag
    rw [resume_fr, href] at h
    exact h
  have hpre : AgreeOn (Dsx (fr L {mapState env1 σ4 entryW with
      flags := (mapState env' σ4 KSm).flags}).pc)
      (fr L {mapState env1 σ4 entryW with flags := (mapState env' σ4 KSm).flags})
      (resume t) :=
    hag2.mono (fun i hi => by
      show i ∈ Dsx 0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> decide)
  have herr1 : (run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps c1)
      (fr L {mapState env1 σ4 entryW with flags := (mapState env' σ4 KSm).flags})).err = none := by
    rw [run_fr]; exact herr
  have hA := run_agree Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC Dsx hsound
    (steps c1) _ _ hpre herr1
  rw [run_fr] at hA
  rw [hfin]
  refine ⟨hA.halted ▸ hhalt, hA.err ▸ herr, hA.tail ▸ htail, hA.mem.symm, hR, hO,
    regsOk_agree hA (fun i hi => not_mem_Dsx i _ hi) hRegs⟩

/-- **x8 -> x4 -> x1, `c = 8 (j + 1) + s` with `9 ≤ s < 12`.**  The x8 run to `KTEs r`, the x4
small path to `KSm` (up to `{rax, rcx}`), and the x1 link (table at `r1`) from the resumed x4
state: halted, no error, no tail, its log = own writes over the renamed x8 log, `InRange` /
`OutOk` of the `s - 8` blocks, `RegsOk` (in the cut's environment over the swapped memory). -/
theorem x8_x4_x1_W_small (j s : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hs : 9 ≤ s) (hs12 : s < 12)
    (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int)) (habi : σ 9 % 16 = 8)
    (hin1 : ∀ o : Nat, mem0c ⟨rIn, sigmaOf tau8 (sIt8 (j + 1) (upd15 σ)) 0 + o⟩ =
      .dat ((inp o).zeroExtend 32) 0) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
          (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31)))) (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r))) ∧
      (let σ' : Nat → Int := sIt8 (j + 1) (upd15 σ)
       let L : CLog := cutLog8 (swap 4 r8) (KTEs r) e' σ' M'
       let σ4 : Nat → Int := sigmaOf tau8 σ'
       let R0 : State E Lin := run Hashtree.Kernels.X86.AvxX4.prog 4
         (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW
       let env' : Key → W32 := envAbs (cutEnv8 (KTEs r) e' σ4 (view L mem0c)) R0
       let env1 : Key → W32 := envSw env' σ4 ((swap 4 r1).mem (view L mem0c))
       let fin : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 (view L mem0c) orcC (steps (s - 8))
         (resume (mapState env' σ4 KSm))
       let g : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (s - 8))
         (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
           (resume ((swap 4 r8).state (fr M' (mapState e' σ' (KTEs r)))))))
       g.halted = true ∧ g.err = none ∧ g.tail = none ∧ g.mem = fin.mem ++ L ∧
         InRange (σ4 9) (σ4 1) (32 * (s - 8)) fin.mem ∧ OutOk inp (σ4 1) (s - 8) fin.mem ∧
         RegsOk env1 σ4 g) := by
  obtain ⟨r, e', M', hr, hrun, hlog, hag⟩ := x8_x4_W_small j s env0 σ mem0c orcC M r8 hrNum hrIn
    hrOut hrStack hrG hrRet hw8 hw4 hM hs hs12 hc habi
  obtain ⟨_, _, f2, f3, _⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  dsimp only at hag
  refine ⟨r, e', M', hr, hrun, ?_⟩
  intro σ' L σ4 R0 env' env1 fin g
  have hL : OutLogW σ4 L := cutLog8_outLogW (swap 4 r8) f2 f3 (KTEs r) e' σ' M' hlog
  have h9 : σ4 9 = σ 9 := by
    show sigmaOf tau8 (sIt8 (j + 1) (upd15 σ)) 9 = σ 9
    rw [tau8_s9, sIt8_9]
  have hc1 : σ4 2 = ((s - 8 : Nat) : Int) := by
    show sigmaOf tau8 (sIt8 (j + 1) (upd15 σ)) 2 = _
    rw [tau8_count, sIt8_count8 j s σ hc]
    omega
  exact x1_ksm_framed (s - 8) inp env' σ4 σ env0 mem0c orcC L r1 _ h1Num h1In h1Out h1Stack
    h1G h1Ret hw1 hL h9 hc1 hin1 hag

/-- **x8 -> x4 -> x1 for `9 ≤ c < 12`.**  One x8 pass to `KTE r`, the x4 small path, x1. -/
theorem x8_x4_x1_W1_small (s : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hs : 1 ≤ s) (hs4 : s < 4) (hc : σ 2 = (s : Int) + 8)
    (habi : σ 9 % 16 = 8)
    (hin1 : ∀ o : Nat, mem0c ⟨rIn, sigmaOf tau8 (upd15 σ) 0 + o⟩ =
      .dat ((inp o).zeroExtend 32) 0) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
          (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r))) ∧
      (let L : CLog := cutLog8 (swap 4 r8) (KTE r) e' (upd15 σ) M'
       let σ4 : Nat → Int := sigmaOf tau8 (upd15 σ)
       let R0 : State E Lin := run Hashtree.Kernels.X86.AvxX4.prog 4
         (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW
       let env' : Key → W32 := envAbs (cutEnv8 (KTE r) e' σ4 (view L mem0c)) R0
       let env1 : Key → W32 := envSw env' σ4 ((swap 4 r1).mem (view L mem0c))
       let fin : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 (view L mem0c) orcC (steps s)
         (resume (mapState env' σ4 KSm))
       let g : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps s)
         (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
           (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r)))))))
       g.halted = true ∧ g.err = none ∧ g.tail = none ∧ g.mem = fin.mem ++ L ∧
         InRange (σ4 9) (σ4 1) (32 * s) fin.mem ∧ OutOk inp (σ4 1) s fin.mem ∧
         RegsOk env1 σ4 g) := by
  obtain ⟨r, e', M', hr, hrun, hlog, hag⟩ := x8_x4_W1_small env0 σ mem0c orcC M r8 hrNum hrIn
    hrOut hrStack hrG hrRet hw8 hw4 hM (by omega) (by omega) habi
  obtain ⟨_, _, f2, f3, _⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  dsimp only at hag
  refine ⟨r, e', M', hr, hrun, ?_⟩
  intro L σ4 R0 env' env1 fin g
  have hL : OutLogW σ4 L := cutLog8_outLogW (swap 4 r8) f2 f3 (KTE r) e' (upd15 σ) M' hlog
  have h9 : σ4 9 = σ 9 := by
    show sigmaOf tau8 (upd15 σ) 9 = σ 9
    rw [tau8_s9, upd15_9]
  have hc1 : σ4 2 = (s : Int) := by
    show sigmaOf tau8 (upd15 σ) 2 = _
    rw [tau8_count, upd15_count8, hc]
    omega
  exact x1_ksm_framed s inp env' σ4 σ env0 mem0c orcC L r1 _ h1Num h1In h1Out h1Stack
    h1G h1Ret hw1 hL h9 hc1 hin1 hag

/-- The x4 cut's symbols after the single x8 pass. -/
def tau41 (σ : Nat → Int) : Nat → Int := sIt 0 (upd15 (sigmaOf tau8 (upd15 σ)))

theorem tau41_9 (σ : Nat → Int) : tau41 σ 9 = σ 9 := by
  simp only [tau41]
  rw [sIt_s9, upd15_9, tau8_s9, upd15_9]

/-- **x8 -> x4 -> x1 for `12 ≤ c < 16`.**  One x8 pass to `KTE r`, the x4 W-mode exit to
`K201W`, and the x1 link for the `s - 4` remaining blocks (`c = s + 8`). -/
theorem x8_x4_x1_W1_last (s : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 r1 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (h1Num : r1 ≠ rNum) (h1In : r1 ≠ rIn) (h1Out : r1 ≠ rOut) (h1Stack : r1 ≠ rStack)
    (h1G : r1 ≠ rG) (h1Ret : r1 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hs : 4 ≤ s) (hs8 : s < 8) (hc : σ 2 = (s : Int) + 8)
    (habi : σ 9 % 16 = 8)
    (hin1 : ∀ o : Nat, mem0c ⟨rIn, tau41 σ 0 + 256 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (hc1 : sigmaOf tau (tau41 σ) 2 = ((s - 4 : Nat) : Int)) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
          (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r))) ∧
      ∃ (e4 : Key → W32) (M4 : CLog),
        let L : CLog := cutLog8 (swap 4 r8) (KTE r) e' (upd15 σ) M'
        let L1 : CLog := cutLog e4 (tau41 σ) (M4 ++ L)
        let σ1 : Nat → Int := sigmaOf tau (tau41 σ)
        let fin : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 (view L1 mem0c) orcC (steps (s - 4))
          (cutBare e4 (tau41 σ))
        let g : CS := run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (s - 4))
          (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
            (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r)))))))
        g.halted = true ∧ g.err = none ∧ g.tail = none ∧ g.mem = fin.mem ++ L1 ∧
          InRange (σ1 9) (σ1 1) (32 * (s - 4)) fin.mem ∧ OutOk inp (σ1 1) (s - 4) fin.mem ∧
          RegsOk (cutEnv (swap 4 r1) e4 σ1 (view L1 mem0c)) σ1 g := by
  obtain ⟨r, e', M', hr, hrun, hlog, h3⟩ := x8_x4_W1_last env0 σ mem0c orcC M r8 hrNum hrIn
    hrOut hrStack hrG hrRet hw8 hw4 hM s hs hs8 hc habi
  obtain ⟨_, _, f2, f3, _⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  dsimp only at h3
  obtain ⟨e4, M4, hag, hlog4⟩ := h3
  refine ⟨r, e', M', hr, hrun, e4, M4, ?_⟩
  intro L L1 σ1 fin g
  have hL : OutLogW (sigmaOf tau8 (upd15 σ)) L :=
    cutLog8_outLogW (swap 4 r8) f2 f3 (KTE r) e' _ M' hlog
  have hLτ : OutLogW (tau41 σ) L :=
    outLogW_congr _ _ (by simp only [tau41]; rw [sIt_s9, upd15_9]) L hL
  have h4log : OutLogW (tau41 σ) ((mapState e4 (tau41 σ) K201W).mem ++ M4) := by
    rw [mapState_mem_eq]; exact hlog4
  have hL1 : OutLogW σ1 L1 := by
    refine outLogW_congr (tau41 σ) σ1 (sigmaOf_s9 _) L1 ?_
    show OutLogW (tau41 σ) ((mapState e4 (tau41 σ) K201W).mem ++ (M4 ++ L))
    rw [← List.append_assoc]
    exact outLogW_app _ h4log hLτ
  have h9 : σ1 9 = σ 9 := by
    show sigmaOf tau (tau41 σ) 9 = σ 9
    rw [sigmaOf_s9, tau41_9]
  have hX := x1cut_framed (s - 4) inp e4 (tau41 σ) mem0c (M4 ++ L) orcC r1 h1Num h1In h1Out
    h1Stack h1G h1Ret
    (wfAt_cut r1 Hashtree.Kernels.X86.AvxX1.rodata env0 _ σ σ1 h9 mem0c _ hL1 h1Out h1Stack hw1)
    (fun _ _ => rfl) hc1
    (fun o => by rw [sigmaOf_tau0]; exact swap_view_in r1 h1In mem0c _ _ hL1 _ _ (hin1 o))
  dsimp only at hX
  obtain ⟨hrunX, hhalt, herr, htail, hR, hO, hRegs⟩ := hX
  have hag' : AgreeOn [0, 1]
      (resume (fr (M4 ++ L) (mapState e4 (tau41 σ) K201W)))
      (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
        (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r))))))) := by
    rw [← fr_fr]; exact agreeOn_resume hag
  have hpre : AgreeOn (Dsx (resume (fr (M4 ++ L) (mapState e4 (tau41 σ) K201W))).pc)
      (resume (fr (M4 ++ L) (mapState e4 (tau41 σ) K201W)))
      (resume (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
        (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r))))))) :=
    hag'.mono (fun i hi => by
      show i ∈ Dsx 0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> decide)
  have herr1 : (run Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC (steps (s - 4))
      (resume (fr (M4 ++ L) (mapState e4 (tau41 σ) K201W)))).err = none :=
    (congrArg State.err hrunX).trans herr
  have hA := run_agree Hashtree.Kernels.X86.AvxX1.prog r1 mem0c orcC Dsx hsound
    (steps (s - 4)) _ _ hpre herr1
  rw [hrunX] at hA
  refine ⟨hA.halted ▸ hhalt, hA.err ▸ herr, hA.tail ▸ htail, hA.mem.symm, hR, hO,
    regsOk_agree hA (fun i hi => not_mem_Dsx i _ hi) hRegs⟩

end Hashtree.Proofs.Avx2X8X1WAgree
