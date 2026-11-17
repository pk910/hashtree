import Hashtree.Proofs.Avx2X8WAt
import Hashtree.Proofs.Avx2X8ExitShape
import Hashtree.Proofs.AvxX4Agree
import Hashtree.Proofs.AvxX4X1WAgree
import Hashtree.Proofs.AvxX4Entry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.X86Chain (CS resume)
open Hashtree.Proofs.AvxX4W (upd15)
open Hashtree.Proofs.AvxX4LoopWFrame (OutLogW sAt_eval)
open Hashtree.Proofs.AvxX4LoopFrame (sIt)
open Hashtree.Proofs.AvxX4LoopWExit (K201W K201W_err upd15_9)
open Hashtree.Proofs.AvxX4LoopWAll (x4_runW_last)
open Hashtree.Proofs.AvxX4Small (small_prefix zero_run KSm KSm_err KSm_pc orcK)
open Hashtree.Proofs.AvxX4Agree (run_agree4 Dsx4 Dsx4_exit mem_Dsx4)
open Hashtree.Proofs.AvxX4X1WAgree (agreeOn_fr wfAt_cut E201L entryW_gpr_list E201L_len
  getD_default getD_map_lt getD_flat map_range_congr getD_range getD_map_eq entryW_vr_shape
  outLogW_congr)
open Hashtree.Proofs.Avx2X8WShift (KTE BODYLEN exitGpr tau8 KTE_gpr_0 KTE_gpr_16 KTE_err_0 KTE_err_16)
open Hashtree.Proofs.Avx2X8WStrip (KTEs stripFacts stripOk_0 stripOk_16)
open Hashtree.Proofs.Avx2X8WLoop (sIt8 TURNLEN tau8_s9 tau8_count tau8_in tau8_out tau8_hi
  sIt8_s9 sIt8_count)
open Hashtree.Proofs.Avx2X8ExitShape
open Hashtree.Proofs.Avx2X8WAt

/-!
# The x8 -> x4 chain edge at the W-mode exit cut, behind a write log

`Avx2X8WAt` ends the x8 run (table at `r8`) at the exit cut `KTE r` / `KTEs r`: the tail call
into `hashtree_sha256_avx_x4` with the frame popped and the entry registers restored
(`Avx2X8WShift.exitGpr`), with three scratch values of the wrapper call state left over:
`rax` (the wrapper's own output pointer, which the loop-shifted x4 entry state does not name),
`rcx` (on the x8 table) and the flags.  `AvxX4Agree.run_agree4` tolerates exactly those at the
x4 entry.  This module states the x4 link at the resumed x8 cut and proves that it runs as the
x4 W-mode contract (`x4_runW_last`, `small_prefix`, `zero_run`) says, up to `{rax, rcx}` (and
the flags on the count-0 return).

* `cutEnv8` is the cut's environment: numbered variables from `100` on are the cut's own
  vector lanes, the ones below the caller's, and the memory keys read the log-framed memory.
* `x4cut_agree` is the `AgreeOn [0, 1, 16]` agreement of the resumed, renamed cut (its log
  split off) with the x4 entry state `entryW` at the loop-shifted sigma `sigmaOf tau8 σ'`.
* `link_last`, `link_small` and `link_zero` are the three x4 behaviours at the residual count
  `c - 8`; `x8_x4_W_*` compose them with the x8 runs.
-/

namespace Hashtree.Proofs.Avx2X8X4WAgree

/-! ## The exit cuts' registers -/

/-- The x8 exit cut's general registers (`Avx2X8WShift.exitGpr`), listed. -/
def X8L : List (Val E Lin) :=
  [.ptr ⟨rOut, Lin.sym 15⟩, .ptr ⟨4, ⟨2048, []⟩⟩, .ptr ⟨rNum, ⟨-8, [0, 0, 1]⟩⟩,
   .ptr ⟨rStack, Lin.sym 5⟩, .ptr ⟨rStack, sAt 0⟩, .ptr ⟨rStack, Lin.sym 6⟩,
   .ptr ⟨rIn, ⟨512, [1]⟩⟩, .ptr ⟨rOut, ⟨256, [0, 1]⟩⟩,
   .num (.var (.n 16)) (.var (.n 17)), .num (.var (.n 18)) (.var (.n 19)),
   .num (.var (.n 20)) (.var (.n 21)), .num (.var (.n 22)) (.var (.n 23)),
   .ptr ⟨rStack, Lin.sym 7⟩, .ptr ⟨rNum, Lin.sym 11⟩, .ptr ⟨rG, Lin.sym 8⟩,
   .ptr ⟨rNum, Lin.sym 12⟩]

theorem exitGpr_list : exitGpr = X8L := by decide +kernel
theorem X8L_len : X8L.length = 16 := rfl

/-- What the hand-off needs of an exit cut: the registers, no error, 32 vector registers of
16 lanes. -/
structure ExitCut (K : State E Lin) : Prop where
  gpr : K.gpr = exitGpr
  err : K.err = none
  shape : vrShape K = true

theorem exitCut_KTE (r : Nat) (hr : r = 0 ∨ r = 16) : ExitCut (KTE r) := by
  rcases hr with rfl | rfl
  · exact ⟨KTE_gpr_0, KTE_err_0, KTE_shape_0⟩
  · exact ⟨KTE_gpr_16, KTE_err_16, KTE_shape_16⟩

theorem exitCut_KTEs (r : Nat) (hr : r = 0 ∨ r = 16) : ExitCut (KTEs r) := by
  rcases hr with rfl | rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, _, _, _, h17, _, _, _⟩ :=
      stripFacts 0 stripOk_0
    exact ⟨h17, h12, KTEs_shape_0⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, _, _, _, h17, _, _, _⟩ :=
      stripFacts 16 stripOk_16
    exact ⟨h17, h12, KTEs_shape_16⟩

/-! ## The framed cut and the reference x4 entry state -/

/-- The x8 exit cut at the x4 entry, with its write log split off. -/
def cutBare8 (K : State E Lin) (e' : Key → W32) (σ' : Nat → Int) : CS :=
  { resume (mapState e' σ' K) with mem := [] }

/-- The cut's vector lanes in one list, evaluated in the cut's own environment. -/
def cutFlat8 (K : State E Lin) (e : Key → W32) : List W32 :=
  (K.vr.map (·.map (E.eval e))).flatten

/-- The cut's environment: numbered variables from `100` on are the cut's own vector lanes,
the ones below the caller's; memory keys read the given (log-framed) memory. -/
def cutEnv8 (K : State E Lin) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) : Key → W32
  | .n i => if 100 ≤ i then (cutFlat8 K e).getD (i - 100) 0 else e (.n i)
  | .m r off => cellX (m ⟨r, off.eval σ⟩)

theorem cutEnv8_mem (K : State E Lin) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) : EnvMem (cutEnv8 K e σ m) σ m := fun _ _ => rfl

theorem cutEnv8_n_hi (K : State E Lin) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (i : Nat) (h : 100 ≤ i) :
    cutEnv8 K e σ m (.n i) = (cutFlat8 K e).getD (i - 100) 0 := by
  simp only [cutEnv8, if_pos h]

theorem cutEnv8_n_lo (K : State E Lin) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (i : Nat) (h : ¬ 100 ≤ i) :
    cutEnv8 K e σ m (.n i) = e (.n i) := by
  simp only [cutEnv8, if_neg h]

/-- The x4 entry state the framed cut is compared against: `entryW` at the loop-shifted sigma,
with the cut's environment. -/
def refCut8 (K : State E Lin) (e' : Key → W32) (σ' : Nat → Int)
    (m : Addr Int → Cell W32 Int) : CS :=
  mapState (cutEnv8 K e' (sigmaOf tau8 σ') m) (sigmaOf tau8 σ') entryW

/-! ## The vector lanes -/

theorem K_vr_eq_range {K : State E Lin} (hK : ExitCut K) :
    K.vr = (List.range 32).map (fun i => K.vr.getD i []) := by
  have h := getD_range K.vr ([] : List E)
  rw [vrShape_len hK.shape] at h
  exact h.symm

theorem cutFlat8_lane {K : State E Lin} (hK : ExitCut K) (e : Key → W32) :
    ∀ l ∈ K.vr.map (·.map (E.eval e)), l.length = 16 := by
  intro l hl
  obtain ⟨l0, h0, rfl⟩ := List.mem_map.mp hl
  rw [List.length_map]
  exact vrShape_lanes hK.shape l0 h0

/-- One vector lane of the x4 entry state, rebuilt from the cut's own lanes. -/
theorem cut_vr_lane8 {K : State E Lin} (hK : ExitCut K) (e : Key → W32) (σ : Nat → Int)
    (m : Addr Int → Cell W32 Int) (i : Nat) (hi : i < 32) :
    (List.range 16).map (fun l => cutEnv8 K e σ m (.n (vId i l))) =
      (K.vr.getD i []).map (E.eval e) := by
  have h1 : ∀ l, cutEnv8 K e σ m (.n (vId i l)) = (cutFlat8 K e).getD (16 * i + l) 0 := by
    intro l
    rw [cutEnv8_n_hi K e σ m _ (by unfold vId; omega)]
    congr 1
    unfold vId
    omega
  rw [show (fun l => cutEnv8 K e σ m (.n (vId i l))) =
      (fun l => (cutFlat8 K e).getD (16 * i + l) 0) from funext h1]
  have hlen : i < (K.vr.map (·.map (E.eval e))).length := by
    rw [List.length_map, vrShape_len hK.shape]; exact hi
  rw [show cutFlat8 K e = (K.vr.map (·.map (E.eval e))).flatten from rfl]
  rw [getD_flat (K.vr.map (·.map (E.eval e))) 0 i hlen (cutFlat8_lane hK e)]
  exact getD_map_eq (·.map (E.eval e)) K.vr i [] [] rfl

/-! ## The general registers -/

theorem lin_eval_m8 (σ : Nat → Int) : (⟨-8, [0, 0, 1]⟩ : Lin).eval σ = σ 2 - 8 := by
  simp [Lin.eval, dotC]
  omega

theorem lin_eval_512 (σ : Nat → Int) : (⟨512, [1]⟩ : Lin).eval σ = σ 0 + 512 := by
  simp [Lin.eval, dotC]
  omega

theorem lin_eval_256 (σ : Nat → Int) : (⟨256, [0, 1]⟩ : Lin).eval σ = σ 1 + 256 := by
  simp [Lin.eval, dotC]
  omega

/-- The registers outside `{rax, rcx}`: the cut's value under the renaming equals the x4 entry
value at the loop-shifted sigma.  The renaming fixes every region the registers point into. -/
theorem x8_gpr_pointwise (ρ : RegionRenaming) (hNum : ρ.f rNum = rNum) (hIn : ρ.f rIn = rIn)
    (hOut : ρ.f rOut = rOut) (hStack : ρ.f rStack = rStack) (hG : ρ.f rG = rG)
    (e' env : Key → W32) (σ' σ1 : Nat → Int)
    (hσ : ∀ k, 3 ≤ k → σ1 k = σ' k)
    (h0 : σ1 0 = σ' 0 + 512) (h1 : σ1 1 = σ' 1 + 256) (h2 : σ1 2 = σ' 2 - 8)
    (he : ∀ i, i < 100 → e' (.n i) = env (.n i))
    (i : Nat) (hi : i < 16) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    ρ.val (mapVal e' σ' (X8L.getD i (default : Val E Lin))) =
      mapVal env σ1 (E201L.getD i (default : Val E Lin)) := by
  have hdisj : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hdisj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [X8L, E201L, List.getD_cons_zero, List.getD_cons_succ]
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hNum, Lin.eval_sym,
      lin_eval_m8, h2]
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hStack, Lin.eval_sym,
      hσ 5 (by omega)]
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hStack, sAt, sAt_eval,
      hσ 9 (by omega)]
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hStack, Lin.eval_sym,
      hσ 6 (by omega)]
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hIn, Lin.eval_sym,
      lin_eval_512, h0]
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hOut, Lin.eval_sym,
      lin_eval_256, h1]
  · show ρ.val (.num (e' (.n 16)) (e' (.n 17))) = .num (env (.n 16)) (env (.n 17))
    rw [he 16 (by omega), he 17 (by omega)]
    rfl
  · show ρ.val (.num (e' (.n 18)) (e' (.n 19))) = .num (env (.n 18)) (env (.n 19))
    rw [he 18 (by omega), he 19 (by omega)]
    rfl
  · show ρ.val (.num (e' (.n 20)) (e' (.n 21))) = .num (env (.n 20)) (env (.n 21))
    rw [he 20 (by omega), he 21 (by omega)]
    rfl
  · show ρ.val (.num (e' (.n 22)) (e' (.n 23))) = .num (env (.n 22)) (env (.n 23))
    rw [he 22 (by omega), he 23 (by omega)]
    rfl
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hStack, Lin.eval_sym,
      hσ 7 (by omega)]
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hNum, Lin.eval_sym,
      hσ 11 (by omega)]
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hG, Lin.eval_sym,
      hσ 8 (by omega)]
  · simp only [mapVal, mapAddr, RegionRenaming.val, RegionRenaming.addr, hNum, Lin.eval_sym,
      hσ 12 (by omega)]

/-! ## The log-framed agreement at the x4 entry -/

/-- **The agreement at the x8 exit cut.**  The x4 entry state `refCut8` (the reference, first)
agrees with the renamed, resumed cut outside `{rax, rcx, flags}`.  No hypothesis on the log:
the fields that do not survive a nonempty log (`mem`, `vr`, the registers) are rebuilt by
`cutBare8`'s empty log and by `cutEnv8`. -/
theorem x4cut_agree (ρ : RegionRenaming) (hNum : ρ.f rNum = rNum) (hIn : ρ.f rIn = rIn)
    (hOut : ρ.f rOut = rOut) (hStack : ρ.f rStack = rStack) (hG : ρ.f rG = rG)
    {K : State E Lin} (hK : ExitCut K) (e' : Key → W32) (σ' : Nat → Int)
    (m : Addr Int → Cell W32 Int) :
    AgreeOn [0, 1, 16] (refCut8 K e' σ' m) (ρ.state (cutBare8 K e' σ')) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [refCut8, cutBare8, resume, mapState, entryW, RegionRenaming.state_pc]
  · simp only [refCut8, cutBare8, resume, mapState, entryW, RegionRenaming.state_halted]
  · simp only [refCut8, cutBare8, resume, mapState, entryW, RegionRenaming.state_tail]
  · simp only [refCut8, cutBare8, resume, mapState, entryW, RegionRenaming.state_err, hK.err]
  · simp only [refCut8, cutBare8, resume, mapState, entryW, RegionRenaming.state_mem,
      List.map_nil]
  · -- the vector lanes
    simp only [refCut8, cutBare8, resume, mapState, RegionRenaming.state_vr]
    rw [entryW_vr_shape, K_vr_eq_range hK]
    simp only [List.map_map, Function.comp_def]
    apply map_range_congr
    intro i hi
    exact cut_vr_lane8 hK e' (sigmaOf tau8 σ') m i (by simpa using hi)
  · simp only [refCut8, cutBare8, resume, mapState, entryW, RegionRenaming.state_assume]
  · intro h
    exact absurd (by decide : flg ∈ [0, 1, 16]) h
  · -- register file length
    simp only [refCut8, cutBare8, resume, mapState, RegionRenaming.state_gpr, hK.gpr,
      exitGpr_list, entryW_gpr_list, List.length_map, X8L_len, E201L_len]
  · -- the registers outside `{rax, rcx}`
    intro i hi
    have h3 : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 16 := by simpa using hi
    simp only [refCut8, cutBare8, resume, mapState, State.getG, RegionRenaming.state_gpr,
      hK.gpr, exitGpr_list, entryW_gpr_list, List.map_map, Function.comp_def]
    by_cases h16 : i < 16
    · rw [getD_map_lt _ _ _ (by rw [E201L_len]; exact h16),
        getD_map_lt _ _ _ (by rw [X8L_len]; exact h16)]
      exact (x8_gpr_pointwise ρ hNum hIn hOut hStack hG e' _ σ' (sigmaOf tau8 σ')
        (fun k hk => tau8_hi k hk σ') (tau8_in σ') (tau8_out σ') (tau8_count σ')
        (fun j hj => (cutEnv8_n_lo K e' (sigmaOf tau8 σ') m j (by omega)).symm)
        i h16 h3.1 h3.2.1).symm
    · rw [getD_default _ _ _ (by rw [List.length_map, E201L_len]; omega),
        getD_default _ _ _ (by rw [List.length_map, X8L_len]; omega)]
  · -- the pseudo-register `flg`
    have hf : flg = 16 := rfl
    simp only [refCut8, cutBare8, resume, mapState, State.getG, RegionRenaming.state_gpr,
      hK.gpr, exitGpr_list, entryW_gpr_list, List.map_map, Function.comp_def]
    rw [getD_default _ _ _ (by rw [List.length_map, E201L_len]; omega),
        getD_default _ _ _ (by rw [List.length_map, X8L_len]; omega)]

/-! ## The resumed cut as a framed state -/

/-- The exit cut's write log under the renaming: its own slice's writes and the turns before. -/
def cutLog8 (ρ : RegionRenaming) (K : State E Lin) (e' : Key → W32) (σ' : Nat → Int)
    (M' : CLog) : CLog :=
  renLog ρ ((mapState e' σ' K).mem ++ M')

/-- The state handed to the x4 link: the resumed, renamed cut with its log split off. -/
theorem resume_cut8 (ρ : RegionRenaming) (K : State E Lin) (e' : Key → W32) (σ' : Nat → Int)
    (M' : CLog) :
    resume (ρ.state (fr M' (mapState e' σ' K))) =
      fr (cutLog8 ρ K e' σ' M') (ρ.state (cutBare8 K e' σ')) := by
  simp only [resume, fr, cutBare8, cutLog8, renLog, RegionRenaming.state, List.map_append,
    List.map_nil, List.nil_append]

theorem fr_nil (s : CS) : fr [] s = s := by
  simp only [fr, List.append_nil]

/-- The W-mode log of the cut at the loop-shifted sigma, renamed. -/
theorem cutLog8_outLogW (ρ : RegionRenaming) (hOut : ρ.f rOut = rOut)
    (hStack : ρ.f rStack = rStack) (K : State E Lin) (e' : Key → W32) (σ' : Nat → Int)
    (M' : CLog) (hlog : OutLogW σ' ((mapState e' σ' K).mem ++ M')) :
    OutLogW (sigmaOf tau8 σ') (cutLog8 ρ K e' σ' M') :=
  outLogW_ren ρ hOut hStack _ _ (outLogW_congr σ' _ (tau8_s9 σ') _ hlog)

/-- The x4 memory shape at the cut: the x4 table at region 4 and the return marker survive the
log framing and the sigma shift. -/
theorem wf_cut8 (ρ : RegionRenaming) (hOut : ρ.f rOut = rOut) (hStack : ρ.f rStack = rStack)
    (K : State E Lin) (e' : Key → W32) (σ' : Nat → Int) (M' : CLog)
    (env0 : Key → W32) (σ0 : Nat → Int) (mem0c : Addr Int → Cell W32 Int)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ0 mem0c) (h9 : σ0 9 = σ' 9)
    (hlog : OutLogW σ' ((mapState e' σ' K).mem ++ M')) :
    WfMemW Hashtree.Kernels.X86.AvxX4.rodata []
      (cutEnv8 K e' (sigmaOf tau8 σ') (view (cutLog8 ρ K e' σ' M') mem0c))
      (sigmaOf tau8 σ') (view (cutLog8 ρ K e' σ' M') mem0c) :=
  wfAt_cut 4 Hashtree.Kernels.X86.AvxX4.rodata env0 _ σ0 (sigmaOf tau8 σ')
    (by rw [tau8_s9]; exact h9.symm) mem0c _ (cutLog8_outLogW ρ hOut hStack K e' σ' M' hlog)
    (by decide) (by decide) hw4

/-! ## The x4 link at the cut -/

theorem K201W_pc : K201W.pc = 4143 := by decide +kernel

/-- The x4 run's step count at the W-mode exit for `4 ≤ c < 8` (`x4_runW_last`'s literal). -/
def x4LastSteps : Nat := 72 + ((38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (55 + (38 + (38 + (38 + (26 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (27 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (25 + (38 + (4 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (48 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (37 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (2 + (1 + (1 + (4 + (2 + (1 + (1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + 27)

/-- **`4 ≤ c - 8 < 8`: the x4 W-mode exit.**  The x4 link entered at the resumed x8 cut runs,
up to `{rax, rcx}`, as the x4 all-count contract from the exact entry state: to the x4 exit
cut `K201W` behind the x8 cut's log, with a W-mode log. -/
theorem link_last (ρ : RegionRenaming) (hNum : ρ.f rNum = rNum) (hIn : ρ.f rIn = rIn)
    (hOut : ρ.f rOut = rOut) (hStack : ρ.f rStack = rStack) (hG : ρ.f rG = rG)
    {K : State E Lin} (hK : ExitCut K) (e' : Key → W32) (σ' : Nat → Int) (M' : CLog)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ0 : Nat → Int)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ0 mem0c) (h9 : σ0 9 = σ' 9)
    (hlog : OutLogW σ' ((mapState e' σ' K).mem ++ M'))
    (s : Nat) (hs : 4 ≤ s) (hs8 : s < 8) (hc : σ' 2 - 8 = (s : Int)) :
    let L : CLog := cutLog8 ρ K e' σ' M'
    let σ4 : Nat → Int := sigmaOf tau8 σ'
    ∃ (e4 : Key → W32) (M4 : CLog),
      AgreeOn [0, 1] (fr L (fr M4 (mapState e4 (sIt 0 (upd15 σ4)) K201W)))
        (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
          (resume (ρ.state (fr M' (mapState e' σ' K))))) ∧
      OutLogW (sIt 0 (upd15 σ4)) (K201W.mem.map (fun p =>
        (mapAddr (sIt 0 (upd15 σ4)) p.1, mapCell e4 (sIt 0 (upd15 σ4)) p.2)) ++ M4) := by
  intro L σ4
  have hw' := wf_cut8 ρ hOut hStack K e' σ' M' env0 σ0 mem0c hw4 h9 hlog
  obtain ⟨e4, M4, hrun, hlog4⟩ := x4_runW_last (cutEnv8 K e' σ4 (view L mem0c)) σ4
    (view L mem0c) orcC [] hw' (fun p hp => by cases hp) s hs hs8
    (by show sigmaOf tau8 σ' 2 = (s : Int); rw [tau8_count]; exact hc)
  rw [fr_nil] at hrun
  refine ⟨e4, M4, ?_, hlog4⟩
  rw [resume_cut8, run_fr]
  apply agreeOn_fr
  unfold x4LastSteps
  have hagree := run_agree4 4 (view L mem0c) orcC _ (refCut8 K e' σ' (view L mem0c))
    (ρ.state (cutBare8 K e' σ')) rfl (x4cut_agree ρ hNum hIn hOut hStack hG hK e' σ' (view L mem0c))
    (by rw [show refCut8 K e' σ' (view L mem0c) = mapState (cutEnv8 K e' σ4 (view L mem0c)) σ4 entryW from rfl, hrun]
        simp only [fr, mapState, K201W_err])
  rw [show refCut8 K e' σ' (view L mem0c) = mapState (cutEnv8 K e' σ4 (view L mem0c)) σ4 entryW from rfl, hrun] at hagree
  have hpc : (fr M4 (mapState e4 (sIt 0 (upd15 σ4)) K201W)).pc = 4143 := by
    simp only [fr, mapState, K201W_pc]
  rw [hpc, Dsx4_exit] at hagree
  exact hagree

/-- **`0 < c - 8 < 4`: the x4 small path.**  Eight steps to the `jmpTail` into x1 with the
entry registers (`KSm`), up to `{rax, rcx}`. -/
theorem link_small (ρ : RegionRenaming) (hNum : ρ.f rNum = rNum) (hIn : ρ.f rIn = rIn)
    (hOut : ρ.f rOut = rOut) (hStack : ρ.f rStack = rStack) (hG : ρ.f rG = rG)
    {K : State E Lin} (hK : ExitCut K) (e' : Key → W32) (σ' : Nat → Int) (M' : CLog)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ0 : Nat → Int)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ0 mem0c) (h9 : σ0 9 = σ' 9)
    (hlog : OutLogW σ' ((mapState e' σ' K).mem ++ M'))
    (hlt : σ' 2 - 8 < 4) (hne : σ' 2 - 8 ≠ 0) :
    let L : CLog := cutLog8 ρ K e' σ' M'
    let σ4 : Nat → Int := sigmaOf tau8 σ'
    let R0 : State E Lin := run Hashtree.Kernels.X86.AvxX4.prog 4
      (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW
    AgreeOn [0, 1] (fr L (mapState (envAbs (cutEnv8 K e' σ4 (view L mem0c)) R0) σ4 KSm))
      (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
        (resume (ρ.state (fr M' (mapState e' σ' K))))) := by
  intro L σ4 R0
  have hw' := wf_cut8 ρ hOut hStack K e' σ' M' env0 σ0 mem0c hw4 h9 hlog
  have hrun := small_prefix (cutEnv8 K e' σ4 (view L mem0c)) σ4 (view L mem0c) orcC hw'
    (cutEnv8_mem K e' σ4 (view L mem0c))
    (by show sigmaOf tau8 σ' 2 < 4; rw [tau8_count]; exact hlt)
    (by show sigmaOf tau8 σ' 2 ≠ 0; rw [tau8_count]; exact hne)
  rw [resume_cut8, run_fr]
  apply agreeOn_fr
  have hagree := run_agree4 4 (view L mem0c) orcC 8 (refCut8 K e' σ' (view L mem0c))
    (ρ.state (cutBare8 K e' σ')) rfl (x4cut_agree ρ hNum hIn hOut hStack hG hK e' σ' (view L mem0c))
    (by rw [show refCut8 K e' σ' (view L mem0c) = mapState (cutEnv8 K e' σ4 (view L mem0c)) σ4 entryW from rfl, hrun]
        simp only [mapState, KSm_err])
  rw [show refCut8 K e' σ' (view L mem0c) = mapState (cutEnv8 K e' σ4 (view L mem0c)) σ4 entryW from rfl, hrun] at hagree
  have hpc : (mapState (envAbs (cutEnv8 K e' σ4 (view L mem0c)) R0) σ4 KSm).pc = 4143 := by
    simp only [mapState, KSm_pc]
  rw [hpc, Dsx4_exit] at hagree
  exact hagree

/-- **`c - 8 = 0`: the x4 count-0 return.**  Four steps to the `ret`, with the callee-saved
registers and `rsp` restored and no memory write, up to `{rax, rcx, flags}`. -/
theorem link_zero (ρ : RegionRenaming) (hNum : ρ.f rNum = rNum) (hIn : ρ.f rIn = rIn)
    (hOut : ρ.f rOut = rOut) (hStack : ρ.f rStack = rStack) (hG : ρ.f rG = rG)
    {K : State E Lin} (hK : ExitCut K) (e' : Key → W32) (σ' : Nat → Int) (M' : CLog)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (env0 : Key → W32) (σ0 : Nat → Int)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ0 mem0c) (h9 : σ0 9 = σ' 9)
    (hlog : OutLogW σ' ((mapState e' σ' K).mem ++ M'))
    (hz : σ' 2 - 8 = 0) :
    let L : CLog := cutLog8 ρ K e' σ' M'
    let σ4 : Nat → Int := sigmaOf tau8 σ'
    let fin : CS := run Hashtree.Kernels.X86.AvxX4.prog 4 (view L mem0c) orcC 4
      (refCut8 K e' σ' (view L mem0c))
    AgreeOn [0, 1, 16] (fr L fin)
      (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 4
        (resume (ρ.state (fr M' (mapState e' σ' K))))) ∧
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧ fin.mem = [] ∧
      fin.getG 4 = .ptr ⟨rStack, σ4 9 + 8⟩ ∧ fin.getG 3 = .ptr ⟨rStack, σ4 5⟩ ∧
      fin.getG 5 = .ptr ⟨rStack, σ4 6⟩ ∧ fin.getG 12 = .ptr ⟨rStack, σ4 7⟩ ∧
      fin.getG 14 = .ptr ⟨rG, σ4 8⟩ ∧ fin.getG 13 = .ptr ⟨rNum, σ4 11⟩ ∧
      fin.getG 15 = .ptr ⟨rNum, σ4 12⟩ := by
  intro L σ4 fin
  have hw' := wf_cut8 ρ hOut hStack K e' σ' M' env0 σ0 mem0c hw4 h9 hlog
  have hz' := zero_run (cutEnv8 K e' σ4 (view L mem0c)) σ4 (view L mem0c) orcC hw'
    (cutEnv8_mem K e' σ4 (view L mem0c))
    (by show sigmaOf tau8 σ' 2 = 0; rw [tau8_count]; exact hz)
  obtain ⟨hh, herr, ht, hm, hr4, hr3, hr5, hr12, hr14, hr13, hr15⟩ := hz'
  refine ⟨?_, hh, herr, ht, hm, hr4, hr3, hr5, hr12, hr14, hr13, hr15⟩
  rw [resume_cut8, run_fr]
  apply agreeOn_fr
  have hagree := run_agree4 4 (view L mem0c) orcC 4 (refCut8 K e' σ' (view L mem0c))
    (ρ.state (cutBare8 K e' σ')) rfl (x4cut_agree ρ hNum hIn hOut hStack hG hK e' σ' (view L mem0c))
    herr
  exact hagree.mono (fun i hi => by
    rcases mem_Dsx4 i _ hi with rfl | rfl | rfl <;> simp)

/-! ## The x8 -> x4 edge, all counts -/

/-- `mapState`'s log, as a rewrite (generic in the cut, so no cut is unfolded). -/
theorem mapState_mem_eq (e : Key → W32) (τ : Nat → Int) (K : State E Lin) :
    (mapState e τ K).mem = K.mem.map (fun p => (mapAddr τ p.1, mapCell e τ p.2)) := rfl

/-- The x4 residual count of the x8 run at `c = 8 (j + 1) + s`. -/
theorem sIt8_count8 (j s : Nat) (σ : Nat → Int) (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int)) :
    sIt8 (j + 1) (upd15 σ) 2 - 8 = (s : Int) - 8 := by
  rw [sIt8_count]
  have h : upd15 σ 2 = σ 2 := by simp [upd15]
  rw [h, hc]
  omega

theorem sIt8_9 (j : Nat) (σ : Nat → Int) : sIt8 j (upd15 σ) 9 = σ 9 := by
  rw [sIt8_s9, upd15_9]

/-- **x8 -> x4 at the W-mode exit cut, `c = 8 (j + 1) + s` with `12 ≤ s < 16`.**  The x8 run
(table at `r8`) reaches its exit cut; the x4 link (table at region 4) entered at the resumed
cut reaches the x4 exit cut `K201W` behind the x8 log, up to `{rax, rcx}`. -/
theorem x8_x4_W_last (j s : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hs : 12 ≤ s) (hs16 : s < 16)
    (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int)) (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
          (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31)))) (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r))) ∧
      OutLogW (sIt8 (j + 1) (upd15 σ))
        ((mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r)).mem ++ M') ∧
      (let σ' : Nat → Int := sIt8 (j + 1) (upd15 σ)
       let L : CLog := cutLog8 (swap 4 r8) (KTEs r) e' σ' M'
       let σ4 : Nat → Int := sigmaOf tau8 σ'
       ∃ (e4 : Key → W32) (M4 : CLog),
         AgreeOn [0, 1] (fr L (fr M4 (mapState e4 (sIt 0 (upd15 σ4)) K201W)))
           (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
             (resume ((swap 4 r8).state (fr M' (mapState e' σ' (KTEs r)))))) ∧
         OutLogW (sIt 0 (upd15 σ4)) (K201W.mem.map (fun p =>
           (mapAddr (sIt 0 (upd15 σ4)) p.1, mapCell e4 (sIt 0 (upd15 σ4)) p.2)) ++ M4)) := by
  obtain ⟨r, e', M', hr, hrun, hlog⟩ := x8_runW_at r8 hrNum hrIn hrOut hrStack hrG hrRet env0 σ
    mem0c orcC M hw8 hM j s (by omega) hs16 hc habi
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  replace hlog : OutLogW (sIt8 (j + 1) (upd15 σ))
      ((mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r)).mem ++ M') := by
    rw [mapState_mem_eq]; exact hlog
  refine ⟨r, e', M', hr, hrun, hlog, ?_⟩
  exact link_last (swap 4 r8) f0 f1 f2 f3 f6 (exitCut_KTEs r hr) e' _ M' mem0c orcC env0 σ hw4
    (sIt8_9 (j + 1) σ).symm hlog (s - 8) (by omega) (by omega)
    (by rw [sIt8_count8 j s σ hc]; omega)

/-- **x8 -> x4 at the W-mode exit cut, `c = 8 (j + 1) + s` with `9 ≤ s < 12`.**  The x4 link
takes its small path to the `jmpTail` into x1 with the entry registers. -/
theorem x8_x4_W_small (j s : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hs : 9 ≤ s) (hs12 : s < 12)
    (hc : σ 2 = 8 * ((j : Int) + 1) + (s : Int)) (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
          (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31)))) (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r))) ∧
      OutLogW (sIt8 (j + 1) (upd15 σ))
        ((mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r)).mem ++ M') ∧
      (let σ' : Nat → Int := sIt8 (j + 1) (upd15 σ)
       let L : CLog := cutLog8 (swap 4 r8) (KTEs r) e' σ' M'
       let σ4 : Nat → Int := sigmaOf tau8 σ'
       let R0 : State E Lin := run Hashtree.Kernels.X86.AvxX4.prog 4
         (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW
       AgreeOn [0, 1]
         (fr L (mapState (envAbs (cutEnv8 (KTEs r) e' σ4 (view L mem0c)) R0) σ4 KSm))
         (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
           (resume ((swap 4 r8).state (fr M' (mapState e' σ' (KTEs r))))))) := by
  obtain ⟨r, e', M', hr, hrun, hlog⟩ := x8_runW_at r8 hrNum hrIn hrOut hrStack hrG hrRet env0 σ
    mem0c orcC M hw8 hM j s (by omega) (by omega) hc habi
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  replace hlog : OutLogW (sIt8 (j + 1) (upd15 σ))
      ((mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r)).mem ++ M') := by
    rw [mapState_mem_eq]; exact hlog
  refine ⟨r, e', M', hr, hrun, hlog, ?_⟩
  exact link_small (swap 4 r8) f0 f1 f2 f3 f6 (exitCut_KTEs r hr) e' _ M' mem0c orcC env0 σ hw4
    (sIt8_9 (j + 1) σ).symm hlog (by rw [sIt8_count8 j s σ hc]; omega)
    (by rw [sIt8_count8 j s σ hc]; omega)

/-- **x8 -> x4 at the W-mode exit cut, `c = 8 (j + 1) + 8`.**  The x4 link returns at once. -/
theorem x8_x4_W_zero (j : Nat) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hc : σ 2 = 8 * ((j : Int) + 1) + 8) (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC
          (16 + (TURNLEN + (j * TURNLEN + (BODYLEN + 31)))) (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r))) ∧
      OutLogW (sIt8 (j + 1) (upd15 σ))
        ((mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r)).mem ++ M') ∧
      (let σ' : Nat → Int := sIt8 (j + 1) (upd15 σ)
       let L : CLog := cutLog8 (swap 4 r8) (KTEs r) e' σ' M'
       let σ4 : Nat → Int := sigmaOf tau8 σ'
       let fin : CS := run Hashtree.Kernels.X86.AvxX4.prog 4 (view L mem0c) orcC 4
         (refCut8 (KTEs r) e' σ' (view L mem0c))
       AgreeOn [0, 1, 16] (fr L fin)
         (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 4
           (resume ((swap 4 r8).state (fr M' (mapState e' σ' (KTEs r)))))) ∧
       fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧ fin.mem = [] ∧
         fin.getG 4 = .ptr ⟨rStack, σ4 9 + 8⟩ ∧ fin.getG 3 = .ptr ⟨rStack, σ4 5⟩ ∧
         fin.getG 5 = .ptr ⟨rStack, σ4 6⟩ ∧ fin.getG 12 = .ptr ⟨rStack, σ4 7⟩ ∧
         fin.getG 14 = .ptr ⟨rG, σ4 8⟩ ∧ fin.getG 13 = .ptr ⟨rNum, σ4 11⟩ ∧
         fin.getG 15 = .ptr ⟨rNum, σ4 12⟩) := by
  obtain ⟨r, e', M', hr, hrun, hlog⟩ := x8_runW_at r8 hrNum hrIn hrOut hrStack hrG hrRet env0 σ
    mem0c orcC M hw8 hM j 8 (by omega) (by omega) (by omega) habi
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  replace hlog : OutLogW (sIt8 (j + 1) (upd15 σ))
      ((mapState e' (sIt8 (j + 1) (upd15 σ)) (KTEs r)).mem ++ M') := by
    rw [mapState_mem_eq]; exact hlog
  refine ⟨r, e', M', hr, hrun, hlog, ?_⟩
  exact link_zero (swap 4 r8) f0 f1 f2 f3 f6 (exitCut_KTEs r hr) e' _ M' mem0c orcC env0 σ hw4
    (sIt8_9 (j + 1) σ).symm hlog
    (by rw [sIt8_count8 j 8 σ (by omega)]; omega)

/-! ### The single-pass x8 run (`8 ≤ c < 16`) -/

theorem upd15_count8 (σ : Nat → Int) : upd15 σ 2 - 8 = σ 2 - 8 := by
  simp [upd15]

/-- **x8 -> x4 for `12 ≤ c < 16`.**  One x8 pass, then the x4 W-mode exit. -/
theorem x8_x4_W1_last (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (s : Nat) (hs : 4 ≤ s) (hs8 : s < 8) (hc : σ 2 = (s : Int) + 8)
    (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
          (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r))) ∧
      OutLogW (upd15 σ) ((mapState e' (upd15 σ) (KTE r)).mem ++ M') ∧
      (let L : CLog := cutLog8 (swap 4 r8) (KTE r) e' (upd15 σ) M'
       let σ4 : Nat → Int := sigmaOf tau8 (upd15 σ)
       ∃ (e4 : Key → W32) (M4 : CLog),
         AgreeOn [0, 1] (fr L (fr M4 (mapState e4 (sIt 0 (upd15 σ4)) K201W)))
           (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC x4LastSteps
             (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r)))))) ∧
         OutLogW (sIt 0 (upd15 σ4)) (K201W.mem.map (fun p =>
           (mapAddr (sIt 0 (upd15 σ4)) p.1, mapCell e4 (sIt 0 (upd15 σ4)) p.2)) ++ M4)) := by
  obtain ⟨r, e', M', hr, hrun, hlog⟩ := x8_runW_last_at r8 hrNum hrIn hrOut hrStack hrG hrRet
    env0 σ mem0c orcC M hw8 hM (by omega) (by omega) habi
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  replace hlog : OutLogW (upd15 σ)
      ((mapState e' (upd15 σ) (KTE r)).mem ++ M') := by
    rw [mapState_mem_eq]; exact hlog
  refine ⟨r, e', M', hr, hrun, hlog, ?_⟩
  exact link_last (swap 4 r8) f0 f1 f2 f3 f6 (exitCut_KTE r hr) e' _ M' mem0c orcC env0 σ hw4
    (upd15_9 σ).symm hlog s hs hs8 (by rw [upd15_count8, hc]; omega)

/-- **x8 -> x4 for `9 ≤ c < 12`.**  One x8 pass, then the x4 small path. -/
theorem x8_x4_W1_small (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hge : 9 ≤ σ 2) (hlt : σ 2 < 12) (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
          (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r))) ∧
      OutLogW (upd15 σ) ((mapState e' (upd15 σ) (KTE r)).mem ++ M') ∧
      (let L : CLog := cutLog8 (swap 4 r8) (KTE r) e' (upd15 σ) M'
       let σ4 : Nat → Int := sigmaOf tau8 (upd15 σ)
       let R0 : State E Lin := run Hashtree.Kernels.X86.AvxX4.prog 4
         (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW
       AgreeOn [0, 1]
         (fr L (mapState (envAbs (cutEnv8 (KTE r) e' σ4 (view L mem0c)) R0) σ4 KSm))
         (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
           (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r))))))) := by
  obtain ⟨r, e', M', hr, hrun, hlog⟩ := x8_runW_last_at r8 hrNum hrIn hrOut hrStack hrG hrRet
    env0 σ mem0c orcC M hw8 hM (by omega) (by omega) habi
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  replace hlog : OutLogW (upd15 σ)
      ((mapState e' (upd15 σ) (KTE r)).mem ++ M') := by
    rw [mapState_mem_eq]; exact hlog
  refine ⟨r, e', M', hr, hrun, hlog, ?_⟩
  exact link_small (swap 4 r8) f0 f1 f2 f3 f6 (exitCut_KTE r hr) e' _ M' mem0c orcC env0 σ hw4
    (upd15_9 σ).symm hlog (by rw [upd15_count8]; omega) (by rw [upd15_count8]; omega)

/-- **x8 -> x4 for `c = 8`.**  One x8 pass, then the x4 count-0 return. -/
theorem x8_x4_W1_zero (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (M : CLog) (r8 : Region)
    (hrNum : r8 ≠ rNum) (hrIn : r8 ≠ rIn) (hrOut : r8 ≠ rOut) (hrStack : r8 ≠ rStack)
    (hrG : r8 ≠ rG) (hrRet : r8 ≠ rRet)
    (hw8 : WfMemAtW r8 Hashtree.Kernels.X86.Avx2X8.rodata [] env0 σ mem0c)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (hM : OutLogW σ M) (hc : σ 2 = 8) (habi : σ 9 % 16 = 8) :
    ∃ (r : Nat) (e' : Key → W32) (M' : CLog), (r = 0 ∨ r = 16) ∧
      run Hashtree.Kernels.X86.Avx2X8.prog r8 mem0c orcC (16 + (BODYLEN + 31))
          (fr M (mapState env0 σ entryW)) =
        (swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r))) ∧
      OutLogW (upd15 σ) ((mapState e' (upd15 σ) (KTE r)).mem ++ M') ∧
      (let L : CLog := cutLog8 (swap 4 r8) (KTE r) e' (upd15 σ) M'
       let σ4 : Nat → Int := sigmaOf tau8 (upd15 σ)
       let fin : CS := run Hashtree.Kernels.X86.AvxX4.prog 4 (view L mem0c) orcC 4
         (refCut8 (KTE r) e' (upd15 σ) (view L mem0c))
       AgreeOn [0, 1, 16] (fr L fin)
         (run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 4
           (resume ((swap 4 r8).state (fr M' (mapState e' (upd15 σ) (KTE r)))))) ∧
       fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧ fin.mem = [] ∧
         fin.getG 4 = .ptr ⟨rStack, σ4 9 + 8⟩ ∧ fin.getG 3 = .ptr ⟨rStack, σ4 5⟩ ∧
         fin.getG 5 = .ptr ⟨rStack, σ4 6⟩ ∧ fin.getG 12 = .ptr ⟨rStack, σ4 7⟩ ∧
         fin.getG 14 = .ptr ⟨rG, σ4 8⟩ ∧ fin.getG 13 = .ptr ⟨rNum, σ4 11⟩ ∧
         fin.getG 15 = .ptr ⟨rNum, σ4 12⟩) := by
  obtain ⟨r, e', M', hr, hrun, hlog⟩ := x8_runW_last_at r8 hrNum hrIn hrOut hrStack hrG hrRet
    env0 σ mem0c orcC M hw8 hM (by omega) (by omega) habi
  obtain ⟨f0, f1, f2, f3, f6⟩ := swap_fix r8 hrNum hrIn hrOut hrStack hrG
  replace hlog : OutLogW (upd15 σ)
      ((mapState e' (upd15 σ) (KTE r)).mem ++ M') := by
    rw [mapState_mem_eq]; exact hlog
  refine ⟨r, e', M', hr, hrun, hlog, ?_⟩
  exact link_zero (swap 4 r8) f0 f1 f2 f3 f6 (exitCut_KTE r hr) e' _ M' mem0c orcC env0 σ hw4
    (upd15_9 σ).symm hlog (by rw [upd15_count8, hc]; omega)

end Hashtree.Proofs.Avx2X8X4WAgree
