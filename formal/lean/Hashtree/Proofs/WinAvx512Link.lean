import Hashtree.Proofs.WinAvx512Bridge
import Hashtree.Proofs.WinAvx512
import Hashtree.Proofs.WinShaniBridge

/-!
# R5: the windows chain link `avx512_x16 -> avx2_x8`, proved from R2b's loop certificate

`KSpecC512_of_turnOut`: under the (explicit, named) output-byte hypothesis `TurnOut` (R2c), the
avx512_x16 link obligation `KSpecC512` holds with R2b's step function `Avx512X16WLoop.steps`.
The windows stream is the renaming `renSt F G` of the linux stream (`WinAvx512.win_transfer`);
the wrapper call state agrees with the renamed linux certificate start state on the kernel's
entry live set `[8, 4, 2, 1]` (`seed_agree512`), so `run_agree` carries R2b's `x16_zero_run`,
`x16_small_run`, `x16_loop` to the windows run; the Win64 callee-saved registers the next link
reads are never written by the stream (`WinAvx512Live.unwritten`, `run_preserve_all`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

namespace Hashtree.Proofs.WinAvx512Link

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.BodyReads
open Hashtree.Asm.RunAgree Hashtree.Asm.RunExit
open Hashtree.Proofs.X86Chain Hashtree.Proofs.WinChain
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.ShaniW (OutLogW)
open Hashtree.Proofs.WinAvx512Bridge
open Hashtree.Proofs.WinAvx512 (F G win_transfer win_correspondence renPerm)
open Hashtree.Proofs.Avx512X16WLoop (steps steps_zero steps_small steps_loop sIt sIt_zero sIt_succ
  sIt_count sIt_9 x16_zero_run x16_small_run x16_loop fr_nil)
open Hashtree.Proofs.Avx512X16WEntry (KZ KSm KTE KZ_pc KZ_mem KZ_halted KSm_tail KTE_tail tau)
open Hashtree.Proofs.WinShaniBridge (stW stW_len stW_halted entryWin_gpr1 entryWin_gpr2 entryWin_gpr4
  entryWin_gpr8 entryWin_gpr3 entryWin_gpr5 entryWin_gpr12 entryWin_gpr13 entryWin_gpr14 entryWin_gpr15
  getElem?_of_getG)
open Hashtree.Proofs.WinShaniSeedAlign (mapState_getG)
open Hashtree.Proofs.WrapperAmd64 (sAt_eval)

abbrev linuxProg : Array Instr := Hashtree.Kernels.X86.Avx512X16.prog
abbrev rodata : List Nat := Hashtree.Kernels.X86.Avx512X16.rodata
abbrev mW : Addr Lin → Cell E Lin := Hashtree.Proofs.Avx512X16WBody.mW

theorem rodata_eq : Hashtree.Kernels.X86Win.Avx512X16.rodata = rodata := by decide +kernel

/-! ## Kernel-decided facts about the certificate cut states -/

theorem entryW_len : entryW.gpr.length = 16 := by decide +kernel
theorem entryW_gpr2 : entryW.gpr[2]? = some (.ptr ⟨rNum, Lin.sym 2⟩) := by decide +kernel
theorem entryW_gpr4 : entryW.gpr[4]? = some (.ptr ⟨rStack, sAt 0⟩) := by decide +kernel
theorem entryW_gpr6 : entryW.gpr[6]? = some (.ptr ⟨rIn, Lin.sym 0⟩) := by decide +kernel
theorem entryW_gpr7 : entryW.gpr[7]? = some (.ptr ⟨rOut, Lin.sym 1⟩) := by decide +kernel

theorem KZ_gpr4 : KZ.gpr[4]? = some (.ptr ⟨rStack, sAt 8⟩) := by decide +kernel
theorem KSm_gpr2 : KSm.gpr[2]? = some (.ptr ⟨rNum, Lin.sym 2⟩) := by decide +kernel
theorem KSm_gpr4 : KSm.gpr[4]? = some (.ptr ⟨rStack, sAt 0⟩) := by decide +kernel
theorem KSm_gpr6 : KSm.gpr[6]? = some (.ptr ⟨rIn, Lin.sym 0⟩) := by decide +kernel
theorem KSm_gpr7 : KSm.gpr[7]? = some (.ptr ⟨rOut, Lin.sym 1⟩) := by decide +kernel
theorem KSm_vr : KSm.vr = entryW.vr := by decide +kernel
theorem KSm_pc : KSm.pc = 8 := by decide +kernel
theorem KSm_mem' : KSm.mem = [] := by decide +kernel
theorem KSm_halted' : KSm.halted = true := by decide +kernel
theorem KTE_pc : KTE.pc = 8 := by decide +kernel
theorem KTE_halted' : KTE.halted = true := by decide +kernel
theorem KTE_gpr2 : KTE.gpr[2]? = some (.ptr ⟨rNum, ⟨-16, [0, 0, 1]⟩⟩) := by decide +kernel
theorem KTE_gpr4 : KTE.gpr[4]? = some (.ptr ⟨rStack, sAt 0⟩) := by decide +kernel
theorem KTE_gpr6 : KTE.gpr[6]? = some (.ptr ⟨rIn, ⟨1024, [1]⟩⟩) := by decide +kernel
theorem KTE_gpr7 : KTE.gpr[7]? = some (.ptr ⟨rOut, ⟨512, [0, 1]⟩⟩) := by decide +kernel
theorem KTE_mem_out : KTE.mem.all (fun p => p.1.region == rOut) = true := by decide +kernel
theorem KTE_vr_shape : KTE.vr.length = 32 ∧ KTE.vr.all (fun v => v.length == 16) = true := by
  decide +kernel
theorem entryW_vr_shape : entryW.vr.length = 32 ∧ entryW.vr.all (fun v => v.length == 16) = true := by
  decide +kernel

theorem live3 : 4 ∈ Hashtree.Proofs.WinAvx512Live.liveT.getD 3 [] := by decide +kernel
theorem tail8 : p512[8]? = some (.jccTail .b "hashtree_sha256_avx2_x8") := WinChain.win_chain_tails.1

/-! ## The loop substitution on the symbols -/

theorem sigmaOf_tau_0 (σ : Nat → Int) : sigmaOf tau σ 0 = σ 0 + 1024 := by
  simp [sigmaOf, tauAt, tau, Lin.eval, dotC]; omega
theorem sigmaOf_tau_1 (σ : Nat → Int) : sigmaOf tau σ 1 = σ 1 + 512 := by
  simp [sigmaOf, tauAt, tau, Lin.eval, dotC]; omega
theorem sigmaOf_tau_ge3 (σ : Nat → Int) (i : Nat) (hi : 3 ≤ i) : sigmaOf tau σ i = σ i := by
  simp only [sigmaOf, tauAt, tau]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
  simp [Lin.eval_sym]

theorem sIt_0 : ∀ (j : Nat) (σ : Nat → Int), sIt j σ 0 = σ 0 + 1024 * (j : Int)
  | 0, σ => by simp [sIt_zero]
  | j + 1, σ => by rw [sIt_succ, sIt_0 j, sigmaOf_tau_0]; omega
theorem sIt_1 : ∀ (j : Nat) (σ : Nat → Int), sIt j σ 1 = σ 1 + 512 * (j : Int)
  | 0, σ => by simp [sIt_zero]
  | j + 1, σ => by rw [sIt_succ, sIt_1 j, sigmaOf_tau_1]; omega
theorem sIt_ge3 : ∀ (j : Nat) (σ : Nat → Int) (i : Nat), 3 ≤ i → sIt j σ i = σ i
  | 0, σ, _, _ => by simp [sIt_zero]
  | j + 1, σ, i, hi => by rw [sIt_succ, sIt_ge3 j _ i hi, sigmaOf_tau_ge3 σ i hi]

/-! ## The certificate environment and the entry agreement -/

section Main
variable (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)

/-- Symbol 10 (unread by `entryW`) pinned to the output base, as `x16_loop` requires. -/
def σW : Nat → Int := fun i => if i = 10 then σ 1 else σ i

theorem σW_ne (i : Nat) (h : i ≠ 10) : σW σ i = σ i := by simp [σW, h]
theorem σW_10 : σW σ 10 = σ 1 := by simp [σW]

/-- The certificate environment: the windows one on numbered symbols, the memory cells on memory
symbols (so `EnvMem` holds by construction). -/
def eL : Key → W32 := fun k => match k with
  | .n i => env (.n i)
  | .m r off => cellX (m0 ⟨r, off.eval (σW σ)⟩)

theorem envMem_eL : EnvMem (eL env σ m0) (σW σ) m0 := fun _ _ => rfl

theorem wf_eL (hw : WfMemW rodata [] env σ m0) : WfMemW rodata [] (eL env σ m0) (σW σ) m0 := by
  obtain ⟨h1, h2, h3, _⟩ := hw
  refine ⟨h1, fun k hk0 hk8 => ?_, h3, fun k c hl => by simp [plookup] at hl⟩
  rw [σW_ne σ 9 (by decide)]
  exact h2 k hk0 hk8

theorem h0_eL (hw : WfMemW rodata [] env σ m0) : Mem0Rel (eL env σ m0) (σW σ) mW m0 :=
  mem0RelW_of_wf rodata [] _ _ _ (wf_eL env σ m0 hw) (envMem_eL env σ m0)

/-- The renamed certificate start state. -/
def sL : CState := renSt F G (mapState (eL env σ m0) (σW σ) entryW)

theorem sL_len : (sL env σ m0).gpr.length = 16 := Hashtree.Asm.X86.renSt_gpr_len F G _

theorem vr_eqW : entryW.vr.map (·.map (E.eval (eL env σ m0))) = entryWin.vr.map (·.map (E.eval env)) := by
  show entryW.vr.map _ = entryW.vr.map _
  apply List.map_congr_left
  intro v hv
  simp only [entryW, List.mem_map, List.mem_range] at hv
  obtain ⟨i, _, rfl⟩ := hv
  simp only [List.map_map]
  apply List.map_congr_left
  intro l _
  rfl

/-- The windows register `F j` of the renamed state is the linux register `j`. -/
theorem sL_getG (j : Nat) (hF : F j < 16) (hG : G (F j) = j) :
    (sL env σ m0).getG (F j) = (mapState (eL env σ m0) (σW σ) entryW).getG j :=
  Hashtree.Asm.X86.renSt_getG F G _ j hF hG

/-- The wrapper call state agrees with the renamed certificate start state on the entry live set. -/
theorem seed_agree512 : Agree [8, 4, 2, 1] false (mapState env σ entryWin) (sL env σ m0) := by
  refine ⟨?_, ?_, ?_, (fun h => by cases h), rfl, rfl, rfl, rfl, rfl⟩
  · intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have h := sL_getG env σ m0 2 (by decide) (by decide)
      rw [show F 2 = 8 from rfl] at h
      rw [mapState_getG entryWin_gpr8, h, mapState_getG entryW_gpr2]
      simp [mapVal, mapAddr, Lin.eval_sym, σW]
    · have h := sL_getG env σ m0 4 (by decide) (by decide)
      rw [show F 4 = 4 from rfl] at h
      rw [mapState_getG entryWin_gpr4, h, mapState_getG entryW_gpr4]
      simp [mapVal, mapAddr, sAt_eval, σW]
    · have h := sL_getG env σ m0 6 (by decide) (by decide)
      rw [show F 6 = 2 from rfl] at h
      rw [mapState_getG entryWin_gpr2, h, mapState_getG entryW_gpr6]
      simp [mapVal, mapAddr, Lin.eval_sym, σW]
    · have h := sL_getG env σ m0 7 (by decide) (by decide)
      rw [show F 7 = 1 from rfl] at h
      rw [mapState_getG entryWin_gpr1, h, mapState_getG entryW_gpr7]
      simp [mapVal, mapAddr, Lin.eval_sym, σW]
  · show (entryWin.gpr.map _).length = (sL env σ m0).gpr.length
    rw [List.length_map, sL_len]; decide +kernel
  · show (entryWin.vr.map _) = (mapState (eL env σ m0) (σW σ) entryW).vr
    exact (vr_eqW env σ m0).symm

/-! ## The windows run against the linux run -/

/-- The windows run from the wrapper call state. -/
def W (c : Nat) : CState := run p512 4 m0 orcC (steps c) (mapState env σ entryWin)
/-- The linux run from the certificate start state. -/
def fL (c : Nat) : CState := run linuxProg 4 m0 orcC (steps c) (mapState (eL env σ m0) (σW σ) entryW)

theorem agree_fin (hw : WfMemW rodata [] env σ m0) (c : Nat) :
    Agree (Hashtree.Proofs.WinAvx512Live.liveT.getD (W env σ m0 orcC c).pc [])
      (Hashtree.Proofs.WinAvx512Live.liveFT.getD (W env σ m0 orcC c).pc false)
      (W env σ m0 orcC c) (run p512 4 m0 orcC (steps c) (sL env σ m0)) := by
  apply run_agree p512 4 m0 orcC Hashtree.Proofs.WinAvx512Live.cert (steps c)
  show Agree (Hashtree.Proofs.WinAvx512Live.liveT.getD 0 [])
    (Hashtree.Proofs.WinAvx512Live.liveFT.getD 0 false) _ _
  rw [Hashtree.Proofs.WinAvx512Live.live_entry_eq, Hashtree.Proofs.WinAvx512Live.liveF_entry]
  exact seed_agree512 env σ m0

theorem ren_fin (c : Nat) (hf : (fL env σ m0 orcC c).err = none) :
    run p512 4 m0 orcC (steps c) (sL env σ m0) = renSt F G (fL env σ m0 orcC c) :=
  win_transfer (ro := 4) (mem0 := m0) (orc := orcC) win_correspondence (steps c) _
    (by show (entryW.gpr.map _).length = 16; rw [List.length_map, entryW_len]) rfl hf

/-- The callee-saved registers (and rsi/rdi) of the windows run are the entry values. -/
theorem W_preserve (c : Nat) (hW : (W env σ m0 orcC c).err = none) (r : Nat)
    (hr : r ∈ [3, 5, 6, 7, 12, 13, 14, 15]) :
    (W env σ m0 orcC c).getG r = (mapState env σ entryWin).getG r :=
  run_preserve_all p512 4 m0 orcC r (unwrittenScan_sound Hashtree.Proofs.WinAvx512Live.unwritten r hr)
    (steps c) _ hW

theorem W_len (c : Nat) : (W env σ m0 orcC c).gpr.length = 16 :=
  Hashtree.Proofs.WinShaniCall.run_gpr_len p512 (steps c) _ (stW_len env σ)

end Main

/-! ## Projections, syntactically (never `show`/`rfl` against a computed cut state) -/

section Proj
variable {M : CLog} {s : CState} {e : Key → W32} {τ : Nat → Int} {K : State E Lin}
theorem fr_err' : (fr M s).err = s.err := rfl
theorem fr_tail' : (fr M s).tail = s.tail := rfl
theorem fr_halted' : (fr M s).halted = s.halted := rfl
theorem fr_pc' : (fr M s).pc = s.pc := rfl
theorem fr_vr' : (fr M s).vr = s.vr := rfl
theorem fr_mem' : (fr M s).mem = s.mem ++ M := rfl
theorem fr_getG' (j : Nat) : (fr M s).getG j = s.getG j := rfl
theorem renSt_fr_getG (j : Nat) : (renSt F G (fr M s)).getG j = (renSt F G s).getG j := rfl
theorem mapState_err' : (mapState e τ K).err = K.err := rfl
theorem mapState_tail' : (mapState e τ K).tail = K.tail := rfl
theorem mapState_halted' : (mapState e τ K).halted = K.halted := rfl
theorem mapState_pc' : (mapState e τ K).pc = K.pc := rfl
theorem mapState_vr' : (mapState e τ K).vr = K.vr.map (·.map (E.eval e)) := rfl
theorem mapState_mem' : (mapState e τ K).mem = K.mem.map (fun p => (mapAddr τ p.1, mapCell e τ p.2)) := rfl
end Proj

/-! ## The link theorem -/

section Final
variable (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)

theorem shift_ge3 (d r i : Nat) (hi : 3 ≤ i) : shift σ d r i = σ i := by
  simp [shift, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega]

/-- The next link's comparison state (the entry state with the symbols advanced, vector file `V`,
log `M'`). -/
def cmpSt (d r : Nat) (V : List (List W32)) (M' : CLog) : CState :=
  fr M' { mapState env (shift σ d r) entryWin with vr := V }

theorem cmpSt_getG (d r : Nat) (V : List (List W32)) (M' : CLog) {j : Nat} {v : Val E Lin}
    (hj : entryWin.gpr[j]? = some v) : (cmpSt env σ d r V M').getG j = mapVal env (shift σ d r) v := by
  show (mapState env (shift σ d r) entryWin).getG j = _
  exact mapState_getG hj

theorem cmpSt_len (d r : Nat) (V : List (List W32)) (M' : CLog) : (cmpSt env σ d r V M').gpr.length = 16 :=
  stW_len env (shift σ d r)

/-- The preserved registers agree with the advanced entry state (their symbols are not moved). -/
theorem preserved_cmp (c d r : Nat) (hW : (W env σ m0 orcC c).err = none) (V : List (List W32)) (M' : CLog)
    (j : Nat) (hj : j ∈ [5, 6, 12, 13, 14, 15]) :
    (W env σ m0 orcC c).getG j = (cmpSt env σ d r V M').getG j := by
  rw [W_preserve env σ m0 orcC c hW j (by simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj ⊢; omega)]
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr5, show (mapState env σ entryWin).getG 5 = _ from mapState_getG entryWin_gpr5]
    simp [mapVal, mapAddr, Lin.eval_sym, shift_ge3]
  · have h6 : entryWin.gpr[6]? = some (.num (.var (.n (gId 6 0))) (.var (.n (gId 6 1)))) := by decide +kernel
    rw [cmpSt_getG env σ d r V M' h6, show (mapState env σ entryWin).getG 6 = _ from mapState_getG h6]
    rfl
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr12, show (mapState env σ entryWin).getG 12 = _ from mapState_getG entryWin_gpr12]
    simp [mapVal, mapAddr, Lin.eval_sym, shift_ge3]
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr13, show (mapState env σ entryWin).getG 13 = _ from mapState_getG entryWin_gpr13]
    simp [mapVal, mapAddr, Lin.eval_sym, shift_ge3]
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr14, show (mapState env σ entryWin).getG 14 = _ from mapState_getG entryWin_gpr14]
    simp [mapVal, mapAddr, Lin.eval_sym, shift_ge3]
  · rw [cmpSt_getG env σ d r V M' entryWin_gpr15, show (mapState env σ entryWin).getG 15 = _ from mapState_getG entryWin_gpr15]
    simp [mapVal, mapAddr, Lin.eval_sym, shift_ge3]

/-- Registers of `T8` at the tail pc are carried by the certificate. -/
theorem tail_live (r : Nat) (hr : r ∈ Hashtree.Proofs.WinAvx512Live.T8) :
    r ∈ Hashtree.Proofs.WinAvx512Live.liveT.getD 8 [] :=
  Cert.tail Hashtree.Proofs.WinAvx512Live.cert tail8 rfl r hr

theorem L8_cases (r : Nat) (hr : r ∈ L8) :
    r ∈ Hashtree.Proofs.WinAvx512Live.T8 ∨ r ∈ [5, 6, 12, 13, 14, 15] := by
  rw [show L8 = [8, 4, 5, 6, 12, 13, 14, 15, 2, 1] from Hashtree.Proofs.WinAvx2X8Live.live_entry_eq] at hr
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
  simp only [Hashtree.Proofs.WinAvx512Live.T8, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  omega

/-- The linux final state's register `G w` for a windows register `w = F j`. -/
theorem ren_getG (f : CState) (j : Nat) (hF : F j < 16) (hG : G (F j) = j) :
    (renSt F G f).getG (F j) = f.getG j := Hashtree.Asm.X86.renSt_getG F G f j hF hG

theorem entryWin_vr_shape : entryWin.vr.length = 32 ∧ entryWin.vr.all (fun v => v.length == 16) = true := by
  decide +kernel

theorem vr_shape_of (K : State E Lin) (hK : K.vr.length = 32 ∧ K.vr.all (fun v => v.length == 16) = true)
    (e : Key → W32) (τ : Nat → Int) :
    (mapState e τ K).vr.length = 32 ∧ ∀ v ∈ (mapState e τ K).vr, v.length = 16 := by
  refine ⟨by simp [mapState, hK.1], fun v hv => ?_⟩
  simp only [mapState, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  have := (List.all_eq_true.mp hK.2) u hu
  simp only [beq_iff_eq] at this
  simp [this]

theorem KSpecC512_body (hT : TurnOut) (c : Nat) (inp : Nat → Spec.Byte)
    (hw : WfMemW Hashtree.Kernels.X86Win.Avx512X16.rodata [] env σ m0) (hc : σ 2 = c) (hsp : 24 ≤ σ 9)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    (W env σ m0 orcC c).err = none ∧
      ((c = 0 ∧ (W env σ m0 orcC c).tail = none ∧ PostLink σ c inp 0 (W env σ m0 orcC c)) ∨
       (c ≠ 0 ∧ (W env σ m0 orcC c).tail = some "hashtree_sha256_avx2_x8" ∧
         PreLink env σ c (c - c % 16) (c % 16) inp L8 (resume (W env σ m0 orcC c)))) := by
  rw [rodata_eq] at hw
  have hwL := wf_eL env σ m0 hw
  have h0 := h0_eL env σ m0 hw
  have hcL : σW σ 2 = (c : Int) := by rw [σW_ne σ 2 (by decide)]; exact hc
  have hspL : 24 ≤ σW σ 9 := by rw [σW_ne σ 9 (by decide)]; exact hsp
  have h10 : σW σ 10 = σW σ 1 := by rw [σW_10, σW_ne σ 1 (by decide)]
  have hA := agree_fin env σ m0 orcC hw c
  rcases Nat.eq_zero_or_pos c with hc0 | hpos
  · -- c = 0: the early `ret`
    subst hc0
    obtain ⟨e, hrun, hh, ht, herr⟩ := x16_zero_run m0 orcC (eL env σ m0) (σW σ) h0 (by simpa using hcL)
    have hfL : fL env σ m0 orcC 0 = mapState e (σW σ) KZ := by unfold fL; rw [steps_zero]; exact hrun
    have hfErr : (fL env σ m0 orcC 0).err = none := by rw [hfL, mapState_err']; exact Hashtree.Proofs.Avx512X16WEntry.KZ_err
    rw [ren_fin env σ m0 orcC 0 hfErr, hfL] at hA
    have hWerr : (W env σ m0 orcC 0).err = none := by rw [hA.err, renSt_err, mapState_err']; exact Hashtree.Proofs.Avx512X16WEntry.KZ_err
    have hWtail : (W env σ m0 orcC 0).tail = none := by rw [hA.tail, renSt_tail, mapState_tail']; exact Hashtree.Proofs.Avx512X16WEntry.KZ_tail
    have hWh : (W env σ m0 orcC 0).halted = true := by rw [hA.halted, renSt_halted, mapState_halted']; exact KZ_halted
    have hWmem : (W env σ m0 orcC 0).mem = [] := by
      rw [hA.mem, renSt_mem, mapState_mem', KZ_mem]; rfl
    have hWpc : (W env σ m0 orcC 0).pc = 3 := by rw [hA.pc, renSt_pc, mapState_pc', KZ_pc]
    refine ⟨hWerr, Or.inl ⟨rfl, hWtail, hWh, ?_, ?_, ?_⟩⟩
    · intro p hp; rw [hWmem] at hp; cases hp
    · intro n i b hn; exact absurd hn (Nat.not_lt_zero _)
    · have hlen := W_len env σ m0 orcC 0
      have hp : ∀ j, j ∈ [3, 5, 6, 7, 12, 13, 14, 15] → (W env σ m0 orcC 0).getG j = (mapState env σ entryWin).getG j :=
        fun j hj => W_preserve env σ m0 orcC 0 hWerr j hj
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [getElem?_of_getG _ 3 (by omega), hp 3 (by simp), show (mapState env σ entryWin).getG 3 = _ from mapState_getG entryWin_gpr3]
        simp [mapVal, mapAddr, Lin.eval_sym]
      · rw [getElem?_of_getG _ 5 (by omega), hp 5 (by simp), show (mapState env σ entryWin).getG 5 = _ from mapState_getG entryWin_gpr5]
        simp [mapVal, mapAddr, Lin.eval_sym]
      · rw [getElem?_of_getG _ 12 (by omega), hp 12 (by simp), show (mapState env σ entryWin).getG 12 = _ from mapState_getG entryWin_gpr12]
        simp [mapVal, mapAddr, Lin.eval_sym]
      · rw [getElem?_of_getG _ 13 (by omega), hp 13 (by simp), show (mapState env σ entryWin).getG 13 = _ from mapState_getG entryWin_gpr13]
        simp [mapVal, mapAddr, Lin.eval_sym]
      · rw [getElem?_of_getG _ 14 (by omega), hp 14 (by simp), show (mapState env σ entryWin).getG 14 = _ from mapState_getG entryWin_gpr14]
        simp [mapVal, mapAddr, Lin.eval_sym]
      · rw [getElem?_of_getG _ 15 (by omega), hp 15 (by simp), show (mapState env σ entryWin).getG 15 = _ from mapState_getG entryWin_gpr15]
        simp [mapVal, mapAddr, Lin.eval_sym]
      · rw [getElem?_of_getG _ 4 (by omega), hA.gpr 4 (by rw [hWpc]; exact live3)]
        have h4 := ren_getG (mapState e (σW σ) KZ) 4 (by decide) (by decide)
        rw [show F 4 = 4 from rfl] at h4
        rw [h4, mapState_getG KZ_gpr4]
        simp [mapVal, mapAddr, sAt_eval, σW]
        omega
  · rcases (show c < 16 ∨ 16 ≤ c by omega) with hlt | h16
    · -- 0 < c < 16: the immediate tail call
      obtain ⟨e, hrun, hh, ht, herr⟩ := x16_small_run m0 orcC (eL env σ m0) (σW σ) c h0 hcL hpos hlt
      have hfL : fL env σ m0 orcC c = mapState e (σW σ) KSm := by
        unfold fL; rw [steps_small (by omega) hlt]; exact hrun
      have hfErr : (fL env σ m0 orcC c).err = none := by rw [hfL, mapState_err']; exact Hashtree.Proofs.Avx512X16WEntry.KSm_err
      rw [ren_fin env σ m0 orcC c hfErr, hfL] at hA
      have hWerr : (W env σ m0 orcC c).err = none := by rw [hA.err, renSt_err, mapState_err']; exact Hashtree.Proofs.Avx512X16WEntry.KSm_err
      have hWtail : (W env σ m0 orcC c).tail = some "hashtree_sha256_avx2_x8" := by rw [hA.tail, renSt_tail, mapState_tail']; exact KSm_tail
      have hWmem : (W env σ m0 orcC c).mem = [] := by
        rw [hA.mem, renSt_mem, mapState_mem', KSm_mem']; rfl
      have hWpc : (W env σ m0 orcC c).pc = 8 := by rw [hA.pc, renSt_pc, mapState_pc', KSm_pc]
      have hd : c - c % 16 = 0 := by omega
      have hr : c % 16 = c := by omega
      refine ⟨hWerr, Or.inr ⟨by omega, hWtail, ?_⟩⟩
      rw [hd, hr]
      refine ⟨(W env σ m0 orcC c).vr, [], ?_, ?_, fun p hp => by simp at hp,
        fun p hp => by simp at hp, fun n i b hn => absurd hn (Nat.not_lt_zero _)⟩
      · rw [hA.vr, renSt_vr]; exact vr_shape_of KSm (by rw [KSm_vr]; exact entryW_vr_shape) e (σW σ)
      · show Agree L8 false (resume (W env σ m0 orcC c)) (cmpSt env σ 0 c (W env σ m0 orcC c).vr [])
        refine ⟨?_, ?_, rfl, (fun h => by cases h), ?_, rfl, rfl, rfl, ?_⟩
        · intro r hr
          show (W env σ m0 orcC c).getG r = _
          rcases L8_cases r hr with hT8 | hpres
          · rw [hA.gpr r (by rw [hWpc]; exact tail_live r hT8)]
            simp only [Hashtree.Proofs.WinAvx512Live.T8, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hT8
            rcases hT8 with rfl | rfl | rfl | rfl
            · have h := ren_getG (mapState e (σW σ) KSm) 2 (by decide) (by decide)
              rw [show F 2 = 8 from rfl] at h
              rw [h, mapState_getG KSm_gpr2, cmpSt_getG env σ 0 c _ _ entryWin_gpr8]
              simp [mapVal, mapAddr, Lin.eval_sym, σW, shift, hc]
            · have h := ren_getG (mapState e (σW σ) KSm) 4 (by decide) (by decide)
              rw [show F 4 = 4 from rfl] at h
              rw [h, mapState_getG KSm_gpr4, cmpSt_getG env σ 0 c _ _ entryWin_gpr4]
              simp [mapVal, mapAddr, sAt_eval, σW, shift]
            · have h := ren_getG (mapState e (σW σ) KSm) 6 (by decide) (by decide)
              rw [show F 6 = 2 from rfl] at h
              rw [h, mapState_getG KSm_gpr6, cmpSt_getG env σ 0 c _ _ entryWin_gpr2]
              simp [mapVal, mapAddr, Lin.eval_sym, σW, shift]
            · have h := ren_getG (mapState e (σW σ) KSm) 7 (by decide) (by decide)
              rw [show F 7 = 1 from rfl] at h
              rw [h, mapState_getG KSm_gpr7, cmpSt_getG env σ 0 c _ _ entryWin_gpr1]
              simp [mapVal, mapAddr, Lin.eval_sym, σW, shift]
          · exact preserved_cmp env σ m0 orcC c 0 c hWerr _ _ r hpres
        · show (W env σ m0 orcC c).gpr.length = _
          rw [W_len, cmpSt_len]
        · show (W env σ m0 orcC c).mem = ([] : CLog) ++ []
          rw [hWmem]; rfl
        · show (W env σ m0 orcC c).err = none
          exact hWerr
    · -- 16 ≤ c: the loop, then the tail call with the residual
      obtain ⟨e, M, hrun, hM, hσ'⟩ := x16_loop m0 orcC (eL env σ m0) (σW σ) c h0 hwL hspL h10 hcL h16
      have hinL : ∀ o : Nat, m0 ⟨rIn, σW σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0 := by
        intro o; rw [σW_ne σ 0 (by decide)]; exact hin o
      obtain ⟨hrange, hout⟩ := hT m0 orcC (eL env σ m0) (σW σ) c inp h0 hwL hspL h10 hcL h16 hinL
      have hfL : fL env σ m0 orcC c = fr M (mapState e (sIt (c / 16 - 1) (σW σ)) KTE) := by
        unfold fL; exact hrun
      have hfErr : (fL env σ m0 orcC c).err = none := by
        rw [hfL, fr_err', mapState_err']; exact Hashtree.Proofs.Avx512X16WEntry.KTE_err
      have hren := ren_fin env σ m0 orcC c hfErr
      rw [hren, hfL] at hA
      have hWerr : (W env σ m0 orcC c).err = none := by
        rw [hA.err, renSt_err, fr_err', mapState_err']; exact Hashtree.Proofs.Avx512X16WEntry.KTE_err
      have hWtail : (W env σ m0 orcC c).tail = some "hashtree_sha256_avx2_x8" := by
        rw [hA.tail, renSt_tail, fr_tail', mapState_tail']; exact KTE_tail
      have hWpc : (W env σ m0 orcC c).pc = 8 := by rw [hA.pc, renSt_pc, fr_pc', mapState_pc', KTE_pc]
      have hWmem : (W env σ m0 orcC c).mem = (fL env σ m0 orcC c).mem := by
        rw [hA.mem, renSt_mem, hfL]
      have hfmem : (fL env σ m0 orcC c).mem = (KTE.mem.map (fun p => (mapAddr (sIt (c / 16 - 1) (σW σ)) p.1,
          mapCell e (sIt (c / 16 - 1) (σW σ)) p.2))) ++ M := by rw [hfL, fr_mem', mapState_mem']
      -- the symbols after the turns
      have hj : c / 16 - 1 + 1 = c / 16 := by omega
      have hs0 : sIt (c / 16 - 1) (σW σ) 0 = σ 0 + 1024 * ((c / 16 - 1 : Nat) : Int) := by
        rw [sIt_0, σW_ne σ 0 (by decide)]
      have hs1 : sIt (c / 16 - 1) (σW σ) 1 = σ 1 + 512 * ((c / 16 - 1 : Nat) : Int) := by
        rw [sIt_1, σW_ne σ 1 (by decide)]
      have hs2 : sIt (c / 16 - 1) (σW σ) 2 = (c : Int) - 16 * ((c / 16 - 1 : Nat) : Int) := by
        rw [sIt_count, hcL]
      have hs9 : sIt (c / 16 - 1) (σW σ) 9 = σ 9 := by rw [sIt_9, σW_ne σ 9 (by decide)]
      refine ⟨hWerr, Or.inr ⟨by omega, hWtail, ?_⟩⟩
      refine ⟨(W env σ m0 orcC c).vr, (W env σ m0 orcC c).mem, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hA.vr, renSt_vr, fr_vr']; exact vr_shape_of KTE KTE_vr_shape e _
      · show Agree L8 false (resume (W env σ m0 orcC c)) (cmpSt env σ (c - c % 16) (c % 16) (W env σ m0 orcC c).vr (W env σ m0 orcC c).mem)
        refine ⟨?_, ?_, rfl, (fun h => by cases h), ?_, rfl, rfl, rfl, ?_⟩
        · intro r hr
          show (W env σ m0 orcC c).getG r = _
          rcases L8_cases r hr with hT8 | hpres
          · rw [hA.gpr r (by rw [hWpc]; exact tail_live r hT8)]
            simp only [Hashtree.Proofs.WinAvx512Live.T8, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hT8
            rcases hT8 with rfl | rfl | rfl | rfl
            · have h := ren_getG (mapState e (sIt (c / 16 - 1) (σW σ)) KTE) 2 (by decide) (by decide)
              rw [show F 2 = 8 from rfl] at h
              rw [renSt_fr_getG, h, mapState_getG KTE_gpr2, cmpSt_getG env σ _ _ _ _ entryWin_gpr8]
              have e1 : Lin.eval (sIt (c / 16 - 1) (σW σ)) ⟨-16, [0, 0, 1]⟩ = ((c % 16 : Nat) : Int) := by
                simp only [Lin.eval, dotC, Int.zero_mul, Int.one_mul, Int.add_zero, Int.zero_add, hs2]
                omega
              have e2 : Lin.eval (shift σ (c - c % 16) (c % 16)) (Lin.sym 2) = ((c % 16 : Nat) : Int) := by
                rw [Lin.eval_sym]; simp [shift]
              simp only [mapVal, mapAddr, e1, e2]
            · have h := ren_getG (mapState e (sIt (c / 16 - 1) (σW σ)) KTE) 4 (by decide) (by decide)
              rw [show F 4 = 4 from rfl] at h
              rw [renSt_fr_getG, h, mapState_getG KTE_gpr4, cmpSt_getG env σ _ _ _ _ entryWin_gpr4]
              simp only [mapVal, mapAddr, sAt_eval, shift, hs9]
              simp [shift_ge3]
            · have h := ren_getG (mapState e (sIt (c / 16 - 1) (σW σ)) KTE) 6 (by decide) (by decide)
              rw [show F 6 = 2 from rfl] at h
              rw [renSt_fr_getG, h, mapState_getG KTE_gpr6, cmpSt_getG env σ _ _ _ _ entryWin_gpr2]
              have e1 : Lin.eval (sIt (c / 16 - 1) (σW σ)) ⟨1024, [1]⟩ = σ 0 + 64 * ((c - c % 16 : Nat) : Int) := by
                simp only [Lin.eval, dotC, Int.zero_mul, Int.one_mul, Int.add_zero, Int.zero_add, hs0]
                omega
              have e2 : Lin.eval (shift σ (c - c % 16) (c % 16)) (Lin.sym 0) = σ 0 + 64 * ((c - c % 16 : Nat) : Int) := by
                rw [Lin.eval_sym]; simp [shift]
              simp only [mapVal, mapAddr, e1, e2]
            · have h := ren_getG (mapState e (sIt (c / 16 - 1) (σW σ)) KTE) 7 (by decide) (by decide)
              rw [show F 7 = 1 from rfl] at h
              rw [renSt_fr_getG, h, mapState_getG KTE_gpr7, cmpSt_getG env σ _ _ _ _ entryWin_gpr1]
              have e1 : Lin.eval (sIt (c / 16 - 1) (σW σ)) ⟨512, [0, 1]⟩ = σ 1 + 32 * ((c - c % 16 : Nat) : Int) := by
                simp only [Lin.eval, dotC, Int.zero_mul, Int.one_mul, Int.add_zero, Int.zero_add, hs1]
                omega
              have e2 : Lin.eval (shift σ (c - c % 16) (c % 16)) (Lin.sym 1) = σ 1 + 32 * ((c - c % 16 : Nat) : Int) := by
                rw [Lin.eval_sym]; simp [shift]
              simp only [mapVal, mapAddr, e1, e2]
          · exact preserved_cmp env σ m0 orcC c _ _ hWerr _ _ r hpres
        · show (W env σ m0 orcC c).gpr.length = _
          rw [W_len, cmpSt_len]
        · show (W env σ m0 orcC c).mem = ([] : CLog) ++ (W env σ m0 orcC c).mem
          rfl
        · show (W env σ m0 orcC c).err = none
          exact hWerr
      · -- OutLogW
        intro p hp
        rw [hWmem, hfmem, List.mem_append] at hp
        rcases hp with hp | hp
        · simp only [List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          have := (List.all_eq_true.mp KTE_mem_out) q hq
          simp only [beq_iff_eq] at this
          exact Or.inl (by simp [mapAddr, this])
        · rcases hM p hp with h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, by omega⟩
      · -- Foot
        intro p hp
        rw [hWmem] at hp
        have := hrange p hp
        rw [σW_ne σ 1 (by decide)] at this
        exact Or.inl ⟨this.1, this.2.1, by have := this.2.2; omega⟩
      · -- OutOk
        rw [hWmem]
        rw [σW_ne σ 1 (by decide)] at hout
        exact hout

/-- **The avx512_x16 link**, from R2b's loop certificate and the output-byte hypothesis `TurnOut`
(R2c): `KSpecC512` with the step function `Avx512X16WLoop.steps`. -/
theorem KSpecC512_of_turnOut (hT : TurnOut) (c : Nat) (inp : Nat → Spec.Byte) :
    KSpecC512 steps env σ m0 orcC c inp := by
  intro hw _ hc hsp hin s hs
  subst hs
  exact KSpecC512_body env σ m0 orcC hT c inp hw hc hsp hin

end Final

end Hashtree.Proofs.WinAvx512Link
