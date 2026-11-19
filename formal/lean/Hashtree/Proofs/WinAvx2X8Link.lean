import Hashtree.Proofs.WinAvx2X8LinkFacts
import Hashtree.Proofs.WinAvx2X8LinkVrE8
import Hashtree.Proofs.WinAvx2X8LinkVrS8
import Hashtree.Proofs.WinAvx2X8LinkVrE24
import Hashtree.Proofs.WinAvx2X8LinkVrS24
import Hashtree.Proofs.WinAvxX4Cert

/-!
# R5: the windows avx2_x8 link `KSpecC8`, given R2c's output contracts

`KSpecC8_of_turnOut8W : TurnOut8W → TurnOut8WLast → KSpecC8 s8 …`: from the wrapper call state the
windows avx2_x8 stream, after `s8 c` instructions,
* `c = 0`: returns after four instructions (`x8_zero_run`, nothing written, depth 0);
* `0 < c < 8`: takes the small path (`WinAvx2X8WSmall.x8w_small_run`, 42 instructions) to the tail
  call into avx_x4 with the call registers and the 368 saved bytes in its frame;
* `8 ≤ c < 16`: one pass (`WinAvx2X8WAll.x8w_runW_last_abi`) to the exit cut `KTE r`;
* `c ≥ 16`: `c / 8 - 1` passes (`x8w_runW_abi`, `j = c / 8 - 2`, `s = c % 8 + 8`) to `KTEs r`;
and hands avx_x4 `c - c % 8` finished blocks and `c % 8` remaining (`PreLink … D8 L4`).  The
registers come from the exit cuts (`exitGprW`: the call registers with `rcx`, `rdx`, `r8`
advanced; `rbp`/`rsi` popped, `r12..r15` restored), the log facts from `TurnOut8W*` on the empty
caller log, the vector-file shapes from one kernel evaluation per cut.

`KSpecC8U` is the same obligation with the hand-off on the larger register set `U` (everything
but the volatile `rax`, `r9..r11`) under the exit cut's own environment — the form the chain
composition (`WinChainAll`) consumes: the avx_x4 and avx_x1 links read the Win64 callee-saved
registers (their returns restore them; avx_x1 pushes `rsi`/`rdi`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvx2X8Link

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.RunAgree
open Hashtree.Proofs.X86Chain (resume)
open Hashtree.Proofs.WinChain (p8)
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.WinAvx512Bridge (shift PostLink PreLink)
open Hashtree.Proofs.WinAvx2X8Bridge (KSpecC8 L4 D8)
open Hashtree.Proofs.WinAvx2X8WOut (TurnOut8W TurnOut8WLast x8wRunSteps x8wLastSteps)
open Hashtree.Proofs.ShaniW (OutLogW fr_nil)
open Hashtree.Proofs.WinShaniSeedAlign (mapState_getG)
open Hashtree.Proofs.WinShaniBridge (entryWin_gpr1 entryWin_gpr2 entryWin_gpr3 entryWin_gpr4 entryWin_gpr5
  entryWin_gpr8 entryWin_gpr12 entryWin_gpr13 entryWin_gpr14 entryWin_gpr15)
open Hashtree.Proofs.WrapperAmd64 (sAt_eval)
open Hashtree.Proofs.WinAvxX4Link (cmpSt cmpSt_len)
open Hashtree.Proofs.WinAvxX4Cert (vrOk vrOk_sound ms_err ms_tail fr_vr)
open Hashtree.Proofs.WinAvx2X8W (exitGprW KTE)
open Hashtree.Proofs.WinAvx2X8WStrip (KTEs)
open Hashtree.Proofs.WinAvx2X8WSmall (x8Sm)
open Hashtree.Proofs.WinAvx2X8WLoop (sIt8)

/-- The step function: early return, small path, one pass, or `c / 8 - 1` passes. -/
def s8 (c : Nat) : Nat :=
  if c = 0 then 4 else if c < 8 then 42 else if c < 16 then x8wLastSteps else x8wRunSteps (c / 8 - 2)

/-- The general registers a link hands over: all but the volatile `rax`, `r9`, `r10`, `r11`. -/
def U : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 14, 15]

/-! ## The hand-off from exit facts -/

theorem preLink_mk (env : Key → W32) (σ : Nat → Int) (c d r : Nat) (inp : Nat → Spec.Byte) (D : Nat)
    (L : List Nat) (f : CState) (hlen : f.gpr.length = 16)
    (hg : ∀ j, j ∈ L → f.getG j = (mapState env (shift σ d r) entryWin).getG j)
    (hV : f.vr.length = 32 ∧ ∀ v ∈ f.vr, v.length = 16)
    (hlog : OutLogW (σ 9) f.mem) (hfoot : Foot (σ 9) D (σ 1) (32 * c) f.mem)
    (hout : OutOk inp (σ 1) d f.mem) (herr : f.err = none) :
    PreLink env σ c d r inp D L (resume f) := by
  refine ⟨f.vr, f.mem, hV, ?_, hlog, hfoot, hout⟩
  show Agree L false (resume f) (cmpSt env σ d r f.vr f.mem)
  refine ⟨fun j hj => ?_, ?_, rfl, (fun h => by cases h), ?_, rfl, rfl, rfl, ?_⟩
  · show f.getG j = _
    rw [hg j hj]; rfl
  · show f.gpr.length = _
    rw [hlen, cmpSt_len]
  · show f.mem = ([] : CLog) ++ f.mem
    rfl
  · show f.err = none
    exact herr

/-- The registers of a loop exit cut (`gpr = exitGprW`) against the advanced call state. -/
theorem agree_exit (e : Key → W32) (τ σ : Nat → Int) (d r : Nat) (K : State E Lin) (hK : K.gpr = exitGprW)
    (M : CLog) (h1 : τ 1 + 256 = σ 1 + 32 * (d : Int)) (h0 : τ 0 + 512 = σ 0 + 64 * (d : Int))
    (h2 : τ 2 - 8 = (r : Int)) (hhi : ∀ i, 3 ≤ i → τ i = σ i) :
    ∀ j, j ∈ U → (fr M (mapState e τ K)).getG j = (mapState e (shift σ d r) entryWin).getG j := by
  have g : ∀ j v, exitGprW[j]? = some v → (fr M (mapState e τ K)).getG j = mapVal e τ v := by
    intro j v h
    show (mapState e τ K).getG j = _
    exact mapState_getG (by rw [hK]; exact h)
  have t5 := hhi 5 (by omega)
  have t6 := hhi 6 (by omega)
  have t7 := hhi 7 (by omega)
  have t8 := hhi 8 (by omega)
  have t9 := hhi 9 (by omega)
  have t11 := hhi 11 (by omega)
  have t12 := hhi 12 (by omega)
  intro j hj
  simp only [U, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [g 1 _ eg1, mapState_getG entryWin_gpr1]; simp only [mapVal, mapAddr, Lin.eval_sym]
    simp [Lin.eval, dotC, shift]; omega
  · rw [g 2 _ eg2, mapState_getG entryWin_gpr2]; simp only [mapVal, mapAddr, Lin.eval_sym]
    simp [Lin.eval, dotC, shift]; omega
  · rw [g 3 _ eg3, mapState_getG entryWin_gpr3]; simp [mapVal, mapAddr, Lin.eval_sym, shift, t5]
  · rw [g 4 _ eg4, mapState_getG entryWin_gpr4]; simp [mapVal, mapAddr, sAt_eval, shift, t9]
  · rw [g 5 _ eg5, mapState_getG entryWin_gpr5]; simp [mapVal, mapAddr, Lin.eval_sym, shift, t6]
  · rw [g 6 _ eg6, mapState_getG ew6]; rfl
  · rw [g 7 _ eg7, mapState_getG ew7]; rfl
  · rw [g 8 _ eg8, mapState_getG entryWin_gpr8]; simp only [mapVal, mapAddr, Lin.eval_sym]
    simp [Lin.eval, dotC, shift]; omega
  · rw [g 12 _ eg12, mapState_getG entryWin_gpr12]; simp [mapVal, mapAddr, Lin.eval_sym, shift, t7]
  · rw [g 13 _ eg13, mapState_getG entryWin_gpr13]; simp [mapVal, mapAddr, Lin.eval_sym, shift, t11]
  · rw [g 14 _ eg14, mapState_getG entryWin_gpr14]; simp [mapVal, mapAddr, Lin.eval_sym, shift, t8]
  · rw [g 15 _ eg15, mapState_getG entryWin_gpr15]; simp [mapVal, mapAddr, Lin.eval_sym, shift, t12]

theorem shift_zero (σ : Nat → Int) (c : Nat) (hc : σ 2 = c) : shift σ 0 c = σ := by
  funext i
  simp only [shift]
  by_cases h0 : i = 0
  · subst h0; simp
  by_cases h1 : i = 1
  · subst h1; simp
  by_cases h2 : i = 2
  · subst h2; simp [hc]
  simp [h0, h1, h2]

theorem mapState_getG_congr (e : Key → W32) (τ : Nat → Int) {K K' : State E Lin} (h : K.gpr = K'.gpr)
    (j : Nat) : (mapState e τ K).getG j = (mapState e τ K').getG j := by
  simp only [State.getG, mapState, h]

/-- The registers of the small-path cut (`gpr = entryWin.gpr`) against the call state. -/
theorem agree_small (e : Key → W32) (σ : Nat → Int) (c : Nat) (hc : σ 2 = c) (K : State E Lin)
    (hK : K.gpr = entryWin.gpr) (M : CLog) :
    ∀ j, j ∈ U → (fr M (mapState e σ K)).getG j = (mapState e (shift σ 0 c) entryWin).getG j := by
  intro j _
  rw [shift_zero σ c hc]
  exact mapState_getG_congr e σ hK j

/-! ## Log facts from the output contracts -/

theorem D8_eq : ((D8 : Nat) : Int) = 1296 := rfl
theorem D8W_eq : ((Hashtree.Proofs.WinAvx2X8WOut.D8 : Nat) : Int) = 1296 := rfl

theorem log_facts8 (σ : Nat → Int) (c : Nat) (L : CLog) (nb : Nat) (hc : nb ≤ c)
    (hL : ∀ p ∈ L, p ∈ ([] : CLog) ∨ (p.1.region = rOut ∧ σ 1 ≤ p.1.off ∧ p.1.off < σ 1 + 32 * (nb : Int)) ∨
      (p.1.region = rStack ∧ σ 9 - 1296 ≤ p.1.off ∧ p.1.off < σ 9)) :
    OutLogW (σ 9) L ∧ Foot (σ 9) D8 (σ 1) (32 * c) L := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rcases hL p hp with h | ⟨h, _⟩ | ⟨h, _, h'⟩
    · cases h
    · exact Or.inl h
    · exact Or.inr ⟨h, h'⟩
  · rcases hL p hp with h | ⟨h, a, b⟩ | ⟨h, a, b⟩
    · cases h
    · left; refine ⟨h, a, ?_⟩; push_cast; omega
    · right; refine ⟨h, ?_, b⟩; rw [D8_eq]; exact a

/-! ## The exit facts -/

theorem KTE_ok (r : Nat) (hr : r = 8 ∨ r = 24) :
    (KTE r).err = none ∧ (KTE r).tail = some "hashtree_sha256_avx_x4" ∧ (KTE r).gpr = exitGprW ∧
      vrOk (KTE r) = true := by
  rcases hr with rfl | rfl
  · obtain ⟨_, _, _, _, _, _, t7, t8, _, _, _, t12, _, _⟩ :=
      Hashtree.Proofs.WinAvx2X8W.shiftFacts 8 Hashtree.Proofs.WinAvx2X8W.shiftOk_8
    exact ⟨t8, t7, t12, KTE_vr_8⟩
  · obtain ⟨_, _, _, _, _, _, t7, t8, _, _, _, t12, _, _⟩ :=
      Hashtree.Proofs.WinAvx2X8W.shiftFacts 24 Hashtree.Proofs.WinAvx2X8W.shiftOk_24
    exact ⟨t8, t7, t12, KTE_vr_24⟩

theorem KTEs_ok (r : Nat) (hr : r = 8 ∨ r = 24) :
    (KTEs r).err = none ∧ (KTEs r).tail = some "hashtree_sha256_avx_x4" ∧ (KTEs r).gpr = exitGprW ∧
      vrOk (KTEs r) = true := by
  rcases hr with rfl | rfl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, s12, s13, _, _, _, _, s18, _, _, _⟩ :=
      Hashtree.Proofs.WinAvx2X8WStrip.stripFacts 8 Hashtree.Proofs.WinAvx2X8WStrip.stripOk_8
    exact ⟨s13, s12, s18, KTEs_vr_8⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, s12, s13, _, _, _, _, s18, _, _, _⟩ :=
      Hashtree.Proofs.WinAvx2X8WStrip.stripFacts 24 Hashtree.Proofs.WinAvx2X8WStrip.stripOk_24
    exact ⟨s13, s12, s18, KTEs_vr_24⟩

section Spec
variable (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
  (c : Nat) (inp : Nat → Spec.Byte)

theorem len8 (n : Nat) : (run p8 4 m0 orcC n (mapState env σ entryWin)).gpr.length = 16 :=
  Hashtree.Proofs.WinShaniCall.run_gpr_len p8 n _ (Hashtree.Proofs.WinShaniBridge.stW_len env σ)

/-- **The tail exit of the windows avx2_x8 stream** (`c ≠ 0`): no error, the tail call into
avx_x4, the registers `U` of the call state advanced by `c - c % 8` blocks (under the exit
cut's environment `e'`), a 32 x 16 vector file, and the log facts. -/
theorem exit8 (hT : TurnOut8W) (hTL : TurnOut8WLast)
    (hw : WfMemW rodata8 [] env σ m0) (hc : σ 2 = c) (hc0 : c ≠ 0) (habi : σ 9 % 16 = 8)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let f := run p8 4 m0 orcC (s8 c) (mapState env σ entryWin)
    f.err = none ∧ f.tail = some "hashtree_sha256_avx_x4" ∧ f.gpr.length = 16 ∧
    (f.vr.length = 32 ∧ ∀ v ∈ f.vr, v.length = 16) ∧
    OutLogW (σ 9) f.mem ∧ Foot (σ 9) D8 (σ 1) (32 * c) f.mem ∧ OutOk inp (σ 1) (c - c % 8) f.mem ∧
    ∃ e' : Key → W32, ∀ j, j ∈ U → f.getG j = (mapState e' (shift σ (c - c % 8) (c % 8)) entryWin).getG j := by
  intro f
  have hlen := len8 env σ m0 orcC (s8 c)
  have hM : Hashtree.Proofs.WinLogW.OutLogW σ [] := fun p hp => by cases hp
  by_cases h8 : c < 8
  · -- the small path
    have hst : s8 c = 42 := by simp [s8, hc0, h8]
    have hr : ∃ r : Nat, (r : Int) = (σ 9 - 16) % 32 ∧ (r = 8 ∨ r = 24) := by
      rcases Hashtree.Proofs.WinAvx2X8WAll.residue_cases σ habi with h | h
      · exact ⟨8, h, Or.inl rfl⟩
      · exact ⟨24, h, Or.inr rfl⟩
    obtain ⟨r, hr, habi'⟩ := hr
    obtain ⟨e', hrun, _⟩ := Hashtree.Proofs.WinAvx2X8WSmall.x8w_small_run env σ m0 orcC [] hw hM
      (by omega) (by omega) r hr habi'
    rw [fr_nil, fr_nil] at hrun
    have hf : f = mapState e' σ (x8Sm r) :=
      (congrArg (fun n => run p8 4 m0 orcC n (mapState env σ entryWin)) hst).trans hrun
    obtain ⟨_, htail, herr, _, _, hgpr, _, _⟩ :=
      Hashtree.Proofs.WinAvx2X8WSmall.smFacts r (Hashtree.Proofs.WinAvx2X8WSmall.smOk_abi r habi')
    obtain ⟨hvr, hstk⟩ := x8Sm_abi r habi'
    have hs := stackLogD_sound 1296 e' σ (x8Sm r) hstk
    have hcm : c % 8 = c := Nat.mod_eq_of_lt h8
    have hcd : c - c % 8 = 0 := by omega
    refine ⟨(congrArg State.err hf).trans ((ms_err _ σ _).trans herr),
      (congrArg State.tail hf).trans ((ms_tail _ σ _).trans htail), hlen,
      by rw [hf]; exact vrOk_sound e' σ _ hvr, ?_, ?_, ?_, ⟨e', ?_⟩⟩
    · intro p hp; rw [hf] at hp; exact Or.inr ⟨(hs p hp).1, (hs p hp).2.2⟩
    · intro p hp; rw [hf] at hp; right; refine ⟨(hs p hp).1, ?_, (hs p hp).2.2⟩
      rw [D8_eq]; exact (hs p hp).2.1
    · rw [hcd]; intro n _ _ hn; omega
    · intro j hj
      rw [hcd, hcm, hf, ← fr_nil (mapState e' σ (x8Sm r))]
      exact agree_small e' σ c hc (x8Sm r) hgpr [] j hj
  by_cases h16 : c < 16
  · -- one pass
    have hst : s8 c = x8wLastSteps := by simp [s8, hc0, h8, h16]
    have hstN : s8 c = 24 + (Hashtree.Proofs.WinAvx2X8W.BODYLEN + 42) := hst.trans rfl
    obtain ⟨r, e', habi', hrun, _⟩ := Hashtree.Proofs.WinAvx2X8WAll.x8w_runW_last_abi env σ m0 orcC [] hw hM
      (by omega) (by omega) habi
    rw [fr_nil, fr_nil] at hrun
    have hf : f = mapState e' σ (KTE r) :=
      (congrArg (fun n => run p8 4 m0 orcC n (mapState env σ entryWin)) hstN).trans hrun
    obtain ⟨herr, htail, hgpr, hvr⟩ := KTE_ok r habi'
    obtain ⟨hTf, hTo⟩ := hTL env σ m0 orcC [] inp hw hM (by omega) (by omega) habi hin
    rw [fr_nil] at hTf hTo
    have hcm : c % 8 = c - 8 := by omega
    have hcd : c - c % 8 = 8 := by omega
    have hLf := log_facts8 σ c f.mem 8 (by omega) (by
      intro p hp
      rcases hTf p (by rw [← hst]; exact hp) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h.1, h.2.1, by have := h.2.2; push_cast; omega⟩)
      · exact Or.inr (Or.inr ⟨h.1, by have := h.2.1; rw [D8W_eq] at this; exact this, h.2.2⟩))
    refine ⟨(congrArg State.err hf).trans ((ms_err _ _ _).trans herr),
      (congrArg State.tail hf).trans ((ms_tail _ _ _).trans htail), hlen,
      by rw [hf]; exact vrOk_sound e' σ _ hvr, hLf.1, hLf.2, ?_, ⟨e', ?_⟩⟩
    · rw [hcd]; show OutOk inp (σ 1) 8 (run p8 4 m0 orcC (s8 c) _).mem; rw [hst]; exact hTo
    · intro j hj
      rw [hf, ← fr_nil (mapState e' σ (KTE r))]
      exact agree_exit e' σ σ (c - c % 8) (c % 8) (KTE r) hgpr []
        (by rw [hcd]; push_cast; omega) (by rw [hcd]; push_cast; omega)
        (by rw [hcm, hc]; push_cast [show 8 ≤ c by omega]; omega) (fun _ _ => rfl) j hj
  · -- several passes
    have hj : σ 2 = 8 * (((c / 8 - 2 : Nat) : Int) + 1) + ((c % 8 + 8 : Nat) : Int) := by
      rw [hc]; push_cast [show 2 ≤ c / 8 by omega]; omega
    have hst : s8 c = x8wRunSteps (c / 8 - 2) := by simp [s8, hc0, h8, h16]
    have hstN : s8 c = 24 + (Hashtree.Proofs.WinAvx2X8WLoop.TURNLEN + ((c / 8 - 2) *
        Hashtree.Proofs.WinAvx2X8WLoop.TURNLEN + (Hashtree.Proofs.WinAvx2X8W.BODYLEN + 42))) := hst.trans rfl
    obtain ⟨r, e', M', habi', hrun, _⟩ := Hashtree.Proofs.WinAvx2X8WAll.x8w_runW_abi env σ m0 orcC [] hw hM
      (c / 8 - 2) (c % 8 + 8) (by omega) (by omega) hj habi
    rw [fr_nil] at hrun
    have hf : f = fr M' (mapState e' (sIt8 (c / 8 - 2 + 1) σ) (KTEs r)) :=
      (congrArg (fun n => run p8 4 m0 orcC n (mapState env σ entryWin)) hstN).trans hrun
    obtain ⟨herr, htail, hgpr, hvr⟩ := KTEs_ok r habi'
    obtain ⟨hTf, hTo⟩ := hT env σ m0 orcC [] (c / 8 - 2) (c % 8 + 8) inp hw hM (by omega) (by omega) hj habi hin
    rw [fr_nil] at hTf hTo
    have hcd : c - c % 8 = 8 * (c / 8 - 2 + 2) := by omega
    have hLf := log_facts8 σ c f.mem (8 * (c / 8 - 2 + 2)) (by omega) (by
      intro p hp
      rcases hTf p (by rw [← hst]; exact hp) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h.1, h.2.1, by
          have := h.2.2; push_cast [show 2 ≤ c / 8 by omega] at this ⊢; omega⟩)
      · exact Or.inr (Or.inr ⟨h.1, by have := h.2.1; rw [D8W_eq] at this; exact this, h.2.2⟩))
    have t1 := Hashtree.Proofs.WinAvx2X8WLoop.sIt8_out (c / 8 - 2 + 1) σ
    have t0 := Hashtree.Proofs.WinAvx2X8WLoop.sIt8_in (c / 8 - 2 + 1) σ
    have t2 := Hashtree.Proofs.WinAvx2X8WLoop.sIt8_count (c / 8 - 2 + 1) σ
    refine ⟨(congrArg State.err hf).trans ((fr_err _ _).trans ((ms_err _ _ _).trans herr)),
      (congrArg State.tail hf).trans ((fr_tail _ _).trans ((ms_tail _ _ _).trans htail)), hlen,
      by rw [hf, fr_vr]; exact vrOk_sound _ _ _ hvr, hLf.1, hLf.2, ?_, ⟨e', ?_⟩⟩
    · rw [hcd]; show OutOk inp (σ 1) _ (run p8 4 m0 orcC (s8 c) _).mem; rw [hst]; exact hTo
    · intro i hi
      rw [hf]
      exact agree_exit e' (sIt8 (c / 8 - 2 + 1) σ) σ (c - c % 8) (c % 8) (KTEs r) hgpr M'
        (by rw [t1, hcd]; push_cast [show 2 ≤ c / 8 by omega]; omega)
        (by rw [t0, hcd]; push_cast [show 2 ≤ c / 8 by omega]; omega)
        (by rw [t2, hc]; push_cast [show 2 ≤ c / 8 by omega]; omega)
        (fun i hi => Hashtree.Proofs.WinAvx2X8WLoop.sIt8_hi i hi _ σ) i hi

end Spec

/-! ## The link -/

theorem L4_mem (j : Nat) (hj : j ∈ L4) : j ∈ [8, 4, 2, 1] := by
  rw [show L4 = [8, 4, 2, 1] from Hashtree.Proofs.WinAvxX4Live.live_entry_eq] at hj; exact hj

theorem L4_U (j : Nat) (h : j ∈ [8, 4, 2, 1]) : j ∈ U := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- The pointer registers of the call state do not depend on the environment. -/
theorem ptr_env (e e' : Key → W32) (τ : Nat → Int) (j : Nat) (hj : j ∈ [8, 4, 2, 1]) :
    (mapState e τ entryWin).getG j = (mapState e' τ entryWin).getG j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl
  · rw [mapState_getG entryWin_gpr8, mapState_getG entryWin_gpr8]; rfl
  · rw [mapState_getG entryWin_gpr4, mapState_getG entryWin_gpr4]; rfl
  · rw [mapState_getG entryWin_gpr2, mapState_getG entryWin_gpr2]; rfl
  · rw [mapState_getG entryWin_gpr1, mapState_getG entryWin_gpr1]; rfl

/-- **The avx2_x8 link `KSpecC8`**, given R2c's output contracts of the windows avx2_x8 loop. -/
theorem KSpecC8_of_turnOut8W (hT : TurnOut8W) (hTL : TurnOut8WLast) (env : Key → W32) (σ : Nat → Int)
    (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte) :
    KSpecC8 s8 env σ m0 orcC c inp := by
  intro hw he hc habi hin s hs
  subst hs
  by_cases hc0 : c = 0
  · subst hc0
    have h4 : s8 0 = 4 := rfl
    rw [h4, x8_zero_run env σ m0 orcC hw he hc]
    exact ⟨by rw [ms_err, KZ8_err], Or.inl ⟨rfl, by rw [ms_tail, KZ8_tail], postLink_zero8 env σ inp⟩⟩
  · obtain ⟨herr, htail, hlen, hV, hlog, hfoot, hout, e', hg⟩ := exit8 env σ m0 orcC c inp hT hTL hw hc hc0 habi hin
    refine ⟨herr, Or.inr ⟨hc0, htail, preLink_mk env σ c _ _ inp D8 L4 _ hlen (fun j hj => ?_) hV hlog hfoot hout herr⟩⟩
    have hj' := L4_mem j hj
    rw [hg j (L4_U j hj')]
    exact ptr_env e' env _ j hj'

/-- The avx2_x8 obligation with the hand-off on `U` under the exit environment (for the chain). -/
def KSpecC8U (s8 : Nat → Nat) (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int)
    (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte) : Prop :=
  WfMemW rodata8 [] env σ m0 → EnvMem env σ m0 → σ 2 = c → σ 9 % 16 = 8 →
  (∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    let f := run p8 4 m0 orcC (s8 c) (mapState env σ entryWin)
    f.err = none ∧
      ((c = 0 ∧ f.tail = none ∧ PostLink σ c inp 0 f) ∨
       (c ≠ 0 ∧ f.tail = some "hashtree_sha256_avx_x4" ∧
         ∃ e' : Key → W32, PreLink e' σ c (c - c % 8) (c % 8) inp D8 U (resume f)))

theorem KSpecC8U_of_turnOut8W (hT : TurnOut8W) (hTL : TurnOut8WLast) (env : Key → W32) (σ : Nat → Int)
    (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (c : Nat) (inp : Nat → Spec.Byte) :
    KSpecC8U s8 env σ m0 orcC c inp := by
  intro hw he hc habi hin
  by_cases hc0 : c = 0
  · subst hc0
    have h4 : s8 0 = 4 := rfl
    show (run p8 4 m0 orcC (s8 0) (mapState env σ entryWin)).err = none ∧ _
    rw [h4, x8_zero_run env σ m0 orcC hw he hc]
    exact ⟨by rw [ms_err, KZ8_err], Or.inl ⟨rfl, by rw [ms_tail, KZ8_tail], postLink_zero8 env σ inp⟩⟩
  · obtain ⟨herr, htail, hlen, hV, hlog, hfoot, hout, e', hg⟩ := exit8 env σ m0 orcC c inp hT hTL hw hc hc0 habi hin
    exact ⟨herr, Or.inr ⟨hc0, htail, e', preLink_mk e' σ c _ _ inp D8 U _ hlen hg hV hlog hfoot hout herr⟩⟩

end Hashtree.Proofs.WinAvx2X8Link
