import Hashtree.Proofs.WinAvx2X8Link
import Hashtree.Proofs.WinLinkLift
import Hashtree.Proofs.WinAvx512Final
import Hashtree.Proofs.WinAvxX1Link

/-!
# R5: the windows tail chain `avx512_x16 -> avx2_x8 -> avx_x4 -> avx_x1`, per-link clauses

The four per-link clauses of the windows tail chain (`clause512`, `clause8`, `clause4`,
`clause1`), each at rodata region 4, conditional only on R2c's output contracts of the two windows
W-mode loops (`TurnOut8W`/`TurnOut8WLast` for avx2_x8, `TurnOut4W`/`TurnOut4WLast` for avx_x4); the
avx512_x16 link is unconditional (`WinAvx512Final`), the avx_x1 link is `WinAvxX1Link.last1`.

The assembled chain is NOT stated here.  An earlier version composed the four clauses with every
table in region 4 (`win_KSpecC`/`win_chain_correct`, removed): their four memory hypotheses fix
region 4 to four different tables and cannot hold together, so that theorem was vacuous.  The
chain theorem is `WinChainRegions.win_chain_correct_regions` (one region per table), and the
wrapper-level statement on the shipped layout is `WinWrapperChain.wrapper_avx512_chain` /
`wrapper_avx2_chain` (non-vacuity: `WinWrapperChain.withTables_ok`).

The pre-condition of each later link is the hand-over `PreLink` on the register set `U` (all but
the volatile `rax`, `r9..r11`) under some environment (the avx2_x8 loop restores `rsi` from its
frame as a data value, so the hand-over environment is the exit cut's), at depth 1296 (the
largest frame, avx2_x8's).  The avx2_x8 and avx_x4 links are their call-state statements
(`KSpecC8U`, `callSpec4`) lifted to the hand-over state (`WinLinkLift.lift`); the avx512_x16 hand-over
gains `rbx`/`rdi` by preservation (the stream never writes them).

-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinChainAll

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.RunAgree
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Proofs.X86Chain
open Hashtree.Proofs.WinChain
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.ShaniW (OutLogW)
open Hashtree.Proofs.WinAvx512Bridge (shift PostLink PreLink L8)
open Hashtree.Proofs.WinAvx2X8Link (U s8 KSpecC8U KSpecC8U_of_turnOut8W preLink_mk rodata8)
open Hashtree.Proofs.WinLinkLift (CallSpec lift)
open Hashtree.Proofs.WinAvxX1Link (CSR)
open Hashtree.Proofs.WinAvxX4Link (rodata4W x4_zero_run KZ4_err KZ4_tail postLink_zero preserved_cmp)
open Hashtree.Proofs.WinAvxX4Cert (ms_err ms_tail stepsW)
open Hashtree.Proofs.WinAvx2X8WOut (TurnOut8W TurnOut8WLast)
open Hashtree.Proofs.WinAvxX4WOut (TurnOut4W TurnOut4WLast)
open Hashtree.Proofs.WinShaniSeedAlign (mapState_getG)
open Hashtree.Proofs.WinShaniBridge (entryWin_gpr1 entryWin_gpr2 entryWin_gpr4 entryWin_gpr8)
open Hashtree.Proofs.WrapperAmd64 (sAt_eval)

/-! ## Monotonicity and environment independence -/

theorem wf_env (ro : List Nat) (e e' : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (h : WfMemW ro [] e σ m) : WfMemW ro [] e' σ m := by
  obtain ⟨h1, h2, h3, _⟩ := h
  exact ⟨h1, h2, h3, fun k c h _ _ => by simp [plookup] at h⟩

theorem foot_mono {sp : Int} {D D' : Nat} {ob : Int} {len : Nat} {M : CLog} (h : D ≤ D')
    (hf : Foot sp D ob len M) : Foot sp D' ob len M := by
  intro p hp
  rcases hf p hp with h1 | ⟨a, b, e⟩
  · exact Or.inl h1
  · exact Or.inr ⟨a, by omega, e⟩

theorem preLink_mono (env : Key → W32) (σ : Nat → Int) (c d r : Nat) (inp : Nat → Byte) {D D' : Nat}
    (hD : D ≤ D') {L L' : List Nat} (hL : ∀ x, x ∈ L' → x ∈ L) (s : CState)
    (h : PreLink env σ c d r inp D L s) : PreLink env σ c d r inp D' L' s := by
  obtain ⟨V, M', hV, hA, hlog, hfoot, hok⟩ := h
  exact ⟨V, M', hV, hA.mono hL (fun h => h), hlog, foot_mono hD hfoot, hok⟩

theorem postLink_mono (σ : Nat → Int) (c : Nat) (inp : Nat → Byte) {D D' : Nat} (hD : D ≤ D') (f : CState)
    (h : PostLink σ c inp D f) : PostLink σ c inp D' f :=
  ⟨h.1, foot_mono hD h.2.1, h.2.2.1, h.2.2.2⟩

/-- A hand-over gains registers that still hold their call-state values. -/
theorem preLink_add (env : Key → W32) (σ : Nat → Int) (c d r : Nat) (inp : Nat → Byte) (D : Nat)
    (L : List Nat) (s : CState) (h : PreLink env σ c d r inp D L s) (X : List Nat)
    (hX : ∀ x, x ∈ X → x ∈ [3, 5, 6, 7, 12, 13, 14, 15])
    (hg : ∀ x, x ∈ X → s.getG x = (mapState env σ entryWin).getG x) :
    PreLink env σ c d r inp D (L ++ X) s := by
  obtain ⟨V, M', hV, hA, hlog, hfoot, hok⟩ := h
  refine ⟨V, M', hV, { hA with gpr := fun x hx => ?_ }, hlog, hfoot, hok⟩
  rcases List.mem_append.mp hx with h | h
  · exact hA.gpr x h
  · rw [hg x h]; exact preserved_cmp env σ d r V M' x (hX x h)

/-! ## The avx_x4 and avx2_x8 links at the call state, hand-over on `U` -/

/-- The avx_x4 step function. -/
def s4 (c : Nat) : Nat := if c = 0 then 4 else stepsW c

theorem callSpec4 (hT : TurnOut4W) (hTL : TurnOut4WLast) :
    CallSpec p4 rodata4W s4 "hashtree_sha256_avx_x1" 4 568 U := by
  intro env σ m0 orcC r inp hw he hc _ hin
  by_cases hr0 : r = 0
  · subst hr0
    show (run p4 4 m0 orcC (s4 0) (mapState env σ entryWin)).err = none ∧ _
    rw [show s4 0 = 4 from rfl, x4_zero_run env σ m0 orcC hw he hc]
    exact ⟨by rw [ms_err, KZ4_err], Or.inl ⟨rfl, by rw [ms_tail, KZ4_tail], postLink_zero env σ inp⟩⟩
  · have hs : s4 r = stepsW r := by simp [s4, hr0]
    obtain ⟨herr, htail, hlen, h8, h1, h2, h4, hcs, hV, hlog, hfoot, hout⟩ :=
      Hashtree.Proofs.WinAvxX4Cert.spec env σ m0 orcC r inp hT hTL hw he hc hr0 hin
    show (run p4 4 m0 orcC (s4 r) (mapState env σ entryWin)).err = none ∧ _
    rw [hs]
    refine ⟨herr, Or.inr ⟨hr0, htail, env, preLink_mk env σ r _ _ inp 568 U _ hlen ?_ hV hlog hfoot hout herr⟩⟩
    intro j hj
    have pc : ∀ x, x ∈ [3, 5, 6, 7, 12, 13, 14, 15] →
        (run p4 4 m0 orcC (stepsW r) (mapState env σ entryWin)).getG x =
          (mapState env (shift σ (r - r % 4) (r % 4)) entryWin).getG x := fun x hx =>
      (hcs x hx).trans (preserved_cmp env σ _ _ [] [] x hx)
    simp only [U, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h1, mapState_getG entryWin_gpr1]; simp [mapVal, mapAddr, Lin.eval_sym, shift]
    · rw [h2, mapState_getG entryWin_gpr2]; simp [mapVal, mapAddr, Lin.eval_sym, shift]
    · exact pc 3 (by decide)
    · rw [h4, mapState_getG entryWin_gpr4]; simp [mapVal, mapAddr, sAt_eval, shift]
    · exact pc 5 (by decide)
    · exact pc 6 (by decide)
    · exact pc 7 (by decide)
    · rw [h8, mapState_getG entryWin_gpr8]; simp [mapVal, mapAddr, Lin.eval_sym, shift]
    · exact pc 12 (by decide)
    · exact pc 13 (by decide)
    · exact pc 14 (by decide)
    · exact pc 15 (by decide)

theorem callSpec8 (hT : TurnOut8W) (hTL : TurnOut8WLast) :
    CallSpec p8 rodata8 s8 "hashtree_sha256_avx_x4" 8 Hashtree.Proofs.WinAvx2X8Bridge.D8 U :=
  fun env σ m0 orcC r inp hw he hc habi hin => KSpecC8U_of_turnOut8W hT hTL env σ m0 orcC r inp hw he hc habi hin

theorem CSR_U : ∀ x, x ∈ CSR → x ∈ U := by decide
theorem L8e_U : ∀ x, x ∈ [8, 4, 5, 6, 12, 13, 14, 15, 2, 1] → x ∈ U := by decide
theorem L4e_U : ∀ x, x ∈ [8, 4, 2, 1] → x ∈ U := by decide
theorem L8_U : ∀ x, x ∈ U → x ∈ L8 ++ [3, 7] := by
  rw [show L8 = [8, 4, 5, 6, 12, 13, 14, 15, 2, 1] from Hashtree.Proofs.WinAvx2X8Live.live_entry_eq]; decide
theorem U_L1 : ∀ x, x ∈ Hashtree.Proofs.WinAvxX4Bridge.L1 → x ∈ U := by
  rw [show Hashtree.Proofs.WinAvxX4Bridge.L1 = [4, 3, 8, 6, 7, 5, 12, 13, 14, 15, 1, 2] from
    Hashtree.Proofs.WinAvxX1Live.live_entry_eq]; decide

/-! ## The four clauses -/

section Clauses
variable (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (c : Nat)
  (inp : Nat → Byte)

/-- The depth every later link's log stays within (avx2_x8's frame). -/
abbrev DW : Nat := 1296

def P8 : CS → Prop := fun s => ∃ e : Key → W32, PreLink e σ c (c - c % 16) (c % 16) inp DW U s
def P4 : CS → Prop := fun s => ∃ e : Key → W32, PreLink e σ c (c - c % 8) (c % 8) inp DW U s
def P1 : CS → Prop := fun s => ∃ e : Key → W32, PreLink e σ c (c - c % 4) (c % 4) inp DW U s

theorem clause512 (hw : WfMemW Hashtree.Kernels.X86Win.Avx512X16.rodata [] env σ m0) (he : EnvMem env σ m0)
    (hc : σ 2 = c) (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ s, s = mapState env σ entryWin →
      let f := step m0 orcC c (linkOf "hashtree_sha256_avx512_x16" p512 Hashtree.Proofs.Avx512X16WLoop.steps) s
      f.err = none ∧
        ((f.tail = none ∧ PostLink σ c inp DW f) ∨
         (f.tail = some "hashtree_sha256_avx2_x8" ∧ P8 σ c inp (resume f))) := by
  intro s hs
  have h := Hashtree.Proofs.WinAvx512Final.head512 env σ m0 orcC c inp hw he hc hin s hs
  subst hs
  obtain ⟨herr, hcase⟩ := h
  refine ⟨herr, ?_⟩
  rcases hcase with ⟨ht, hp⟩ | ⟨ht, hp⟩
  · exact Or.inl ⟨ht, postLink_mono σ c inp (by decide) _ hp⟩
  · refine Or.inr ⟨ht, env, ?_⟩
    have hpres : ∀ x, x ∈ [3, 7] → (resume (step m0 orcC c (linkOf "hashtree_sha256_avx512_x16" p512
        Hashtree.Proofs.Avx512X16WLoop.steps) (mapState env σ entryWin))).getG x =
        (mapState env σ entryWin).getG x := by
      intro x hx
      have hx' : x ∈ [3, 5, 6, 7, 12, 13, 14, 15] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega
      exact Hashtree.Asm.RunExit.run_preserve_all p512 4 m0 orcC x
        (Hashtree.Asm.RunExit.unwrittenScan_sound Hashtree.Proofs.WinAvx512Live.unwritten x hx') _ _ herr
    have hadd := preLink_add env σ c _ _ inp 0 L8 _ hp [3, 7]
      (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; omega) hpres
    exact preLink_mono env σ c _ _ inp (by decide) L8_U _ hadd

theorem clause8 (hT : TurnOut8W) (hTL : TurnOut8WLast) (hw : WfMemW rodata8 [] env σ m0)
    (habi : σ 9 % 16 = 8) (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ s, P8 σ c inp s →
      let f := step m0 orcC c (linkOf "hashtree_sha256_avx2_x8" p8 (fun c => s8 (c % 16))) s
      f.err = none ∧
        ((f.tail = none ∧ PostLink σ c inp DW f) ∨
         (f.tail = some "hashtree_sha256_avx_x4" ∧ P4 σ c inp (resume f))) := by
  intro s ⟨e, hpre⟩
  have hLp : ∀ x, x ∈ (fun p => Hashtree.Proofs.WinAvx2X8Live.liveT.getD p []) 0 ++ U → x ∈ U := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · have h' : x ∈ Hashtree.Proofs.WinAvx2X8Live.liveT.getD 0 [] := h
      rw [Hashtree.Proofs.WinAvx2X8Live.live_entry_eq] at h'
      exact L8e_U x h'
    · exact h
  have h := lift Hashtree.Proofs.WinAvx2X8Live.cert Hashtree.Proofs.WinAvx2X8Live.liveF_entry s8
    "hashtree_sha256_avx_x4" 8 Hashtree.Proofs.WinAvx2X8Bridge.D8 U (callSpec8 hT hTL) U (fun x hx => hx) CSR_U U hLp
    e σ m0 orcC c inp DW (by decide) (wf_env rodata8 env e σ m0 hw) habi hin (c - c % 16) (c % 16) (by omega) s hpre
  obtain ⟨herr, hcase⟩ := h
  refine ⟨herr, ?_⟩
  rcases hcase with ⟨_, ht, hp⟩ | ⟨_, ht, e', hp⟩
  · exact Or.inl ⟨ht, hp⟩
  · refine Or.inr ⟨ht, e', ?_⟩
    rw [show c - c % 16 + (c % 16 - c % 16 % 8) = c - c % 8 by omega,
      show c % 16 % 8 = c % 8 by omega] at hp
    exact hp

theorem clause4 (hT : TurnOut4W) (hTL : TurnOut4WLast) (hw : WfMemW rodata4W [] env σ m0)
    (habi : σ 9 % 16 = 8) (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ s, P4 σ c inp s →
      let f := step m0 orcC c (linkOf "hashtree_sha256_avx_x4" p4 (fun c => s4 (c % 8))) s
      f.err = none ∧
        ((f.tail = none ∧ PostLink σ c inp DW f) ∨
         (f.tail = some "hashtree_sha256_avx_x1" ∧ P1 σ c inp (resume f))) := by
  intro s ⟨e, hpre⟩
  have hLp : ∀ x, x ∈ (fun p => Hashtree.Proofs.WinAvxX4Live.liveT.getD p []) 0 ++ U → x ∈ U := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · have h' : x ∈ Hashtree.Proofs.WinAvxX4Live.liveT.getD 0 [] := h
      rw [Hashtree.Proofs.WinAvxX4Live.live_entry_eq] at h'
      exact L4e_U x h'
    · exact h
  have h := lift Hashtree.Proofs.WinAvxX4Live.cert Hashtree.Proofs.WinAvxX4Live.liveF_entry s4
    "hashtree_sha256_avx_x1" 4 568 U (callSpec4 hT hTL) U (fun x hx => hx) CSR_U U hLp
    e σ m0 orcC c inp DW (by decide) (wf_env rodata4W env e σ m0 hw) habi hin (c - c % 8) (c % 8) (by omega) s hpre
  obtain ⟨herr, hcase⟩ := h
  refine ⟨herr, ?_⟩
  rcases hcase with ⟨_, ht, hp⟩ | ⟨_, ht, e', hp⟩
  · exact Or.inl ⟨ht, hp⟩
  · refine Or.inr ⟨ht, e', ?_⟩
    rw [show c - c % 8 + (c % 8 - c % 8 % 4) = c - c % 4 by omega,
      show c % 8 % 4 = c % 4 by omega] at hp
    exact hp

theorem clause1 (hw : WfMemW Hashtree.Kernels.X86Win.AvxX1.rodata [] env σ m0)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ s, P1 σ c inp s →
      let f := step m0 orcC c (linkOf "hashtree_sha256_avx_x1" p1
        (fun c => Hashtree.Proofs.WinAvxX1W.steps (c % 4))) s
      f.err = none ∧ f.tail = none ∧ PostLink σ c inp DW f := by
  intro s ⟨e, hpre⟩
  exact Hashtree.Proofs.WinAvxX1Link.last1 e σ m0 orcC c inp DW (by decide)
    (wf_env _ env e σ m0 hw) hin s (preLink_mono e σ c _ _ inp (Nat.le_refl _) U_L1 s hpre)

end Clauses

end Hashtree.Proofs.WinChainAll
