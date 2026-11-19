import Hashtree.Proofs.WinAvxX1Link
import Hashtree.Proofs.WinAvxX4Link

/-!
# R5: a chain link from its call-state statement — the lift to the hand-over state

The link obligations `KSpecC512`/`KSpecC8`/`KSpecC4` are stated from the wrapper call state
`mapState env σ entryWin`.  In the chain a link starts from the previous link's hand-over
(`PreLink env σ c d r inp D Lp s`: on the registers `Lp` the call state with the symbols
advanced by the `d` finished blocks, under some vector file `V`, over the previous links' log
`M'`).  `lift` turns a call-state statement (`CallSpec`, quantified over the environment, the
symbols and the memory) into the hand-over form: the comparison state is a call state for the
environment `envV` (the vector file on the vector symbols, the viewed memory on the memory keys)
at the advanced symbols over the viewed memory `view M' m0`; the actual run agrees with it by
`run_agree` on the stream's liveness certificate extended by a constant set `C` (`cert_const`)
that holds the next link's hand-over set and the registers `RegsOkW` reads; the call-state
statement's return or hand-over at the advanced symbols becomes the return or hand-over at the
original symbols (`shift_shift`, logs appended, `outOk_new` joins the output blocks).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinLinkLift

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.RunAgree
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Proofs.X86Chain (resume)
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.ShaniW (OutLogW)
open Hashtree.Proofs.WinAvx512Bridge (shift PostLink PreLink)
open Hashtree.Proofs.WinAvxX1Link (cert_const CSR envV envV_mem mapState_envV wf_view gpr_transfer blk_shift_n)

/-- A link's statement at the wrapper call state, for every remaining count `r = σ 2`: return at
`r = 0`, otherwise the tail `nm` with `r - r % k` blocks done, on the hand-over set `Ln`, under
some environment. -/
def CallSpec (p : Array Instr) (ro : List Nat) (S : Nat → Nat) (nm : String) (k Dk : Nat) (Ln : List Nat) : Prop :=
  ∀ (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r : Nat)
    (inp : Nat → Byte),
    WfMemW ro [] env σ m0 → EnvMem env σ m0 → σ 2 = r → σ 9 % 16 = 8 →
    (∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) →
    let f := run p 4 m0 orcC (S r) (mapState env σ entryWin)
    f.err = none ∧
      ((r = 0 ∧ f.tail = none ∧ PostLink σ r inp 0 f) ∨
       (r ≠ 0 ∧ f.tail = some nm ∧ ∃ e' : Key → W32, PreLink e' σ r (r - r % k) (r % k) inp Dk Ln (resume f)))

theorem shift_shift (σ : Nat → Int) (d r a b : Nat) : shift (shift σ d r) a b = shift σ (d + a) b := by
  funext i
  simp only [shift]
  by_cases h0 : i = 0
  · subst h0; simp; push_cast; omega
  by_cases h1 : i = 1
  · subst h1; simp; push_cast; omega
  by_cases h2 : i = 2
  · subst h2; simp
  simp [h0, h1, h2]

theorem shift_hi (σ : Nat → Int) (d r i : Nat) (hi : 3 ≤ i) : shift σ d r i = σ i := by
  simp [shift, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega]

theorem regsOkW_shift (σ : Nat → Int) (d r : Nat) (s : CState) (h : RegsOkW (shift σ d r) s) : RegsOkW σ s := by
  obtain ⟨g3, g5, g12, g13, g14, g15, g4⟩ := h
  rw [shift_hi σ d r 5 (by omega)] at g3
  rw [shift_hi σ d r 6 (by omega)] at g5
  rw [shift_hi σ d r 7 (by omega)] at g12
  rw [shift_hi σ d r 11 (by omega)] at g13
  rw [shift_hi σ d r 8 (by omega)] at g14
  rw [shift_hi σ d r 12 (by omega)] at g15
  rw [shift_hi σ d r 9 (by omega)] at g4
  exact ⟨g3, g5, g12, g13, g14, g15, g4⟩

/-- `RegsOkW` moves along agreement on `CSR`. -/
theorem regsOkW_agree (σ : Nat → Int) (s1 s2 : CState) (hl : s1.gpr.length = s2.gpr.length)
    (hg : ∀ x, x ∈ CSR → s1.getG x = s2.getG x) (h : RegsOkW σ s2) : RegsOkW σ s1 := by
  obtain ⟨g3, g5, g12, g13, g14, g15, g4⟩ := h
  exact ⟨gpr_transfer hl (hg 3 (by decide)) g3, gpr_transfer hl (hg 5 (by decide)) g5,
    gpr_transfer hl (hg 12 (by decide)) g12, gpr_transfer hl (hg 13 (by decide)) g13,
    gpr_transfer hl (hg 14 (by decide)) g14, gpr_transfer hl (hg 15 (by decide)) g15,
    gpr_transfer hl (hg 4 (by decide)) g4⟩

section Lift
variable {p : Array Instr} {ro : List Nat} {LL : Nat → List Nat} {LF : Nat → Bool}

/-- **The lift.**  A link with a liveness certificate whose flags are dead at entry, and a
call-state statement, runs from any hand-over state agreeing on `Lp ⊇ LL 0 ++ C` (where `C`
holds the next hand-over set `Ln` and `CSR`), and returns or hands over at the original symbols:
`d` blocks done before, `r - r % k` more by this link. -/
theorem lift (hcert : Cert p LL LF []) (hF : LF 0 = false) (S : Nat → Nat) (nm : String) (k Dk : Nat)
    (Ln : List Nat) (hspec : CallSpec p ro S nm k Dk Ln)
    (C : List Nat) (hLn : ∀ x, x ∈ Ln → x ∈ C) (hCSR : ∀ x, x ∈ CSR → x ∈ C)
    (Lp : List Nat) (hLp : ∀ x, x ∈ LL 0 ++ C → x ∈ Lp)
    (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (c : Nat)
    (inp : Nat → Byte) (D : Nat) (hD : Dk ≤ D)
    (hw : WfMemW ro [] env σ m0) (habi : σ 9 % 16 = 8)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (d r : Nat) (hdr : d + r = c) (s : CState) (hpre : PreLink env σ c d r inp D Lp s) :
    let f := run p 4 m0 orcC (S r) s
    f.err = none ∧
      ((r = 0 ∧ f.tail = none ∧ PostLink σ c inp D f) ∨
       (r ≠ 0 ∧ f.tail = some nm ∧
         ∃ e' : Key → W32, PreLink e' σ c (d + (r - r % k)) (r % k) inp D Ln (resume f))) := by
  obtain ⟨V, M', hV, hA, hlog, hfoot, hok⟩ := hpre
  intro f
  have hX := mapState_envV env (shift σ d r) (view M' m0) V hV
  rw [hX] at hA
  have h9 : shift σ d r 9 = σ 9 := rfl
  have hw' := wf_view ro env σ (shift σ d r) m0 V M' hw h9 hlog
  have hin' : ∀ o : Nat, view M' m0 ⟨rIn, shift σ d r 0 + o⟩ = .dat ((inp (64 * d + o)).zeroExtend 32) 0 := by
    intro o
    rw [view_other]
    · rw [show shift σ d r 0 + (o : Int) = σ 0 + ((64 * d + o : Nat) : Int) by simp [shift]; omega]
      exact hin (64 * d + o)
    · intro q hq heq
      rcases hlog q hq with h | ⟨h, _⟩ <;> rw [heq] at h <;> simp [rIn, rOut, rStack] at h
  have hsp := hspec (envV env (shift σ d r) (view M' m0) V) (shift σ d r) (view M' m0) orcC r
    (fun o => inp (64 * d + o)) hw' (envV_mem env (shift σ d r) (view M' m0) V) (by simp [shift])
    (by rw [h9]; exact habi) hin'
  have hpc : s.pc = 0 := hA.pc
  have hA0 : Agree ((fun q => LL q ++ C) s.pc) (LF s.pc) s
      (fr M' (mapState (envV env (shift σ d r) (view M' m0) V) (shift σ d r) entryWin)) := by
    rw [hpc, hF]
    exact hA.mono (fun x hx => hLp x hx) (fun h => h)
  have hR := run_agree p 4 m0 orcC (cert_const hcert C) (S r) hA0
  rw [run_fr] at hR
  generalize hfin : run p 4 (view M' m0) orcC (S r)
    (mapState (envV env (shift σ d r) (view M' m0) V) (shift σ d r) entryWin) = fin at hR hsp
  have hmem : f.mem = fin.mem ++ M' := hR.mem
  have hC : ∀ x, x ∈ C → f.getG x = fin.getG x := fun x hx => hR.gpr x (List.mem_append_right _ hx)
  have hlen : f.gpr.length = fin.gpr.length := hR.len
  obtain ⟨herr', hcase⟩ := hsp
  refine ⟨hR.err.trans herr', ?_⟩
  have hs1 : shift σ d r 1 = σ 1 + 32 * (d : Int) := by simp [shift]
  rcases hcase with ⟨hr0, htl, hpost⟩ | ⟨hr0, htl, e', hpl⟩
  · -- the link returns
    obtain ⟨hh, hft, _, hreg⟩ := hpost
    have hnil : fin.mem = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hq
      rcases hft q hq with ⟨_, a, b⟩ | ⟨_, a, b⟩
      · rw [hr0] at a b; simp at b; omega
      · simp at a; omega
    have hcd : c = d := by omega
    refine Or.inl ⟨hr0, hR.tail.trans htl, hR.halted.trans hh, ?_, ?_, ?_⟩
    · rw [hmem, hnil, List.nil_append]; exact hfoot
    · rw [hmem, hnil, List.nil_append, hcd]; exact hok
    · exact regsOkW_agree σ f fin hlen (fun x hx => hC x (hCSR x hx)) (regsOkW_shift σ d r fin hreg)
  · -- the link hands over
    refine Or.inr ⟨hr0, hR.tail.trans htl, e', ?_⟩
    obtain ⟨V', M'', hV', hA', hlog', hfoot', hok'⟩ := hpl
    rw [shift_shift] at hA'
    refine ⟨V', M'' ++ M', hV', ?_, ?_, ?_, ?_⟩
    · refine ⟨fun x hx => ?_, ?_, ?_, (fun h => by cases h), ?_, rfl, rfl, rfl, ?_⟩
      · show f.getG x = _
        rw [hC x (hLn x hx)]
        exact hA'.gpr x hx
      · show f.gpr.length = _
        rw [hlen]; exact hA'.len
      · show f.vr = V'
        rw [hR.vr]; exact hA'.vr
      · show f.mem = _
        rw [hmem]
        have := hA'.mem
        change fin.mem = _ at this
        rw [this]
        simp only [fr, List.append_assoc]
      · show f.err = none
        exact hR.err.trans herr'
    · intro q hq
      rcases List.mem_append.mp hq with h | h
      · exact hlog' q h
      · exact hlog q h
    · intro q hq
      rcases List.mem_append.mp hq with h | h
      · rcases hfoot' q h with ⟨a, b, e⟩ | ⟨a, b, e⟩
        · left; rw [hs1] at b e; refine ⟨a, by omega, ?_⟩
          have : (32 * c : Nat) = 32 * d + 32 * r := by omega
          push_cast [this] at e ⊢; omega
        · right; rw [h9] at b e; exact ⟨a, by omega, e⟩
      · exact hfoot q h
    · have hnew : ∀ n i b, n < r - r % k → i < 8 → b < 4 → ∃ x,
          lookup (⟨rOut, shift σ d r 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) M'' = .ok (some (.dat x b)) ∧
            byteOf x b = ((node (blk inp (d + n))).getD (4 * i + b) 0).zeroExtend 32 := by
        intro n i b hn hi hb
        obtain ⟨x, hx, hv⟩ := hok' n i b hn hi hb
        exact ⟨x, hx, by rw [hv, blk_shift_n]⟩
      have hL : ∀ q ∈ M'', q.1.region ≠ rOut ∨ σ 1 + 32 * (d : Int) ≤ q.1.off := by
        intro q hq
        rcases hfoot' q hq with ⟨_, b, _⟩ | ⟨a, _, _⟩
        · right; rw [hs1] at b; exact b
        · left; rw [a]; decide
      exact Hashtree.Proofs.WinAvxX1W.outOk_new inp (σ 1) d (r - r % k) M'' M' (shift σ d r 1) hs1 hnew hL hok

end Lift

end Hashtree.Proofs.WinLinkLift
