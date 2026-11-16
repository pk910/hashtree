import Hashtree.Proofs.WinAvxX1W
import Hashtree.Proofs.WinAvxX4Bridge

/-!
# R5: the avx_x1 link of the windows chain (the last link, `KSpecC` clause for `winSpecs`)

From `PreLink env σ c d r inp D L1 s` (the state the avx_x4 link hands over: on the avx_x1 entry
live set `L1` it is the wrapper call state with the symbols advanced by `d` blocks, under some
vector file `V`, over the previous links' log `M'`), the windows avx_x1 stream runs `steps r`
instructions and returns meeting `PostLink σ c inp D` (`d + r = c`, `264 ≤ D`).

The proof: the comparison state is a wrapper call state `mapState env' σ' entryWin` for an
environment `env'` that carries `V` on the vector symbols and the viewed memory on the memory
keys (`envV`); the run from it over the log `M'` is `WinAvxX1W.correctW` on the viewed memory
(`run_fr`); the actual run agrees with it by `run_agree` on the liveness certificate of the
windows avx_x1 stream extended by the Win64 callee-saved registers and `rsp` at every pc
(`cert_const`: adding a constant set keeps a certificate valid), so the final states have the
same log, status and callee-saved registers.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinAvxX1Link

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Asm.RunAgree
open Hashtree.Asm.SpecQ Hashtree.Spec
open Hashtree.Proofs.WinWrapper (entryWin Foot OutOk RegsOkW)
open Hashtree.Proofs.ShaniW (OutLogW)
open Hashtree.Proofs.WinAvx512Bridge (shift PostLink PreLink)
open Hashtree.Proofs.WinAvxX4Bridge (L1)

abbrev prog : Array Instr := Hashtree.Kernels.X86Win.AvxX1.prog

/-! ## A certificate stays valid when a constant set is added at every pc -/

theorem cert_const {prog : Array Instr} {L : Nat → List Nat} {LF : Nat → Bool} {T : List Nat}
    (hc : Cert prog L LF T) (C : List Nat) : Cert prog (fun p => L p ++ C) LF T := by
  intro p i hp
  obtain ⟨h1, h2, h3, h4⟩ := hc p i hp
  refine ⟨fun r hr => List.mem_append_left _ (h1 r hr), h2,
    fun ht r hr => List.mem_append_left _ (h3 ht r hr), fun q hq => ⟨fun r hr => ?_, (h4 q hq).2⟩⟩
  rcases List.mem_append.mp hr with h | h
  · rcases List.mem_append.mp ((h4 q hq).1 r h) with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (List.mem_append_left _ h')
  · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- The registers `RegsOkW` reads: the Win64 callee-saved ones it names and `rsp`. -/
def CSR : List Nat := [3, 4, 5, 12, 13, 14, 15]

def LX (p : Nat) : List Nat := Hashtree.Proofs.WinAvxX1Live.liveT.getD p [] ++ CSR

theorem certX : Cert prog LX (fun p => Hashtree.Proofs.WinAvxX1Live.liveFT.getD p false) [] :=
  cert_const Hashtree.Proofs.WinAvxX1Live.cert CSR

theorem LX_entry : ∀ r, r ∈ LX 0 → r ∈ L1 := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact h
  · show r ∈ Hashtree.Proofs.WinAvxX1Live.liveT.getD 0 []
    rw [Hashtree.Proofs.WinAvxX1Live.live_entry_eq]
    simp only [CSR, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem CSR_LX (p : Nat) : ∀ r, r ∈ CSR → r ∈ LX p := fun _ h => List.mem_append_right _ h

/-! ## The comparison state as a wrapper call state -/

/-- The vector file `V` on the vector symbols, the memory `m` on the memory keys, `env` elsewhere. -/
def envV (env : Key → W32) (σ' : Nat → Int) (m : Addr Int → Cell W32 Int) (V : List (List W32)) :
    Key → W32
  | .n k => if 100 ≤ k ∧ k < 612 then (V.getD ((k - 100) / 16) []).getD ((k - 100) % 16) 0 else env (.n k)
  | .m r off => cellX (m ⟨r, off.eval σ'⟩)

theorem envV_mem (env : Key → W32) (σ' : Nat → Int) (m : Addr Int → Cell W32 Int) (V : List (List W32)) :
    EnvMem (envV env σ' m V) σ' m := fun _ _ => rfl

theorem mapState_envV (env : Key → W32) (σ' : Nat → Int) (m : Addr Int → Cell W32 Int)
    (V : List (List W32)) (hV : V.length = 32 ∧ ∀ v ∈ V, v.length = 16) :
    { mapState env σ' entryWin with vr := V } = mapState (envV env σ' m V) σ' entryWin := by
  have hg : entryWin.gpr.map (mapVal env σ') = entryWin.gpr.map (mapVal (envV env σ' m V) σ') := by
    simp only [entryWin, List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' : i < 16 := List.mem_range.mp hi
    simp only [Function.comp]
    repeat' split
    all_goals simp [mapVal, E.eval, envV, gId]
    all_goals omega
  have hv : V = entryWin.vr.map (·.map (E.eval (envV env σ' m V))) := by
    apply List.ext_getElem
    · simp [entryWin, hV.1]
    · intro i h1 h2
      have hi : i < 32 := by rw [hV.1] at h1; exact h1
      apply List.ext_getElem
      · simp [entryWin, hV.2 _ (List.getElem_mem h1)]
      · intro l k1 k2
        have hl : l < 16 := by rw [hV.2 _ (List.getElem_mem h1)] at k1; exact k1
        simp only [entryWin, List.getElem_map, List.getElem_range, E.eval, envV, vId]
        rw [if_pos (by omega)]
        have e1 : (100 + 16 * i + l - 100) / 16 = i := by omega
        have e2 : (100 + 16 * i + l - 100) % 16 = l := by omega
        rw [e1, e2, show V.getD i [] = V[i] by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some],
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem k1, Option.getD_some]
  have hm : entryWin.mem = [] := rfl
  simp only [mapState, hm, List.map_nil]
  rw [hg, ← hv]

/-! ## The viewed memory -/

theorem wf_view (rodata : List Nat) (env : Key → W32) (σ σ' : Nat → Int) (m0 : Addr Int → Cell W32 Int)
    (V : List (List W32)) (M' : CLog) (hw : WfMemW rodata [] env σ m0) (h9 : σ' 9 = σ 9)
    (hlog : OutLogW (σ 9) M') :
    WfMemW rodata [] (envV env σ' (view M' m0) V) σ' (view M' m0) := by
  obtain ⟨hro, hret, hin, _⟩ := hw
  refine ⟨fun o => ?_, fun k h0 h8 => ?_, fun o => ?_, fun k c h _ _ => by simp [plookup] at h⟩
  · rw [view_other]
    · exact hro o
    · intro p hp heq
      rcases hlog p hp with h | ⟨h, _⟩ <;> rw [heq] at h <;> simp [rOut, rStack] at h
  · rw [view_other, h9]
    · exact hret k h0 h8
    · intro p hp heq
      rcases hlog p hp with h | ⟨h, hl⟩
      · rw [heq] at h; simp [rOut, rStack] at h
      · rw [heq] at hl; simp only at hl; omega
  · have hv : view M' m0 ⟨rIn, o⟩ = m0 ⟨rIn, o⟩ := by
      apply view_other
      intro p hp heq
      rcases hlog p hp with h | ⟨h, _⟩ <;> rw [heq] at h <;> simp [rIn, rOut, rStack] at h
    rw [hv]; exact hin o

/-! ## Register transfer -/

theorem getElem?_getG (s : CState) (j : Nat) (hj : j < s.gpr.length) : s.gpr[j]? = some (s.getG j) := by
  rw [List.getElem?_eq_getElem hj]
  simp only [State.getG, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem gpr_transfer {s1 s2 : CState} {j : Nat} {v : Val W32 Int} (hl : s1.gpr.length = s2.gpr.length)
    (hg : s1.getG j = s2.getG j) (h : s2.gpr[j]? = some v) : s1.gpr[j]? = some v := by
  rcases Nat.lt_or_ge j s2.gpr.length with hj | hj
  · rw [getElem?_getG s1 j (by omega), hg, ← getElem?_getG s2 j hj]; exact h
  · rw [List.getElem?_eq_none hj] at h; cases h

theorem blk_shift_n (inp : Nat → Byte) (d n : Nat) : blk (fun o => inp (64 * d + o)) n = blk inp (d + n) := by
  funext i; simp only [blk]; congr 1; omega

/-! ## The link -/

/-- **The avx_x1 link of the windows chain.**  From the hand-over state of the previous link
(`PreLink` on `L1` with `d` blocks done and `r` remaining, `d + r = c`), the windows avx_x1 stream
returns after `steps r` instructions without a model error, all `c` output blocks correct, the
footprint inside `[σ 9 - D, σ 9)` and the output, and the Win64 callee-saved registers and `rsp`
restored. -/
theorem tail1 (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (c : Nat) (inp : Nat → Byte) (D : Nat) (hD : 264 ≤ D)
    (hw : WfMemW Hashtree.Kernels.X86Win.AvxX1.rodata [] env σ m0)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (d r : Nat) (hdr : d + r = c) (s : CState) (hpre : PreLink env σ c d r inp D L1 s) :
    let f := run prog 4 m0 orcC (Hashtree.Proofs.WinAvxX1W.steps r) s
    f.err = none ∧ f.tail = none ∧ PostLink σ c inp D f := by
  obtain ⟨V, M', hV, hA, hlog, hfoot, hok⟩ := hpre
  intro f
  have hX := mapState_envV env (shift σ d r) (view M' m0) V hV
  rw [hX] at hA
  have h9 : shift σ d r 9 = σ 9 := rfl
  have hw' := wf_view Hashtree.Kernels.X86Win.AvxX1.rodata env σ (shift σ d r) m0 V M' hw h9 hlog
  have hin' : ∀ o : Nat, view M' m0 ⟨rIn, shift σ d r 0 + o⟩ = .dat ((inp (64 * d + o)).zeroExtend 32) 0 := by
    intro o
    rw [view_other]
    · rw [show shift σ d r 0 + (o : Int) = σ 0 + ((64 * d + o : Nat) : Int) by simp [shift]; omega]
      exact hin (64 * d + o)
    · intro p hp heq
      rcases hlog p hp with h | ⟨h, _⟩ <;> rw [heq] at h <;> simp [rIn, rOut, rStack] at h
  have hcw := Hashtree.Proofs.WinAvxX1W.correctW r (fun o => inp (64 * d + o))
    (envV env (shift σ d r) (view M' m0) V) (shift σ d r) (view M' m0) orcC hw'
    (envV_mem env (shift σ d r) (view M' m0) V) (by simp [shift]) hin'
  rw [Hashtree.Proofs.WinAvxX1W.entryWinS_eq] at hcw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcw
  have hpc : s.pc = 0 := hA.pc
  have hA0 : Agree (LX s.pc) (Hashtree.Proofs.WinAvxX1Live.liveFT.getD s.pc false) s
      (fr M' (mapState (envV env (shift σ d r) (view M' m0) V) (shift σ d r) entryWin)) := by
    rw [hpc, Hashtree.Proofs.WinAvxX1Live.liveF_entry]
    exact hA.mono LX_entry (fun h => h)
  have hR := run_agree prog 4 m0 orcC certX (Hashtree.Proofs.WinAvxX1W.steps r) hA0
  rw [run_fr] at hR
  generalize hfin : run prog 4 (view M' m0) orcC (Hashtree.Proofs.WinAvxX1W.steps r)
    (mapState (envV env (shift σ d r) (view M' m0) V) (shift σ d r) entryWin) = fin at hR h1 h2 h3 h4 h5 h6
  have hmem : f.mem = fin.mem ++ M' := hR.mem
  have hs1 : shift σ d r 1 = σ 1 + 32 * (d : Int) := by simp [shift]
  refine ⟨hR.err.trans h2, hR.tail.trans h3, hR.halted.trans h1, ?_, ?_, ?_⟩
  · intro p hp
    rw [hmem] at hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases h4 p hp with ⟨a, b, e⟩ | ⟨a, b, e⟩
      · left; rw [hs1] at b e; refine ⟨a, by omega, ?_⟩
        have : (32 * c : Nat) = 32 * d + 32 * r := by omega
        push_cast [this] at e ⊢; omega
      · right; rw [h9] at b e; exact ⟨a, by omega, e⟩
    · exact hfoot p hp
  · have hnew : ∀ n i b, n < r → i < 8 → b < 4 → ∃ x,
        lookup (⟨rOut, shift σ d r 1 + ((32 * n + 4 * i + b : Nat) : Int)⟩ : Addr Int) fin.mem = .ok (some (.dat x b)) ∧
          byteOf x b = ((node (blk inp (d + n))).getD (4 * i + b) 0).zeroExtend 32 := by
      intro n i b hn hi hb
      obtain ⟨x, hx, hv⟩ := h5 n i b hn hi hb
      exact ⟨x, hx, by rw [hv, blk_shift_n]⟩
    have hL : ∀ p ∈ fin.mem, p.1.region ≠ rOut ∨ σ 1 + 32 * (d : Int) ≤ p.1.off := by
      intro p hp
      rcases h4 p hp with ⟨_, b, _⟩ | ⟨a, _, _⟩
      · right; rw [hs1] at b; exact b
      · left; rw [a]; decide
    have := Hashtree.Proofs.WinAvxX1W.outOk_new inp (σ 1) d r fin.mem M' (shift σ d r 1) hs1 hnew hL hok
    rw [hdr] at this
    rw [hmem]; exact this
  · have hl : f.gpr.length = fin.gpr.length := hR.len
    have hg : ∀ j, j ∈ CSR → f.getG j = fin.getG j := fun j hj => hR.gpr j (CSR_LX _ j hj)
    obtain ⟨g3, g5, g12, g13, g14, g15, g4⟩ := h6
    exact ⟨gpr_transfer hl (hg 3 (by decide)) g3, gpr_transfer hl (hg 5 (by decide)) g5,
      gpr_transfer hl (hg 12 (by decide)) g12, gpr_transfer hl (hg 13 (by decide)) g13,
      gpr_transfer hl (hg 14 (by decide)) g14, gpr_transfer hl (hg 15 (by decide)) g15,
      gpr_transfer hl (hg 4 (by decide)) g4⟩

/-- **The last clause of `KSpecC` for `winSpecs`**, at the avx_x1 link with step function
`fun c => steps (c % 4)` (the link always runs the `c % 4` blocks the avx_x4 link leaves). -/
theorem last1 (env : Key → W32) (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (c : Nat) (inp : Nat → Byte) (D : Nat) (hD : 264 ≤ D)
    (hw : WfMemW Hashtree.Kernels.X86Win.AvxX1.rodata [] env σ m0)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    ∀ s, PreLink env σ c (c - c % 4) (c % 4) inp D L1 s →
      let f := Hashtree.Proofs.X86Chain.step m0 orcC c (Hashtree.Proofs.WinChain.linkOf
        "hashtree_sha256_avx_x1" Hashtree.Proofs.WinChain.p1 (fun c => Hashtree.Proofs.WinAvxX1W.steps (c % 4))) s
      f.err = none ∧ f.tail = none ∧ PostLink σ c inp D f :=
  fun s hs => tail1 env σ m0 orcC c inp D hD hw hin (c - c % 4) (c % 4) (by omega) s hs

end Hashtree.Proofs.WinAvxX1Link
