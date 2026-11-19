import Hashtree.Proofs.WinChainAll
import Hashtree.Proofs.WinLinkSwap

/-!
# R5: the windows tail chain with one rodata region per link

`WinChainAll` composes the four links with every table in region 4 (`WinChain.linkOf`); there the
four memory hypotheses fix region 4 to four different tables, so they cannot hold together.
Here each link reads its own region — avx512_x16 at 7, avx2_x8 at 8, avx_x4 at 4, avx_x1 at 9 —
and the four tables sit side by side in one memory (`WfMemAtW`).  Each link's region-4 clause
(`WinChainAll.clause*`, on the swapped memory) becomes its clause at its own region by
`X86Ren.run_swap_chain`: the run at region `r` is the region-4 run renamed by `swap 4 r`, and the
chain's conditions are invariant under that renaming (`WinLinkSwap`).

`win_chain_correct_regions`: from the wrapper call state the chain run ends without a model
error and without a pending tail, halted, all `c` output blocks correct, the footprint inside
the output and `[σ 9 - 1296, σ 9)`, the Win64 callee-saved registers and `rsp` restored —
conditional only on R2c's `TurnOut8W`/`TurnOut8WLast`/`TurnOut4W`/`TurnOut4WLast`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Hashtree.Proofs.WinChainRegions

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Spec
open Hashtree.Proofs.X86Chain
open Hashtree.Proofs.WinChain (p512 p8 p4 p1 linkOf)
open Hashtree.Proofs.WinWrapper (entryWin)
open Hashtree.Proofs.WinAvx512Bridge (PostLink PreLink)
open Hashtree.Proofs.WinAvx2X8Link (U s8 rodata8)
open Hashtree.Proofs.WinAvxX4Link (rodata4W)
open Hashtree.Proofs.WinChainAll (DW P8 P4 P1 s4 clause512 clause8 clause4 clause1)
open Hashtree.Proofs.WinLinkSwap (Fix fix_swap preLink_ren postLink_ren run_at swap_mem_wf swap_mem_in
  envSwap envSwap_mem mapState_envSwap state_entryWin)
open Hashtree.Proofs.WinAvx2X8WOut (TurnOut8W TurnOut8WLast)
open Hashtree.Proofs.WinAvxX4WOut (TurnOut4W TurnOut4WLast)

/-! ## A clause at region 4 becomes a clause at region `r` -/

theorem clause_at (r : Region) (hF : Fix (swap 4 r)) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet)
    (p : Array Instr) (n : Nat) (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (P P4 Q Pn : CS → Prop) (nm : String)
    (hP : ∀ s, P s → P4 ((swap 4 r).state s)) (hQ : ∀ f, Q f → Q ((swap 4 r).state f))
    (hPn : ∀ f, Pn f → Pn ((swap 4 r).state f))
    (h4 : ∀ s, P4 s → let f := run p 4 ((swap 4 r).mem m0) orc n s
      f.err = none ∧ ((f.tail = none ∧ Q f) ∨ (f.tail = some nm ∧ Pn (resume f)))) :
    ∀ s, P s → let f := run p r m0 orc n s
      f.err = none ∧ ((f.tail = none ∧ Q f) ∨ (f.tail = some nm ∧ Pn (resume f))) := by
  intro s hs
  have h := h4 _ (hP s hs)
  show (run p r m0 orc n s).err = none ∧ _
  rw [run_at r hrNum hrRet]
  obtain ⟨he, hc⟩ := h
  refine ⟨he, ?_⟩
  rcases hc with ⟨ht, hq⟩ | ⟨ht, hq⟩
  · exact Or.inl ⟨ht, hQ _ hq⟩
  · exact Or.inr ⟨ht, hPn _ hq⟩

theorem clause_at_last (r : Region) (hF : Fix (swap 4 r)) (hrNum : r ≠ rNum) (hrRet : r ≠ rRet)
    (p : Array Instr) (n : Nat) (m0 : Addr Int → Cell W32 Int) (orc : Nat → Bool)
    (P Q : CS → Prop) (hP : ∀ s, P s → P ((swap 4 r).state s)) (hQ : ∀ f, Q f → Q ((swap 4 r).state f))
    (h4 : ∀ s, P s → let f := run p 4 ((swap 4 r).mem m0) orc n s
      f.err = none ∧ f.tail = none ∧ Q f) :
    ∀ s, P s → let f := run p r m0 orc n s
      f.err = none ∧ f.tail = none ∧ Q f := by
  intro s hs
  have h := h4 _ (hP s hs)
  show (run p r m0 orc n s).err = none ∧ _
  rw [run_at r hrNum hrRet]
  exact ⟨h.1, h.2.1, hQ _ h.2.2⟩

/-! ## The chain -/

theorem fix7 : Fix (swap 4 7) := fix_swap 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem fix8 : Fix (swap 4 8) := fix_swap 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem fix9 : Fix (swap 4 9) := fix_swap 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

section Chain
variable (env : Key → W32) (σ : Nat → Int) (c : Nat) (inp : Nat → Byte)

/-- The windows chain, each link at its own rodata region. -/
def specsR : List Spec :=
  [ ⟨⟨"hashtree_sha256_avx512_x16", p512, 7, Hashtree.Proofs.Avx512X16WLoop.steps⟩,
      (fun s => s = mapState env σ entryWin), PostLink σ c inp DW⟩,
    ⟨⟨"hashtree_sha256_avx2_x8", p8, 8, fun c => s8 (c % 16)⟩, P8 σ c inp, PostLink σ c inp DW⟩,
    ⟨⟨"hashtree_sha256_avx_x4", p4, 4, fun c => s4 (c % 8)⟩, P4 σ c inp, PostLink σ c inp DW⟩,
    ⟨⟨"hashtree_sha256_avx_x1", p1, 9, fun c => Hashtree.Proofs.WinAvxX1W.steps (c % 4)⟩,
      P1 σ c inp, PostLink σ c inp DW⟩ ]

theorem P8_ren (s : CS) (h : P8 σ c inp s) : P8 σ c inp ((swap 4 8).state s) := by
  obtain ⟨e, hp⟩ := h; exact ⟨e, preLink_ren fix8 e σ c _ _ inp DW U s hp⟩
theorem P4_ren (r : Region) (hF : Fix (swap 4 r)) (s : CS) (h : P4 σ c inp s) : P4 σ c inp ((swap 4 r).state s) := by
  obtain ⟨e, hp⟩ := h; exact ⟨e, preLink_ren hF e σ c _ _ inp DW U s hp⟩
theorem P1_ren (s : CS) (h : P1 σ c inp s) : P1 σ c inp ((swap 4 9).state s) := by
  obtain ⟨e, hp⟩ := h; exact ⟨e, preLink_ren fix9 e σ c _ _ inp DW U s hp⟩
theorem P8_ren7 (s : CS) (h : P8 σ c inp s) : P8 σ c inp ((swap 4 7).state s) := by
  obtain ⟨e, hp⟩ := h; exact ⟨e, preLink_ren fix7 e σ c _ _ inp DW U s hp⟩

/-- **Every link of the windows chain, at its own region, meets its obligation.** -/
theorem win_KSpecC_regions (hT8 : TurnOut8W) (hT8L : TurnOut8WLast) (hT4 : TurnOut4W) (hT4L : TurnOut4WLast)
    (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw512 : WfMemAtW 7 Hashtree.Kernels.X86Win.Avx512X16.rodata [] env σ m0)
    (hw8 : WfMemAtW 8 rodata8 [] env σ m0) (hw4 : WfMemW rodata4W [] env σ m0)
    (hw1 : WfMemAtW 9 Hashtree.Kernels.X86Win.AvxX1.rodata [] env σ m0)
    (hc : σ 2 = c) (habi : σ 9 % 16 = 8)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    KSpecC m0 orcC c (specsR env σ c inp) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- avx512_x16 at region 7
    let m7 := (swap 4 7).mem m0
    let e7 := envSwap env σ m7
    have hc512 := clause512 e7 σ m7 orcC c inp (Hashtree.Proofs.WinChainAll.wf_env _ env e7 σ m7
      (swap_mem_wf 7 fix7 _ env σ m0 hw512)) (envSwap_mem env σ m7) hc
      (swap_mem_in 7 fix7 m0 σ inp hin)
    exact clause_at 7 fix7 (by decide) (by decide) p512 (Hashtree.Proofs.Avx512X16WLoop.steps c) m0 orcC
      (fun s => s = mapState env σ entryWin) (fun s => s = mapState e7 σ entryWin)
      (PostLink σ c inp DW) (P8 σ c inp) "hashtree_sha256_avx2_x8"
      (fun s hs => by rw [hs, state_entryWin fix7, mapState_envSwap])
      (fun f hf => postLink_ren fix7 σ c inp DW f hf) (P8_ren7 σ c inp) hc512
  · -- avx2_x8 at region 8
    exact clause_at 8 fix8 (by decide) (by decide) p8 (s8 (c % 16)) m0 orcC
      (P8 σ c inp) (P8 σ c inp) (PostLink σ c inp DW) (P4 σ c inp) "hashtree_sha256_avx_x4"
      (P8_ren σ c inp) (fun f hf => postLink_ren fix8 σ c inp DW f hf) (P4_ren σ c inp 8 fix8)
      (clause8 env σ ((swap 4 8).mem m0) orcC c inp hT8 hT8L
        (swap_mem_wf 8 fix8 _ env σ m0 hw8) habi (swap_mem_in 8 fix8 m0 σ inp hin))
  · -- avx_x4 at region 4
    exact clause4 env σ m0 orcC c inp hT4 hT4L hw4 habi hin
  · -- avx_x1 at region 9
    exact clause_at_last 9 fix9 (by decide) (by decide) p1 (Hashtree.Proofs.WinAvxX1W.steps (c % 4)) m0 orcC
      (P1 σ c inp) (PostLink σ c inp DW) (P1_ren σ c inp) (fun f hf => postLink_ren fix9 σ c inp DW f hf)
      (clause1 env σ ((swap 4 9).mem m0) orcC c inp (swap_mem_wf 9 fix9 _ env σ m0 hw1)
        (swap_mem_in 9 fix9 m0 σ inp hin))

/-- **The windows chain from the wrapper call state, each link at its own rodata region**: no
model error, no pending tail, halted, all `c` output blocks correct, the footprint inside the
output and the 1296-byte frame below the return marker, the Win64 callee-saved registers and
`rsp` restored.  Conditional only on R2c's output contracts of the two W-mode loops. -/
theorem win_chain_correct_regions (hT8 : TurnOut8W) (hT8L : TurnOut8WLast) (hT4 : TurnOut4W)
    (hT4L : TurnOut4WLast) (m0 : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw512 : WfMemAtW 7 Hashtree.Kernels.X86Win.Avx512X16.rodata [] env σ m0)
    (hw8 : WfMemAtW 8 rodata8 [] env σ m0) (hw4 : WfMemW rodata4W [] env σ m0)
    (hw1 : WfMemAtW 9 Hashtree.Kernels.X86Win.AvxX1.rodata [] env σ m0)
    (hc : σ 2 = c) (habi : σ 9 % 16 = 8)
    (hin : ∀ o : Nat, m0 ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0) :
    let f := chainRun m0 orcC c (specsR env σ c inp) (mapState env σ entryWin)
    f.err = none ∧ f.tail = none ∧ PostLink σ c inp DW f := by
  have h := chain_sound m0 orcC c (specsR env σ c inp) (mapState env σ entryWin)
    (win_KSpecC_regions env σ c inp hT8 hT8L hT4 hT4L m0 orcC hw512 hw8 hw4 hw1 hc habi hin) rfl
  obtain ⟨herr, htl, hpost⟩ := h
  refine ⟨herr, htl, ?_⟩
  rcases hpost with h | h | h | h <;> exact h

end Chain

end Hashtree.Proofs.WinChainRegions
