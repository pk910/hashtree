import Hashtree.Proofs.AvxX1Agree
import Hashtree.Proofs.AvxX4ToX1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# The x4 -> x1 chain edge at the dead-register cut

`hashtree_sha256_avx_x4` has two tail calls into `hashtree_sha256_avx_x1`:

* the early exit `0 < c < 4` (eight instructions, `AvxX4Small.KSm`).  Its cut is the x1 entry
  state up to flags (`AvxX1W.resume_KSm`), so it satisfies the dead-register agreement
  trivially.  This module closes that edge with the bridge of `Hashtree.Proofs.AvxX1Agree`
  instead of the exact-shape x1 pre of `AvxX4ToX1`: the x1 link's pre is
  `AgreeOn [0, 1, 9] s {mapState env' σ entryW with flags := s.flags}`, so any future caller
  that only agrees outside `{rax, rcx, r9}` can be composed the same way.
* the all-count W-mode exit cut (`AvxX4LoopWEntry.K201W`, `c >= 4`).  Its state is
  `fr M' (mapState e' σ' K201W)`: the three caller-saved registers `rax`, `rcx`, `r9` carry
  kernel-specific values (the blocker recorded in `formal/notes/R2.md`) *and* its write log is
  the exit slice's own log extended by `M'`, which is nonempty.  `AgreeOn` requires the write
  logs to be equal, so the unframed pre
  `AgreeOn [0, 1, 9] s {mapState env' σ entryW with flags := s.flags}` is *false* at that cut
  (`agreeOn_mem_nil` below: an agreeing state must have an empty log, and the cut's is not).
  Closing that edge needs the x1 link stated at the log-framed entry `fr L (entryW)` with a
  framed bridge (`X86Frame.run_fr` plus a `fr` lift of `AgreeOn`); it is not part of this
  module.
-/

namespace Hashtree.Proofs.AvxX4X1Agree

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.X86Chain
open Hashtree.Spec
open Hashtree.Kernels.X86.AvxX4
open Hashtree.Proofs.AvxX4Small (KSm KSm_err KSm_tail orcK small_prefix)
open Hashtree.Proofs.AvxX4ToX1 (x4spec x4link x1link entry_pc_zero wfMemAtW_nil_env)
open Hashtree.Proofs.AvxX1W (steps resume_KSm InRange envAbs_envMem)
open Hashtree.Proofs.ShaniW (OutOk RegsOk)
open Hashtree.Proofs.AvxX1Agree (correctWAt_agree)

/-- `AgreeOn` holds of a state and itself. -/
theorem agreeOn_self {S : List Nat} {s : CS} : AgreeOn S s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ _ => rfl, rfl⟩

/-- A state that agrees with an empty-log state has an empty write log.  This is the `mem`
field of `AgreeOn`, and it is what an unframed hand-off from a nonempty log cannot satisfy. -/
theorem agreeOn_mem_nil {S : List Nat} {s1 s2 : CS} (h : AgreeOn S s1 s2)
    (h2 : s2.mem = []) : s1.mem = [] := by
  rw [h.mem, h2]

/-- The early-exit cut, handed to x1.  `resume_KSm` makes the cut literally the flagged entry
state, so it agrees on every field (in particular on the empty write log). -/
theorem ksm_agree (env' : Key → W32) (σ : Nat → Int) :
    AgreeOn [0, 1, 9] (resume (mapState env' σ KSm))
      {mapState env' σ entryW with flags := (resume (mapState env' σ KSm)).flags} := by
  rw [resume_KSm env' σ]
  exact agreeOn_self

/-- The x1 link entered through the dead-register hand-off.  The pre is the agreement with the
flagged entry state outside `{rax, rcx, r9}`; the post is the x1 all-count post. -/
def x1specA (c : Nat) (inp : Nat → Byte) (env' : Key → W32) (σ : Nat → Int)
    (r : Region) : Spec where
  link := x1link c r
  pre := fun s => AgreeOn [0, 1, 9] s {mapState env' σ entryW with flags := s.flags}
  post := fun f =>
    InRange (σ 9) (σ 1) (32 * c) f.mem ∧ OutOk inp (σ 1) c f.mem ∧ RegsOk env' σ f

/-- **The x4 -> x1 chain edge, `0 < c < 4`, through the dead-register cut.**  Same statement as
`AvxX4ToX1.x4_small_to_x1`, but the x1 link is entered through `correctWAt_agree`: the x4
early-exit cut satisfies `AgreeOn [0, 1, 9]` against the flagged x1 entry state, and the
bridge carries the x1 postcondition over. -/
theorem x4_small_to_x1_agree (c : Nat) (inp : Nat → Byte) (env0 : Key → W32)
    (σ : Nat → Int) (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r1 : Region)
    (hrNum : r1 ≠ rNum) (hrIn : r1 ≠ rIn) (hrOut : r1 ≠ rOut) (hrStack : r1 ≠ rStack)
    (hrG : r1 ≠ rG) (hrRet : r1 ≠ rRet)
    (hw4 : WfMemW rodata [] env0 σ mem0c)
    (he0 : EnvMem env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (he1 : EnvMem env0 σ ((swap 4 r1).mem mem0c))
    (hc : σ 2 = (c : Int)) (hlt : σ 2 < 4) (hne : σ 2 ≠ 0)
    (hin1 : ∀ o : Nat, (swap 4 r1).mem mem0c ⟨rIn, σ 0 + o⟩ =
      .dat ((inp o).zeroExtend 32) 0) :
    let env' : Key → W32 := envAbs env0 (run prog 4 (mem0sW 4 rodata []) orcK 8 entryW)
    let fin : CS := callChain mem0c orcC c
      [x4spec env0 σ, x1specA c inp env' σ r1] (mapState env0 σ entryW)
    fin.err = none ∧ fin.tail = none ∧ fin.halted = false ∧ fin.pc = 0 ∧
      InRange (σ 9) (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem ∧
      RegsOk env' σ fin := by
  dsimp only
  generalize hR0 : run prog 4 (mem0sW 4 rodata []) orcK 8 entryW = R0
  generalize henv : envAbs env0 R0 = env'
  have hw1' : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env' σ mem0c := by
    have h := wfMemAtW_nil_env r1 Hashtree.Kernels.X86.AvxX1.rodata env0 (envAbs env0 R0)
      σ mem0c hw1
    rwa [henv] at h
  have he1' : EnvMem env' σ ((swap 4 r1).mem mem0c) := by
    have h := envAbs_envMem env0 R0 σ ((swap 4 r1).mem mem0c) he1
    rwa [henv] at h
  have hpre : FirstPre [x4spec env0 σ, x1specA c inp env' σ r1]
      ({mapState env0 σ entryW with pc := 0} : CS) := by
    dsimp only [FirstPre, x4spec]
  have hok : KSpecC mem0c orcC c [x4spec env0 σ, x1specA c inp env' σ r1] := by
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs' : s = {mapState env0 σ entryW with pc := 0} := hs
      subst hs'
      dsimp only [step, x4spec, x1specA, x4link, x1link]
      have hsp := small_prefix env0 σ mem0c orcC hw4 he0 hlt hne
      rw [hR0] at hsp
      rw [henv] at hsp
      have hf : run prog 4 mem0c orcC 8
          ({mapState env0 σ entryW with pc := 0} : CS) = mapState env' σ KSm := by
        rw [entry_pc_zero env0 σ]
        exact hsp
      rw [hf]
      refine ⟨KSm_err, Or.inr ⟨KSm_tail, ?_⟩⟩
      exact ksm_agree env' σ
    · intro s hs
      dsimp only [step, x1specA, x1link]
      have hp := correctWAt_agree c inp env' σ mem0c orcC r1 hrNum hrIn hrOut hrStack hrG
        hrRet hw1' he1' hc hin1 s.flags s hs
      dsimp only at hp
      exact ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  have hchain := chain_sound mem0c orcC c [x4spec env0 σ, x1specA c inp env' σ r1]
    {mapState env0 σ entryW with pc := 0} hok hpre
  dsimp only at hchain
  obtain ⟨herr, _htail, hpost⟩ := hchain
  simp only [ChainPost, x4spec, x1specA] at hpost
  rcases hpost with h | h
  · exact h.elim
  exact ⟨herr, rfl, rfl, rfl, h.1, h.2.1, h.2.2⟩

end Hashtree.Proofs.AvxX4X1Agree
