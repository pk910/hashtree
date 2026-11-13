import Hashtree.Proofs.AvxX1Entry
import Hashtree.Proofs.AvxX4Entry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# The x4 -> x1 tail-call link, small counts

`AvxX4Small.small_prefix` shows that the x4 kernel with `0 < c < 4` blocks runs eight
instructions and reaches its tail call into `hashtree_sha256_avx_x1`.  This module composes
that link with the x1 all-count contract (`AvxX1W.correctWAt_entry`) in the chain framework
of `X86Chain`: the x4 table lives at region 4 of the shared memory, the x1 table at a fresh
region `r1`, and the x1 link runs on the same memory at its own region.

The result is the `x4 -> x1` entry bridge: for `0 < c < 4` the composed chain returns with
no error and no tail, having written exactly the output bytes and the stack frame, with the
callee-saved registers restored.
-/

namespace Hashtree.Proofs.AvxX4ToX1
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Asm.X86Ren Hashtree.Asm.X86Region
open Hashtree.Proofs.X86Chain
open Hashtree.Spec
open Hashtree.Proofs.AvxX4Small
open Hashtree.Proofs.AvxX1W
open Hashtree.Proofs.ShaniW (OutOk RegsOk)

/-- `WfMemAtW` does not depend on the environment when no cells are pushed (`push = []`):
the only clause that mentions `env` is vacuous. -/
theorem wfMemAtW_nil_env (ro : Region) (rodata : List Nat) (env env' : Key → W32)
    (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (hw : WfMemAtW ro rodata [] env σ m) : WfMemAtW ro rodata [] env' σ m := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  exact ⟨h1, h2, h3, fun k c hk => by simp [plookup] at hk⟩

/-- The x4 link on its early-exit path: eight instructions, then a tail call into x1. -/
def x4link : Link where
  name := "hashtree_sha256_avx_x4"
  prog := Hashtree.Kernels.X86.AvxX4.prog
  ro := 4
  steps := fun _ => 8

/-- The x1 link, started at region `r` for `c` blocks. -/
def x1link (c : Nat) (r : Region) : Link where
  name := "hashtree_sha256_avx_x1"
  prog := Hashtree.Kernels.X86.AvxX1.prog
  ro := r
  steps := fun _ => Hashtree.Proofs.AvxX1W.steps c

/-- The x4 small-count link as a chain spec: starts at the wrapper entry and always tails. -/
def x4spec (env0 : Key → W32) (σ : Nat → Int) : Spec where
  link := x4link
  pre := fun s => s = {mapState env0 σ entryW with pc := 0}
  post := fun _ => False

/-- The x1 link as a chain spec: enters at the x1 entry register shape (up to flags). -/
def x1spec (c : Nat) (inp : Nat → Byte) (env' : Key → W32) (σ : Nat → Int)
    (r : Region) : Spec where
  link := x1link c r
  pre := fun s => ∃ fl, s = {mapState env' σ entryW with flags := fl}
  post := fun f =>
    InRange (σ 9) (σ 1) (32 * c) f.mem ∧ OutOk inp (σ 1) c f.mem ∧ RegsOk env' σ f

/-- The wrapper entry state already has `pc = 0`, so `callChain`'s program-counter reset
changes nothing. -/
theorem entry_pc_zero (env : Key → W32) (σ : Nat → Int) :
    ({mapState env σ entryW with pc := 0} : CS) = mapState env σ entryW := by
  simp [mapState, entryW]

/-- **The x4 -> x1 entry bridge, small counts.**  With the x4 table at region 4 and the x1
table at a fresh region `r1` of one shared memory, the x4 early-exit path (one to three
blocks) tails into x1, and the composed chain returns with the output bytes written, the
stack frame bounded, and the callee-saved registers restored. -/
theorem x4_small_to_x1 (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r1 : Region)
    (hrNum : r1 ≠ rNum) (hrIn : r1 ≠ rIn) (hrOut : r1 ≠ rOut) (hrStack : r1 ≠ rStack)
    (hrG : r1 ≠ rG) (hrRet : r1 ≠ rRet)
    (hw4 : WfMemW Hashtree.Kernels.X86.AvxX4.rodata [] env0 σ mem0c)
    (he0 : EnvMem env0 σ mem0c)
    (hw1 : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env0 σ mem0c)
    (he1 : EnvMem env0 σ ((swap 4 r1).mem mem0c))
    (hc : σ 2 = (c : Int)) (hlt : σ 2 < 4) (hne : σ 2 ≠ 0)
    (hin1 : ∀ o : Nat, (swap 4 r1).mem mem0c ⟨rIn, σ 0 + o⟩ =
      .dat ((inp o).zeroExtend 32) 0) :
    let env' : Key → W32 := envAbs env0 (run Hashtree.Kernels.X86.AvxX4.prog 4
      (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW)
    let fin : CS := callChain mem0c orcC c
      [x4spec env0 σ, x1spec c inp env' σ r1] (mapState env0 σ entryW)
    fin.err = none ∧ fin.tail = none ∧ fin.halted = false ∧ fin.pc = 0 ∧
      InRange (σ 9) (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem ∧
      RegsOk env' σ fin := by
  dsimp only
  generalize hR0 : run Hashtree.Kernels.X86.AvxX4.prog 4
    (mem0sW 4 Hashtree.Kernels.X86.AvxX4.rodata []) orcK 8 entryW = R0
  generalize henv : envAbs env0 R0 = env'
  have hw1' : WfMemAtW r1 Hashtree.Kernels.X86.AvxX1.rodata [] env' σ mem0c := by
    have h := wfMemAtW_nil_env r1 Hashtree.Kernels.X86.AvxX1.rodata env0 (envAbs env0 R0)
      σ mem0c hw1
    rwa [henv] at h
  have he1' : EnvMem env' σ ((swap 4 r1).mem mem0c) := by
    have h := envAbs_envMem env0 R0 σ ((swap 4 r1).mem mem0c) he1
    rwa [henv] at h
  have hpre : FirstPre [x4spec env0 σ, x1spec c inp env' σ r1]
      ({mapState env0 σ entryW with pc := 0} : CS) := by
    dsimp only [FirstPre, x4spec]
  have hok : KSpecC mem0c orcC c [x4spec env0 σ, x1spec c inp env' σ r1] := by
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs' : s = {mapState env0 σ entryW with pc := 0} := hs
      subst hs'
      dsimp only [step, x4spec, x1spec, x4link, x1link]
      have hsp := small_prefix env0 σ mem0c orcC hw4 he0 hlt hne
      rw [hR0] at hsp
      rw [henv] at hsp
      have hf : run Hashtree.Kernels.X86.AvxX4.prog 4 mem0c orcC 8
          ({mapState env0 σ entryW with pc := 0} : CS) = mapState env' σ KSm := by
        rw [entry_pc_zero env0 σ]
        exact hsp
      rw [hf]
      refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
      · show KSm.err = none
        exact KSm_err
      · show KSm.tail = some "hashtree_sha256_avx_x1"
        exact KSm_tail
      · show ∃ fl, resume (mapState env' σ KSm) =
            {mapState env' σ entryW with flags := fl}
        exact ⟨(mapState env' σ KSm).flags, resume_KSm env' σ⟩
    · intro s hs
      obtain ⟨fl, rfl⟩ := hs
      dsimp only [step, x1spec, x1link]
      have hp := correctWAt_entry c inp env' σ mem0c orcC r1
        hrNum hrIn hrOut hrStack hrG hrRet hw1' he1' hc hin1 fl
      dsimp only at hp
      exact ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  have hchain := chain_sound mem0c orcC c [x4spec env0 σ, x1spec c inp env' σ r1]
    {mapState env0 σ entryW with pc := 0} hok hpre
  dsimp only at hchain
  obtain ⟨herr, _htail, hpost⟩ := hchain
  simp only [ChainPost, x4spec, x1spec] at hpost
  rcases hpost with h | h
  · exact h.elim
  exact ⟨herr, rfl, rfl, rfl, h.1, h.2.1, h.2.2⟩

end Hashtree.Proofs.AvxX4ToX1
