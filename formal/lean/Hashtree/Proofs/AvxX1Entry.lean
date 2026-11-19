import Hashtree.Proofs.AvxX1WAt
import Hashtree.Proofs.AvxX1Prefix
import Hashtree.Proofs.AvxX4Entry
import Hashtree.Proofs.X86Chain
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# Entry bridge from a tail call into `hashtree_sha256_avx_x1`

A tail call arrives with the x1 kernel's entry register shape but with the caller's flags
(`X86Chain.resume` clears pc/halted/tail only).  `AvxX1Prefix.run_from_flag_entry` removes
the flags after the eight-instruction prefix, so `correctWAt` applies to the flagged state.
This is the x1 end of every entry bridge in the chain.
-/

namespace Hashtree.Proofs.AvxX1W
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW Hashtree.Kernels.X86.AvxX1
open Hashtree.Proofs.WrapperAmd64
open Hashtree.Proofs.AvxX4Small
open Hashtree.Proofs.X86Chain
open Hashtree.Gen.AvxX1LW
open Hashtree.Spec
open Hashtree.Asm.X86Ren
open Hashtree.Asm.X86Region
open Hashtree.Proofs.ShaniW (OutOk RegsOk)

/-- `rsp` is a pointer in `entryW` (`rbx` is `entryW.gpr[3]`, etc.; here only `rsp`). -/
theorem entryW_g4 : entryW.gpr[4]? = some (.ptr ⟨rStack, sAt 0⟩) := by decide +kernel

theorem entryW_getG4 : entryW.getG 4 = .ptr ⟨rStack, sAt 0⟩ := getG_of _ _ _ entryW_g4

theorem entryW_len : entryW.gpr.length = 16 := by decide +kernel

theorem mapState_entryW_g4 (env : Key → W32) (σ : Nat → Int) :
    (mapState env σ entryW).getG rsp = .ptr ⟨rStack, σ 9⟩ := by
  rw [getG_hom, show entryW.getG rsp = .ptr ⟨rStack, sAt 0⟩ from entryW_getG4]
  simp [mapVal, mapAddr, sAt_eval]

theorem mapState_entryW_len (env : Key → W32) (σ : Nat → Int) :
    rsp < (mapState env σ entryW).gpr.length := by
  simp [mapState, entryW_len]
  decide

theorem steps_ge_8 (c : Nat) : 8 ≤ steps c := by
  unfold steps NP
  split <;> omega

/-- **avx_x1 at an arbitrary region from a *flagged* entry state.**  Same conclusion as
`correctWAt`, but the initial state may carry any flags: the prefix discards them. -/
theorem correctWAt_entry (c : Nat) (inp : Nat → Byte) (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (r : Region)
    (hrNum : r ≠ rNum) (hrIn : r ≠ rIn) (hrOut : r ≠ rOut) (hrStack : r ≠ rStack)
    (hrG : r ≠ rG) (hrRet : r ≠ rRet)
    (hw : WfMemAtW r rodata [] env0 σ mem0c)
    (he : EnvMem env0 σ ((swap 4 r).mem mem0c))
    (hc : σ 2 = c)
    (hin : ∀ o : Nat, (swap 4 r).mem mem0c ⟨rIn, σ 0 + o⟩ = .dat ((inp o).zeroExtend 32) 0)
    (fl : Option (Int × Int)) :
    let fin := run prog r mem0c orcC (steps c) {mapState env0 σ entryW with flags := fl}
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧
      InRange (σ 9) (σ 1) (32 * c) fin.mem ∧ OutOk inp (σ 1) c fin.mem ∧
      RegsOk env0 σ fin := by
  have hOut : (swap 4 r).f rOut = rOut :=
    swap_fixes 4 r rOut (by decide) (Ne.symm hrOut)
  have hIn : (swap 4 r).f rIn = rIn :=
    swap_fixes 4 r rIn (by decide) (Ne.symm hrIn)
  have hStack : (swap 4 r).f rStack = rStack :=
    swap_fixes 4 r rStack (by decide) (Ne.symm hrStack)
  have hG : (swap 4 r).f rG = rG :=
    swap_fixes 4 r rG (by decide) (Ne.symm hrG)
  have hNum : (swap 4 r).f rNum = rNum := swap_rNum 4 r (by decide) hrNum
  have hpost := correctWAt c inp env0 σ mem0c orcC r hrNum hrIn hrOut hrStack hrG hrRet hw he hc hin
  dsimp only at hpost
  have hentry : (swap 4 r).state (mapState env0 σ entryW) = mapState env0 σ entryW :=
    state_entryW (swap 4 r) hNum hIn hOut hStack hG env0 σ
  rw [hentry] at hpost
  have h8 : run prog r mem0c orcC (steps c) {mapState env0 σ entryW with flags := fl}
      = run prog r mem0c orcC (steps c) (mapState env0 σ entryW) :=
    run_from_flag_entry r mem0c orcC (mapState env0 σ entryW) fl rfl rfl ⟨rStack, σ 9⟩
      (mapState_entryW_g4 env0 σ) (mapState_entryW_len env0 σ) (steps c) (steps_ge_8 c)
  dsimp only
  rw [h8]
  exact hpost

/-- The state handed to x1 by the x4 small-count tail is the plain entry state up to flags. -/
theorem resume_KSm (env : Key → W32) (σ : Nat → Int) :
    resume (mapState env σ KSm) =
      {mapState env σ entryW with flags := (mapState env σ KSm).flags} := by
  simp only [resume, mapState, KSm_pc, KSm_halted, KSm_tail, KSm_mem, KSm_err, KSm_gpr, KSm_vr,
    entryW]

end Hashtree.Proofs.AvxX1W
