import Hashtree.Asm.ArmCall
import Hashtree.Asm.ArmRet
import Hashtree.Asm.ArmShiftCall
import Hashtree.Gen.ArmShaX1P.Final

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# `sha_x1`: from the proven tree's final state to the wrapper's exit cut

`Hashtree.Gen.ArmShaX1P.Final.run_final` gives the exact final state of the proven two-block
tree, but that state is the tree's symbolic one (`mapState (E193 env0) σ K193`), entered at
`entryS 0` - `x30 = <rRet,0>`, `SP = <rStack,0>` - while the shipped wrapper's `sha_x1` leg
enters the kernel at `x30 = <rRet,1>` (`ArmCall.shaEntry`; the `BL` resumes at pc 1).

This module does the extraction half only:

* `sha_x1_noTouch` - the shipped stream never touches `x30` (`native_decide`);
* `sha_x1_run_relabeled` - the tree's run restated at `x30 = <rRet,1>`, by `ArmRet.run_retOff`
  (the kernel only tests the *region* of `x30` at `ret`, so the offset is inert);
* `sha_x1_exit` - that run's final state satisfies `ArmCall.ShaX1Exit 0`.

The entry `SP` stays 0: moving it to an arbitrary `sp0` is the stack-shift step (the tree's
stack accesses are the absolute `[-32, 0]` range), not proved here.  The entry-state identity
with `ArmCall.shaEntry` (environment/memory bridge) is likewise left to the driver.
-/

open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun Hashtree.Asm.ArmRename
  Hashtree.Asm.ArmRet Hashtree.Asm.ArmSym

namespace Hashtree.Proofs.ArmShaX1

open Hashtree.Gen.ArmShaX1P

/-- The shipped linux_arm64 `sha_x1` stream never reads or writes `x30`. -/
theorem sha_x1_noTouch :
    Hashtree.Kernels.Arm.ShaX1.prog.all
      (fun i => decide (Hashtree.Asm.ArmRet.NoTouch i)) = true := by
  rw [← Array.all_toList]
  decide

/-- Fuel of the proven two-block tree: the literal of `ArmShaX1P.Final.run_final`. -/
abbrev fuel : Nat := (28 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (2 + (1 + (1 + (3 + (1 + (1 + (2 + (1 + (1 + (2 + (1 + (1 + (11 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (24 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (4 + (1 + (1 + (2 + (1 + (1 + (3 + (1 + (1 + (2 + (1 + (1 + (2 + (1 + (1 + (11 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (12)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The tree's run, entered with the wrapper's return marker `1` in `x30` instead of the tree's
`0`.  Same fuel, same final state modulo the `x30` offset. -/
theorem sha_x1_run_relabeled (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (h0 : Mem0Rel env0 σ (mem0s 4 Hashtree.Kernels.Arm.ShaX1.rodata) mem0c)
    (hσ : σ 2 = 2) :
    run Hashtree.Kernels.Arm.ShaX1.prog 4 mem0c orcC fuel
        (retOff 1 (mapState env0 σ (entryS 0)))
      = retOff 1 (mapState (E193 env0) σ K193) := by
  have hrf := Hashtree.Gen.ArmShaX1P.run_final env0 σ mem0c orcC h0 hσ
  have h30 : (mapState env0 σ (entryS 0)).getG 30 = .ptr ⟨rRet, (0 : Int)⟩ := by
    simp [State.getG, mapState, entryS, List.getD, mapVal, mapAddr, Lin.ofInt, Lin.eval, dotC]
  have hc := run_retOff Hashtree.Kernels.Arm.ShaX1.prog 4 mem0c orcC sha_x1_noTouch fuel
    (mapState env0 σ (entryS 0)) 1 0 h30
  rw [hrf] at hc
  exact hc

/-- The exit cut of the proven tree, at `SP = 0`: clean finish, `x30` back at the wrapper's
resume pc `1`, `SP` where it entered.  This is `ArmCall.ShaX1Exit 0`, the input of
`ArmCall.wrapper_sha_of_run`. -/
theorem sha_x1_exit (env0 : Key → W32) (σ : Nat → Int) :
    Hashtree.Asm.ArmCall.ShaX1Exit 0 (retOff 1 (mapState (E193 env0) σ K193)) := by
  have h30 : (mapState (E193 env0) σ K193).getG 30 = .ptr ⟨rRet, (0 : Int)⟩ := by
    simp [State.getG, mapState, K193, rRet, List.getD, mapVal, mapAddr, Lin.eval, dotC]
  have h31 : (mapState (E193 env0) σ K193).getG 31 = .ptr ⟨rStack, (0 : Int)⟩ := by
    simp [State.getG, mapState, K193, rStack, List.getD, mapVal, mapAddr, Lin.eval, dotC]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [retOff, State.setG, mapState, K193]
  · simp [retOff, State.setG, mapState, K193]
  · simp [retOff, State.setG, mapState, K193]
  · exact getG_retOff_self' 1 _ h30
  · rw [retOff_getG 1 _ 31 (by decide)]
    exact h31

/-- Both halves together, in the shape `ArmCall.wrapper_sha_of_run` consumes: the tree's run at
the wrapper's return marker, and the exit cut of its final state. -/
theorem sha_x1_run_exit (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (h0 : Mem0Rel env0 σ (mem0s 4 Hashtree.Kernels.Arm.ShaX1.rodata) mem0c)
    (hσ : σ 2 = 2) :
    run Hashtree.Kernels.Arm.ShaX1.prog 4 mem0c orcC fuel
          (retOff 1 (mapState env0 σ (entryS 0)))
        = retOff 1 (mapState (E193 env0) σ K193) ∧
      Hashtree.Asm.ArmCall.ShaX1Exit 0 (retOff 1 (mapState (E193 env0) σ K193)) :=
  ⟨sha_x1_run_relabeled env0 σ mem0c orcC h0 hσ, sha_x1_exit env0 σ⟩

/-- Stack-shift step at the entry and through the whole run: entering the tree with `SP = sp0`
(a multiple of 16) is the `sp0`-shift of entering it with `SP = 0`, at the same return marker
`x30 = 1` and with the initial memory shifted by `sp0` on the stack region.  The final states
are related by `ArmShift.Rel sp0` (same registers/vr/mem after the shift, no flag requirement).

The initial memory on the shifted side is `memSh sp0 mem0c`; relating that to `mem0c` is the
memory-footprint step, not proved here. -/
theorem sha_x1_run_shift_sp (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (sp0 : Int)
    (hsp : sp0 % 16 = 0) :
    Hashtree.Asm.ArmShift.Rel sp0
      (run Hashtree.Kernels.Arm.ShaX1.prog 4
          (Hashtree.Asm.ArmShift.memSh sp0 mem0c) orcC fuel
          (retOff 1 (mapState env0 σ (entryS sp0))))
      (run Hashtree.Kernels.Arm.ShaX1.prog 4 mem0c orcC fuel
          (retOff 1 (mapState env0 σ (entryS 0)))) := by
  have hcanon : Hashtree.Kernels.Arm.ShaX1.prog.all Hashtree.Asm.ArmShift.Canon = true := by
    rw [← Array.all_toList]
    decide
  have hrel : Hashtree.Asm.ArmShift.Rel sp0
      (retOff 1 (mapState env0 σ (entryS sp0)))
      (retOff 1 (mapState env0 σ (entryS 0))) := by
    rw [Hashtree.Asm.ArmShift.entryS_map_sh, Hashtree.Asm.ArmShift.retOff_sh]
    exact Hashtree.Asm.ArmShift.rel_sh sp0 _
  exact Hashtree.Asm.ArmShift.run_rel Hashtree.Kernels.Arm.ShaX1.prog 4 orcC mem0c sp0
    (by decide : (4 : Region) ≠ rStack) hsp hcanon fuel hrel

/-- The shift relation composed with the known base run and base exit cut: the run entered at
`SP = sp0` (on the `sp0`-shifted initial memory) satisfies `ShaX1Exit sp0`. -/
theorem sha_x1_run_exit_sp (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (sp0 : Int)
    (h0 : Mem0Rel env0 σ (mem0s 4 Hashtree.Kernels.Arm.ShaX1.rodata) mem0c)
    (hσ : σ 2 = 2) (hsp : sp0 % 16 = 0) :
    Hashtree.Asm.ArmCall.ShaX1Exit sp0
      (run Hashtree.Kernels.Arm.ShaX1.prog 4
          (Hashtree.Asm.ArmShift.memSh sp0 mem0c) orcC fuel
          (retOff 1 (mapState env0 σ (entryS sp0)))) := by
  have hshift := sha_x1_run_shift_sp env0 σ mem0c orcC sp0 hsp
  rw [sha_x1_run_relabeled env0 σ mem0c orcC h0 hσ] at hshift
  exact Hashtree.Asm.ArmShift.ShaX1Exit_shift hshift (sha_x1_exit env0 σ)

end Hashtree.Proofs.ArmShaX1
