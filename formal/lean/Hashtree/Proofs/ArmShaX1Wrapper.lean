import Hashtree.Proofs.ArmShaX1Exit

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# The `sha_x1` leg at the wrapper entry: the environment bridge and #79 wrapper

`ArmShaX1Exit.sha_x1_run_exit_sp_mem0` proves the kernel leg from the symbolic entry state
`retOff 1 (mapState env0 σ (entryS sp0))`.  This module supplies the concrete environment `env0`
that makes that state *equal* to the wrapper's call entry `shaEntry count sp0` (junk registers
and vector lanes are the env choice; the symbol values are `σ 0 = σ 1 = 0`, `σ 2 = count`),
and feeds the result to `ArmCall.wrapper_sha_of_run` (upstream #79 shape, `sha_x1` at the
unmoved `SP`).
-/

open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun Hashtree.Asm.ArmRename
  Hashtree.Asm.ArmRet Hashtree.Asm.ArmSym Hashtree.Asm.ArmCall

namespace Hashtree.Proofs.ArmShaX1

open Hashtree.Gen.ArmShaX1P

/-- The concrete environment matching the wrapper's `entry` state: numbered variable keys are
decoded from the `gId`/`vId` numbering (junk GPR values, caller's vector register contents),
and memory keys re-read from the concrete initial memory `m0`. -/
def bridgeEnv (σ : Nat → Int) (m0 : Addr Int → Cell W32 Int) : Key → W32
  | .n i =>
      if i < 64 then
        if i % 2 = 0 then BitVec.ofNat 32 (0x1000 + i / 2)
        else BitVec.ofNat 32 (0x2000 + i / 2)
      else if 100 ≤ i ∧ i < 612 then
        BitVec.ofNat 32 (0x51000000 + 256 * ((i - 100) / 16) + (i - 100) % 16)
      else 0
  | .m r off => cellX (m0 ⟨r, off.eval σ⟩)

/-- The symbolic entry state at the concrete environment is exactly the wrapper's sha call
entry: `x0/x1/x2` from `σ 0/σ 1/σ 2`, `x30 = <rRet,1>` from `retOff 1`, `SP = <rStack,sp0>`,
junk GPR/vector values from `bridgeEnv`. -/
theorem entry_bridge (m0 : Addr Int → Cell W32 Int) (σ : Nat → Int)
    (sp0 : Int) (count : Nat)
    (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 0) (hσ2 : σ 2 = (count : Int)) :
    retOff 1 (mapState (bridgeEnv σ m0) σ (entryS sp0)) = shaEntry count sp0 := by
  have h32 : List.range 32 =
      [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := by
    decide
  have h16 : List.range 16 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := by decide
  simp [mapState, entryS, retOff, shaEntry, setRet, entry, State.setG,
    bridgeEnv, mapVal, E.eval, Hashtree.Asm.mapAddr,
    Lin.eval, Lin.sym, Lin.ofInt, dotC, sOut, sIn, sCnt, gId, vId, h32, h16,
    hσ0, hσ1, hσ2, Int_ofInt]
  decide

/-- The #79 `sha_x1` leg, from the wrapper's own entry state: if the program list contains the
model's `sha_x1` stream at region 4, the concrete memory `m0` is `Mem0Rel`-related to
`mem0s 4 rodata` under `bridgeEnv`, and the symbolic environment fixes `σ 0 = σ 1 = 0`,
`σ 2 = 2` (so `count = 2`), then the wrapper path `BL sha_x1; RET` completes with `SP` back at
`sp0`. -/
theorem sha_x1_wrapper_79 (progs : List Prog) (m0 : Addr Int → Cell W32 Int)
    (σ : Nat → Int) (count : Nat) (sp0 : Int) (sha : Prog)
    (hf : progs.find? (·.name = "hashtree_sha256_sha_x1") = some sha)
    (hcode : sha.code = Hashtree.Kernels.Arm.ShaX1.prog)
    (hro : sha.ro = 4)
    (h0 : Mem0Rel (bridgeEnv σ m0) σ
      (mem0s 4 Hashtree.Kernels.Arm.ShaX1.rodata) m0)
    (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 0) (hσ : σ 2 = (2 : Int))
    (hcount : count = 2) (hsp : sp0 % 16 = 0) :
    ∃ sf, runCall progs shaniPath rNum m0 fuel 1 2 (entry count sp0) = sf ∧
      sf.err = none ∧ sf.halted = true ∧ sf.tail = none ∧
      sf.getG 31 = .ptr ⟨rStack, sp0⟩ := by
  let sc : CS := run Hashtree.Kernels.Arm.ShaX1.prog 4 m0 (fun _ => false) fuel
    (retOff 1 (mapState (bridgeEnv σ m0) σ (entryS sp0)))
  have hfin : ShaX1Exit sp0 sc := by
    simpa only [sc] using
      sha_x1_run_exit_sp_mem0 (bridgeEnv σ m0) σ m0 (fun _ => false) sp0 h0 hσ hsp
  have hentry : shaEntry count sp0 = retOff 1 (mapState (bridgeEnv σ m0) σ (entryS sp0)) := by
    rw [hcount]
    exact (entry_bridge m0 σ sp0 2 hσ0 hσ1 hσ).symm
  have hrun : run sha.code sha.ro m0 (fun _ => false) fuel (shaEntry count sp0) = sc := by
    rw [hcode, hro, hentry]
  exact wrapper_sha_of_run progs m0 fuel count sp0 sha sc hf hrun hfin

end Hashtree.Proofs.ArmShaX1
