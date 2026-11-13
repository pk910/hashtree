import Hashtree.Proofs.ArmWrapper82

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# The AArch64 wrapper at the top level: dispatch on the `hasShani` flag

`Hashtree/Asm/ArmCall.lean` models the wrapper's two paths as `shaniPath` / `neonPath`
(upstream #79); `ArmCall82` adds the per-branch #82 streams.  `ArmShaX1Wrapper` proves the
#79 `sha_x1` leg and `ArmWrapper82` the #82 legs, each from its kernel's contract.  This module
composes the legs the way the real wrapper does: `MOVBU ·hasShani(SB)` selects the path, and
whichever path runs, the wrapper returns with `SP` back at the entry value.  `pickArm` mirrors
`WrapperAmd64.pick` (the branch instruction itself is not modelled, as on x86); the kernel
contracts stay hypotheses where they are not yet proved (`neon_x4 -> neon_x1`).  The `sha_x1`
legs are discharged below from the kernel proofs.

For #82 the shared `ADD $2048, RSP` runs before the branch.  Its seam is explicit, not an
equality of pcs: `renum_addi_shaWrap82` executes the `ADD` from `entry count sp0` and renumbers
to the leg convention (`pc = 0`), giving `shaWrap82 count sp0`; both #82 leg streams start
there (`shaniPath82`, `neonPath82`), with return marker `1` at the shared `done:` `SUB`.
-/

namespace Hashtree.Proofs.ArmWrapper

open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun Hashtree.Asm.ArmSym
  Hashtree.Asm.ArmCall Hashtree.Asm.ArmCall82 Hashtree.Proofs.ArmShaX1

/-- The kernel the wrapper's `hasShani` flag selects. -/
inductive ArmKern where
  | shani
  | neon
  deriving DecidableEq, Repr

/-- The wrapper's branch on `MOVBU ·hasShani(SB)`: `true` runs the `sha_x1` path.  The branch
instructions (`CBNZ` / `JMP`) are not modelled, as with `WrapperAmd64.pick`; the per-path
streams absorb them. -/
def pickArm (hasShani : Bool) : ArmKern := if hasShani then .shani else .neon

theorem pickArm_true : pickArm true = .shani := rfl
theorem pickArm_false : pickArm false = .neon := rfl

/-- The #79 wrapper stream for the selected kernel. -/
def path79 : ArmKern → Array WInstr
  | .shani => shaniPath
  | .neon => neonPath

/-- The #82 wrapper stream for the selected kernel, after the shared `ADD $2048` (see
`renum_addi_shaWrap82`). -/
def path82 : ArmKern → Array WInstr
  | .shani => shaniPath82
  | .neon => neonPath82

/-- Callee-chain hops: the `sha_x1` leg is one call; the NEON leg is the `neon_x4 -> neon_x1`
chain, so it keeps the caller's budget. -/
def hopsOf : ArmKern → Nat → Nat
  | .shani, _ => 1
  | .neon, hops => hops

/-- Wrapper steps of the #79 stream (`BL; RET` vs `ADD; BL; SUB; RET`). -/
def steps79 : ArmKern → Nat
  | .shani => 2
  | .neon => 4

/-- Wrapper steps of the #82 stream after the shared `ADD` (`BL; SUB; RET`). -/
def steps82 : ArmKern → Nat
  | .shani => 3
  | .neon => 3

/-- The wrapper postcondition: clean return with `SP` back at the entry value. -/
def Post (sf : CS) (sp0 : Int) : Prop :=
  sf.err = none ∧ sf.halted = true ∧ sf.tail = none ∧ sf.getG 31 = .ptr ⟨rStack, sp0⟩

/-- The #79 leg contract: the selected stream, run from the wrapper entry, satisfies `Post`. -/
def Leg79 (progs : List Prog) (k : ArmKern) (m0 : Addr Int → Cell W32 Int)
    (fuel hops count : Nat) (sp0 : Int) : Prop :=
  ∃ sf, runCall progs (path79 k) rNum m0 fuel (hopsOf k hops) (steps79 k)
      (entry count sp0) = sf ∧ Post sf sp0

/-- The #82 leg contract: the selected stream, run from the post-`ADD` state `shaWrap82`,
satisfies `Post`. -/
def Leg82 (progs : List Prog) (k : ArmKern) (m0 : Addr Int → Cell W32 Int)
    (fuel hops count : Nat) (sp0 : Int) : Prop :=
  ∃ sf, runCall progs (path82 k) rNum m0 fuel (hopsOf k hops) (steps82 k)
      (shaWrap82 count sp0) = sf ∧ Post sf sp0

/-- **#79 top level.**  With both legs' contracts, the wrapper is correct whichever way
`hasShani` dispatches: the run uses the selected stream and finishes with `SP = sp0`. -/
theorem wrapper_arm64_79 (progs : List Prog) (m0 : Addr Int → Cell W32 Int)
    (fuel hops count : Nat) (sp0 : Int) (hasShani : Bool)
    (hsha : Leg79 progs .shani m0 fuel hops count sp0)
    (hneon : Leg79 progs .neon m0 fuel hops count sp0) :
    Leg79 progs (pickArm hasShani) m0 fuel hops count sp0 := by
  cases hasShani
  · rw [pickArm_false]
    simpa only [Leg79, path79, hopsOf, steps79] using hneon
  · rw [pickArm_true]
    simpa only [Leg79, path79, hopsOf, steps79] using hsha

/-- **#82 top level.**  The shared `ADD $2048` is executed from the wrapper entry and the pc is
renumbered to the leg convention (`renum_addi_shaWrap82`); then the selected per-branch stream
runs, whose shared `done:` `SUB $2048` restores `SP = sp0`. -/
theorem wrapper_arm64_82 (progs : List Prog) (m0 : Addr Int → Cell W32 Int)
    (fuel hops count : Nat) (sp0 : Int) (hasShani : Bool)
    (hsha : Leg82 progs .shani m0 fuel hops count sp0)
    (hneon : Leg82 progs .neon m0 fuel hops count sp0) :
    ∃ sf, runCall progs (path82 (pickArm hasShani)) rNum m0 fuel
        (hopsOf (pickArm hasShani) hops) (steps82 (pickArm hasShani))
        (renum (Arm.exec rNum m0 (fun _ => false) (.addi 31 31 2048) (entry count sp0))) = sf ∧
      Post sf sp0 := by
  rw [renum_addi_shaWrap82]
  cases hasShani
  · rw [pickArm_false]
    simpa only [Leg82, path82, hopsOf, steps82] using hneon
  · rw [pickArm_true]
    simpa only [Leg82, path82, hopsOf, steps82] using hsha

/-! ## Discharging the legs -/

/-- #79 `sha_x1` leg, from the proved kernel composition (`sha_x1_wrapper_79`). -/
theorem leg79_shani (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (σ : Nat → Int)
    (count : Nat) (sp0 : Int) (sha : Prog)
    (hf : progs.find? (·.name = "hashtree_sha256_sha_x1") = some sha)
    (hcode : sha.code = Hashtree.Kernels.Arm.ShaX1.prog)
    (hro : sha.ro = 4)
    (h0 : Mem0Rel (bridgeEnv σ m0) σ (mem0s 4 Hashtree.Kernels.Arm.ShaX1.rodata) m0)
    (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 0) (hσ : σ 2 = (2 : Int))
    (hcount : count = 2) (hsp : sp0 % 16 = 0) :
    Leg79 progs .shani m0 fuel 1 count sp0 :=
  sha_x1_wrapper_79 progs m0 σ count sp0 sha hf hcode hro h0 hσ0 hσ1 hσ hcount hsp

/-- #79 NEON leg, from the `neon_x4 -> neon_x1` chain contract (`wrapper_neon`). -/
theorem leg79_neon (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (fuel hops : Nat)
    (count : Nat) (sp0 : Int) (sc : CS) (path : List String)
    (hsc : runChain progs m0 fuel hops "hashtree_sha256_neon_x4" (neonEntry count sp0)
      = (sc, path))
    (herr : sc.err = none) (hHalt : sc.halted = true) (hTail : sc.tail = none)
    (h30 : sc.getG 30 = .ptr ⟨rRet, (2 : Int)⟩)
    (h31 : sc.getG 31 = .ptr ⟨rStack, sp0 + 2048⟩)
    (hgl : 31 < sc.gpr.length) :
    Leg79 progs .neon m0 fuel hops count sp0 :=
  wrapper_neon progs m0 fuel hops count sp0 sc path hsc herr hHalt hTail h30 h31 hgl

/-- #82 `sha_x1` leg, from the proved kernel composition (`sha_x1_wrapper_82`): the entry is
the post-`ADD` state `shaWrap82`. -/
theorem leg82_shani (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (σ : Nat → Int)
    (count : Nat) (sp0 : Int) (sha : Prog)
    (hf : progs.find? (·.name = "hashtree_sha256_sha_x1") = some sha)
    (hcode : sha.code = Hashtree.Kernels.Arm.ShaX1.prog)
    (hro : sha.ro = 4)
    (h0 : Mem0Rel (bridgeEnv σ m0) σ (mem0s 4 Hashtree.Kernels.Arm.ShaX1.rodata) m0)
    (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 0) (hσ : σ 2 = (2 : Int))
    (hcount : count = 2) (hsp : sp0 % 16 = 0) :
    Leg82 progs .shani m0 fuel 1 count sp0 :=
  sha_x1_wrapper_82 progs m0 σ count sp0 sha hf hcode hro h0 hσ0 hσ1 hσ hcount hsp

/-- #82 NEON leg, from the `neon_x4 -> neon_x1` chain contract after the shared `ADD`
(`wrapper_neon82`). -/
theorem leg82_neon (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (fuel hops : Nat)
    (count : Nat) (sp0 : Int) (sc : CS) (path : List String)
    (hsc : runChain progs m0 fuel hops "hashtree_sha256_neon_x4" (shaEntry82 count sp0)
      = (sc, path))
    (herr : sc.err = none) (hHalt : sc.halted = true) (hTail : sc.tail = none)
    (h30 : sc.getG 30 = .ptr ⟨rRet, (1 : Int)⟩)
    (h31 : sc.getG 31 = .ptr ⟨rStack, sp0 + 2048⟩)
    (hgl : 31 < sc.gpr.length) :
    Leg82 progs .neon m0 fuel hops count sp0 :=
  wrapper_neon82 progs m0 fuel hops count sp0 sc path hsc herr hHalt hTail h30 h31 hgl

end Hashtree.Proofs.ArmWrapper
