import Hashtree.Proofs.ArmShaX1Wrapper

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

/-!
# The #82 wrapper pin: `sha_x1` inside the shared frame

Upstream PR #82 (`fix/arm64-wrapper-sp`) moves the wrapper's `ADD $2048, RSP` before the
hash-impl branch and shares a single `SUB $2048, RSP` at the `done:` epilogue:

```
    MOVBU ·hasShani(SB), check_shani
    ADD  $2048, RSP, RSP
    CBNZ  check_shani, shani
    BL   hashtree_sha256_neon_x4(SB)
    JMP  done
shani:
    BL   hashtree_sha256_sha_x1(SB)
done:
    SUB  $2048, RSP, RSP
    RET
```

Consequences for the model:

* the NEON leg stream is unchanged: `ADD; BL neon_x4; (JMP); SUB; RET` is exactly
  `ArmCall.neonPath` (the jump is the already-decided branch), so `wrapper_neon` and
  `wrapper_neon_of_cut` replay as-is at the #82 shape;
* the `sha_x1` leg now enters with `SP` moved: `ADD; BL sha_x1; SUB; RET`.  The shared `ADD`
  is folded into the leg's entry state, exactly as `exec_addi_entry` computes it, with the pc
  renumbered to 0 so the leg stream `shaniPath82 = [BL; SUB; RET]` starts at 0; its return
  marker `1` is the renumbered index of the shared `done:` (`SUB`) instruction.

This file is a separate pin: `ArmCall`'s #79 definitions (`shaniPath`, `shaEntry`,
`wrapper_sha`, `wrapper_sha_of_run`) are untouched.
-/

namespace Hashtree.Asm.ArmCall82

open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun Hashtree.Asm.ArmCall

/-- The #82 `sha_x1` leg stream, after the shared `ADD $2048` has run:
`BL hashtree_sha256_sha_x1; SUB $2048, RSP; RET`.  The return marker `1` is the renumbered
index of the shared `done:` `SUB`. -/
def shaniPath82 : Array WInstr :=
  #[.call 1 "hashtree_sha256_sha_x1", .ins (.subi 31 31 2048), .ins .ret]

theorem shaniPath82_0 :
    shaniPath82[0]? = some (.call 1 "hashtree_sha256_sha_x1") := by decide
theorem shaniPath82_1 : shaniPath82[1]? = some (.ins (.subi 31 31 2048)) := by decide
theorem shaniPath82_2 : shaniPath82[2]? = some (.ins .ret) := by decide
theorem shaniPath82_size : shaniPath82.size = 3 := by decide

/-- The wrapper state after the shared `ADD $2048` (`exec_addi_entry`, pc renumbered to 0 so
the leg stream indexes from 0).  The NEON leg's `neonPath` starts one instruction earlier and
executes the `ADD` itself; the `sha_x1` leg starts here. -/
def shaWrap82 (count : Nat) (sp0 : Int) : CS :=
  State.setG (entry count sp0) 31 (.ptr ⟨rStack, sp0 + 2048⟩)

/-- The state the #82 wrapper hands `hashtree_sha256_sha_x1`: `SP = sp0 + 2048` and
`x30 = <rRet, 1>` (the shared `done:` resume pc), all else as the wrapper's entry.  This is
`shaEntry` at `sp0 + 2048`. -/
def shaEntry82 (count : Nat) (sp0 : Int) : CS := shaEntry count (sp0 + 2048)

/-- The `BL` into the `sha_x1` kernel leaves the same state as `shaEntry82`. -/
theorem shaEntry82_callee (count : Nat) (sp0 : Int) :
    shaEntry82 count sp0 =
      { setRet (shaWrap82 count sp0) 1 with pc := 0, halted := false, tail := none } := by
  rfl

/-- The shared `ADD` of #82, from the wrapper's entry: it lands in `shaWrap82` (`pc` moved to 1
by `next`, the leg stream renumbers it to 0). -/
theorem exec_addi_shaWrap82 (m0 : Addr Int → Cell W32 Int) (count : Nat) (sp0 : Int) :
    Arm.exec rNum m0 (fun _ => false) (.addi 31 31 2048) (entry count sp0)
      = (shaWrap82 count sp0).next := by
  rw [exec_addi_entry]
  rfl

theorem shaWrap82_halted (count : Nat) (sp0 : Int) : (shaWrap82 count sp0).halted = false := by
  simp [shaWrap82, State.setG, entry]

theorem shaWrap82_pc (count : Nat) (sp0 : Int) : (shaWrap82 count sp0).pc = 0 := by
  simp [shaWrap82, State.setG, entry]

theorem shaWrap82_tail (count : Nat) (sp0 : Int) : (shaWrap82 count sp0).tail = none := by
  simp [shaWrap82, State.setG, entry]

theorem shaWrap82_getG31 (count : Nat) (sp0 : Int) :
    (shaWrap82 count sp0).getG 31 = .ptr ⟨rStack, sp0 + 2048⟩ := by
  unfold shaWrap82
  rw [State.setG, State.getG]
  exact getD_set_self _ 31 _ _ (by simp [entry, List.length_set])

theorem shaWrap82_gpr_length (count : Nat) (sp0 : Int) :
    (shaWrap82 count sp0).gpr.length = 32 := by
  simp [shaWrap82, State.setG, entry, List.length_set, List.length_map, List.length_range]

/-- The stack shift does not change the register-file length. -/
theorem sh_gpr_length (k : Int) (s : CS) :
    (Hashtree.Asm.ArmShift.sh k s).gpr.length = s.gpr.length := by
  simp [Hashtree.Asm.ArmShift.sh, Hashtree.Asm.ArmShift.shLog, List.length_map]

/-- The #82 `sha_x1` path, with the kernel leg as hypothesis.

`hsc` is the `sha_x1` chain from `shaEntry82` (`SP = sp0 + 2048`, `x30 = <rRet,1>`); its `ret`
leaves `x30 = <rRet,1>` and `SP` at the moved entry `SP`.  The wrapper then executes the shared
`SUB $2048; RET`, restoring `SP = sp0`. -/
theorem wrapper_sha82 (progs : List Prog) (m0 : Addr Int → Cell W32 Int) (fuel hops : Nat)
    (count : Nat) (sp0 : Int) (sc : CS) (path : List String)
    (hsc : runChain progs m0 fuel hops "hashtree_sha256_sha_x1" (shaEntry82 count sp0)
      = (sc, path))
    (herr : sc.err = none) (hHalt : sc.halted = true) (hTail : sc.tail = none)
    (h30 : sc.getG 30 = .ptr ⟨rRet, (1 : Int)⟩)
    (h31 : sc.getG 31 = .ptr ⟨rStack, sp0 + 2048⟩)
    (hgl : 31 < sc.gpr.length) :
    ∃ sf, runCall progs shaniPath82 rNum m0 fuel hops 3 (shaWrap82 count sp0) = sf ∧
      sf.err = none ∧ sf.halted = true ∧ sf.tail = none ∧
      sf.getG 31 = .ptr ⟨rStack, sp0⟩ := by
  let E : CS := shaWrap82 count sp0
  let C : CS := { setRet E 1 with halted := true, tail := some "hashtree_sha256_sha_x1" }
  let D : CS := { sc with pc := 1, halted := false, tail := none }
  let a31 : Addr Int := ⟨rStack, sp0 + 2048⟩
  let F : CS := (State.setG D 31 (.ptr (a31.plusI (-((2048 : Nat) : Int))))).next
  let G : CS := { F with halted := true }
  have hE : runW shaniPath82 rNum m0 (fun _ => false) 1 E = C := by
    rw [runW_one shaniPath82 rNum m0 (fun _ => false) E (.call 1 "hashtree_sha256_sha_x1")
      (by rfl) shaniPath82_0]
    simp only [execW, show E.halted = false from rfl]
    rfl
  have hsha : ({ C with pc := 0, halted := false, tail := none } : CS)
      = shaEntry82 count sp0 := by
    rw [shaEntry82_callee]
  have step1 : runCall progs shaniPath82 rNum m0 fuel hops 3 E
      = runCall progs shaniPath82 rNum m0 fuel hops 2 D := by
    change runCall progs shaniPath82 rNum m0 fuel hops (2 + 1) E
      = runCall progs shaniPath82 rNum m0 fuel hops 2 D
    rw [runCall_succ (n := 2), hE]
    have hc : (C.halted && C.err == none && C.tail.isSome) = true := by rfl
    simp only [hc, if_true]
    rw [hsha]
    simp only [C, Option.getD_some]
    rw [hsc]
    simp only [h30]
    rw [herr, hHalt, hTail]
    have hc2 : ((none : Option String) == none && true && (none : Option String) == none
        && (⟨rRet, (1 : Int)⟩ : Addr Int).region == rRet) = true := by decide
    simp only [hc2, if_true]
    have h1 : ((⟨rRet, (1 : Int)⟩ : Addr Int).off).toNat = 1 := rfl
    rw [h1]
    simp [D, herr]
  have hD31 : D.getG 31 = .ptr a31 := by
    show sc.getG 31 = .ptr a31
    exact h31
  have hDgl : 31 < D.gpr.length := by
    show 31 < sc.gpr.length
    exact hgl
  have hD : runW shaniPath82 rNum m0 (fun _ => false) 1 D = F := by
    rw [runW_one shaniPath82 rNum m0 (fun _ => false) D (.ins (.subi 31 31 2048))
      (by rfl) shaniPath82_1]
    simp only [execW, show D.halted = false from rfl]
    exact exec_subi_eq rNum m0 (fun _ => false) D a31 31 31 2048 (by rfl) hD31
  have step2 : runCall progs shaniPath82 rNum m0 fuel hops 2 D
      = runCall progs shaniPath82 rNum m0 fuel hops 1 F := by
    change runCall progs shaniPath82 rNum m0 fuel hops (1 + 1) D
      = runCall progs shaniPath82 rNum m0 fuel hops 1 F
    rw [runCall_succ (n := 1), hD]
    have hc : (F.halted && F.err == none && F.tail.isSome) = false := by rfl
    simp only [hc, Bool.false_eq_true, if_false]
  have hF30 : F.getG 30 = .ptr ⟨rRet, (1 : Int)⟩ := by
    have hne : (31 : Nat) ≠ 30 := by decide
    show (State.setG D 31 (.ptr (a31.plusI (-((2048 : Nat) : Int))))).next.getG 30
      = .ptr ⟨rRet, (1 : Int)⟩
    rw [next_getG, setG_getG_ne _ 31 30 _ hne]
    exact h30
  have hG : runW shaniPath82 rNum m0 (fun _ => false) 1 F = G := by
    rw [runW_one shaniPath82 rNum m0 (fun _ => false) F (.ins .ret) (by rfl) shaniPath82_2]
    simp only [execW, show F.halted = false from rfl]
    exact exec_ret_halt rNum m0 (fun _ => false) F (1 : Int) (by rfl) hF30
  have step3 : runCall progs shaniPath82 rNum m0 fuel hops 1 F
      = runCall progs shaniPath82 rNum m0 fuel hops 0 G := by
    change runCall progs shaniPath82 rNum m0 fuel hops (0 + 1) F
      = runCall progs shaniPath82 rNum m0 fuel hops 0 G
    rw [runCall_succ (n := 0), hG]
    have hc : (G.halted && G.err == none && G.tail.isSome) = false := by
      rw [show G.halted = true from rfl, show G.tail = none from rfl]
      simp only [Bool.true_and, Option.isSome_none, Bool.and_false]
    simp only [hc, Bool.false_eq_true, if_false]
  have hF31 : F.getG 31 = .ptr (a31.plusI (-((2048 : Nat) : Int))) := by
    show (State.setG D 31 (.ptr (a31.plusI (-((2048 : Nat) : Int))))).next.getG 31
      = .ptr (a31.plusI (-((2048 : Nat) : Int)))
    rw [next_getG]
    exact setG_getG_self D 31 _ (by simpa using hDgl)
  have haddr : a31.plusI (-((2048 : Nat) : Int)) = ⟨rStack, sp0⟩ := by
    show (⟨rStack, sp0 + 2048⟩ : Addr Int).plusI (-((2048 : Nat) : Int)) = ⟨rStack, sp0⟩
    rw [addr_plusI_int]
    congr 1
    omega
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · rw [step1, step2, step3]
    rfl
  · exact herr
  · rfl
  · rfl
  · show F.getG 31 = .ptr ⟨rStack, sp0⟩
    rw [hF31, haddr]

/-- The #82 `sha_x1` path with the kernel leg as a run to its exit cut (the shared `SUB`
restores `SP = sp0`; the exit cut is `ShaX1Exit` at the moved `SP`). -/
theorem wrapper_sha82_of_run (progs : List Prog) (m0 : Addr Int → Cell W32 Int)
    (fuel : Nat) (count : Nat) (sp0 : Int) (sha : Prog) (sc : CS)
    (hf : progs.find? (·.name = "hashtree_sha256_sha_x1") = some sha)
    (hrun : run sha.code sha.ro m0 (fun _ => false) fuel (shaEntry82 count sp0) = sc)
    (hfin : ShaX1Exit (sp0 + 2048) sc)
    (hgl : 31 < sc.gpr.length) :
    ∃ sf, runCall progs shaniPath82 rNum m0 fuel 1 3 (shaWrap82 count sp0) = sf ∧
      sf.err = none ∧ sf.halted = true ∧ sf.tail = none ∧
      sf.getG 31 = .ptr ⟨rStack, sp0⟩ :=
  wrapper_sha82 progs m0 fuel 1 count sp0 sc ["hashtree_sha256_sha_x1"]
    (runChain_single progs m0 fuel "hashtree_sha256_sha_x1" sha (shaEntry82 count sp0) sc
      hf hrun hfin.tail)
    hfin.err hfin.halted hfin.tail hfin.ret hfin.sp hgl

end Hashtree.Asm.ArmCall82

namespace Hashtree.Proofs.ArmShaX1

open Hashtree.Asm Hashtree.Asm.Arm Hashtree.Asm.ArmRun Hashtree.Asm.ArmRename
  Hashtree.Asm.ArmRet Hashtree.Asm.ArmSym Hashtree.Asm.ArmCall Hashtree.Asm.ArmCall82
  Hashtree.Asm.ArmShift

open Hashtree.Gen.ArmShaX1P

/-- The stack-shift relation used by `sha_x1_run_exit_sp_mem0`, exposed: the concrete run at
`SP = sp0` is the `sp0`-shift of the symbolic final state.  Replays the internal steps of
`sha_x1_run_exit_sp_mem0` (only the relation is kept, not the exit cut). -/
theorem sha_x1_run_rel_sp_mem0 (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool) (sp0 : Int)
    (h0 : Mem0Rel env0 σ (mem0s 4 Hashtree.Kernels.Arm.ShaX1.rodata) mem0c)
    (hσ : σ 2 = 2) (hsp : sp0 % 16 = 0) :
    Hashtree.Asm.ArmShift.Rel sp0
      (run Hashtree.Kernels.Arm.ShaX1.prog 4 mem0c orcC fuel
        (retOff 1 (mapState env0 σ (entryS sp0))))
      (retOff 1 (mapState (E193 env0) σ K193)) := by
  have h0' : Mem0Rel env0 σ (mem0s 4 Hashtree.Kernels.Arm.ShaX1.rodata)
      (Hashtree.Asm.ArmShift.memSh (-sp0) mem0c) :=
    Hashtree.Asm.ArmShift.Mem0Rel_memSh 4 Hashtree.Kernels.Arm.ShaX1.rodata
      (by decide : (4 : Region) ≠ rStack) env0 σ mem0c (-sp0) h0
  have hshift := sha_x1_run_shift_sp env0 σ
    (Hashtree.Asm.ArmShift.memSh (-sp0) mem0c) orcC sp0 hsp
  rw [Hashtree.Asm.ArmShift.memSh_comp, show sp0 + -sp0 = 0 by omega,
    Hashtree.Asm.ArmShift.memSh_zero] at hshift
  rw [sha_x1_run_relabeled env0 σ (Hashtree.Asm.ArmShift.memSh (-sp0) mem0c) orcC h0' hσ]
    at hshift
  exact hshift

/-- Length of the symbolic final register file: the `sha_x1` kernel preserves the 32-entry
`gpr`. -/
theorem sha_x1_run_final_gpr_length (env0 : Key → W32) (σ : Nat → Int) :
    (retOff 1 (mapState (E193 env0) σ K193)).gpr.length = 32 := by
  simp [retOff, State.setG, Hashtree.Asm.mapState, E193, K193]

/-- The #82 `sha_x1` leg, driven from the wrapper state after the shared `ADD $2048`
(`shaWrap82`, see `exec_addi_shaWrap82` for the `ADD` itself): the kernel leg enters at
`SP = sp0 + 2048` with return marker `1`, and the shared `SUB $2048; RET` restores
`SP = sp0`. -/
theorem sha_x1_wrapper_82 (progs : List Prog) (m0 : Addr Int → Cell W32 Int)
    (σ : Nat → Int) (count : Nat) (sp0 : Int) (sha : Prog)
    (hf : progs.find? (·.name = "hashtree_sha256_sha_x1") = some sha)
    (hcode : sha.code = Hashtree.Kernels.Arm.ShaX1.prog)
    (hro : sha.ro = 4)
    (h0 : Mem0Rel (bridgeEnv σ m0) σ
      (mem0s 4 Hashtree.Kernels.Arm.ShaX1.rodata) m0)
    (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 0) (hσ : σ 2 = (2 : Int))
    (hcount : count = 2) (hsp : sp0 % 16 = 0) :
    ∃ sf, runCall progs shaniPath82 rNum m0 fuel 1 3 (shaWrap82 count sp0) = sf ∧
      sf.err = none ∧ sf.halted = true ∧ sf.tail = none ∧
      sf.getG 31 = .ptr ⟨rStack, sp0⟩ := by
  have hsp' : (sp0 + 2048) % 16 = 0 := by omega
  have hσ2 : σ 2 = (count : Int) := by rw [hcount]; exact hσ
  let sc : CS := run sha.code sha.ro m0 (fun _ => false) fuel (shaEntry82 count sp0)
  have hentry : shaEntry82 count sp0
      = retOff 1 (mapState (bridgeEnv σ m0) σ (entryS (sp0 + 2048))) := by
    have hb := entry_bridge m0 σ (sp0 + 2048) count hσ0 hσ1 hσ2
    simpa [shaEntry82] using hb.symm
  have hrun : run sha.code sha.ro m0 (fun _ => false) fuel (shaEntry82 count sp0) = sc := rfl
  have hfin : ShaX1Exit (sp0 + 2048) sc := by
    dsimp only [sc]
    rw [hcode, hro, hentry]
    exact sha_x1_run_exit_sp_mem0 (bridgeEnv σ m0) σ m0 (fun _ => false) (sp0 + 2048)
      h0 hσ hsp'
  have hgl : 31 < sc.gpr.length := by
    have hrel := sha_x1_run_rel_sp_mem0 (bridgeEnv σ m0) σ m0 (fun _ => false) (sp0 + 2048)
      h0 hσ hsp'
    dsimp only [sc]
    rw [hcode, hro, hentry, hrel.gpr, sh_gpr_length, sha_x1_run_final_gpr_length]
    decide
  exact wrapper_sha82_of_run progs m0 fuel count sp0 sha sc hf hrun hfin hgl

end Hashtree.Proofs.ArmShaX1
