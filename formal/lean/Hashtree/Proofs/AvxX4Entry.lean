import Hashtree.Asm.Slice
import Hashtree.Asm.X86SymW
import Hashtree.Kernels.X86.AvxX4
import Hashtree.Proofs.WrapperPre
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Proofs.WrapperAmd64

/-!
# The avx_x4 kernel at the wrapper call state, small counts

Verified groundwork for the all-count proof of the x4 kernel at `entryW`:

* `zero_run`: the count-0 path (`nop; cmp rdx,0; jne; ret`) returns after 4 instructions with the
  callee-saved registers and rsp restored and an empty write log (the KSpec postcondition for c=0).
* `small_prefix`: for `0 < c < 4` the kernel takes the early exit (sub/add rsp, jl) and reaches the
  tail instruction with `entryW` registers, rsp restored, an empty log, and `tail = x1`; the
  instruction after the tail is the x1 kernel entry, at the same `entryW` register shape.
  The remaining gap to a KSpec for these counts is the tail composition into x1 (the flags left by
  the x4 `cmp` and the per-kernel `.rodata` region), not the x4 prefix.
-/

namespace Hashtree.Proofs.AvxX4Small
open Hashtree.Kernels.X86.AvxX4

def orc0 : Nat → Bool := fun _ => false

/-- The cut after the count-0 path. -/
def K0 : State E Lin := abstract (run prog 4 (mem0sW 4 rodata []) orc0 4 entryW)

theorem slice0 : sliceCheck prog 4 (mem0sW 4 rodata []) orc0 4 entryW K0 [] = true := by
  decide +kernel
theorem K0_halted : K0.halted = true := by decide +kernel
theorem K0_tail : K0.tail = none := by decide +kernel
theorem K0_mem : K0.mem = [] := by decide +kernel
theorem K0_err : K0.err = none := by decide +kernel
theorem K0_g4 : K0.gpr[4]? = some (.ptr ⟨rStack, sAt 8⟩) := by decide +kernel
theorem K0_g3 : K0.gpr[3]? = some (.ptr ⟨rStack, Lin.sym 5⟩) := by decide +kernel
theorem K0_g5 : K0.gpr[5]? = some (.ptr ⟨rStack, Lin.sym 6⟩) := by decide +kernel
theorem K0_g12 : K0.gpr[12]? = some (.ptr ⟨rStack, Lin.sym 7⟩) := by decide +kernel
theorem K0_g14 : K0.gpr[14]? = some (.ptr ⟨rG, Lin.sym 8⟩) := by decide +kernel
theorem K0_g13 : K0.gpr[13]? = some (.ptr ⟨rNum, Lin.sym 11⟩) := by decide +kernel
theorem K0_g15 : K0.gpr[15]? = some (.ptr ⟨rNum, Lin.sym 12⟩) := by decide +kernel
theorem K0_assume : K0.assume =
    [((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), false)] := by decide +kernel
theorem entryW_err : entryW.err = none := by decide +kernel

theorem K0_assumeOk (σ : Nat → Int) (hc : σ 2 = 0) : AssumeOk σ K0 := by
  unfold AssumeOk
  intro p hp
  rw [K0_assume] at hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  simp [mapCond, Cond.decideC, Lin.eval, dotC, hc, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]

/-- **Count 0**: the x4 kernel returns directly after `nop; cmp rdx,0; jne; ret`, with the
callee-saved registers and rsp restored and no memory writes. -/
theorem zero_run (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMemW rodata [] env0 σ mem0c) (he : EnvMem env0 σ mem0c) (hc : σ 2 = 0) :
    let fin := run prog 4 mem0c orcC 4 (mapState env0 σ entryW)
    fin.halted = true ∧ fin.err = none ∧ fin.tail = none ∧ fin.mem = [] ∧
      fin.getG 4 = .ptr ⟨rStack, σ 9 + 8⟩ ∧ fin.getG 3 = .ptr ⟨rStack, σ 5⟩ ∧
      fin.getG 5 = .ptr ⟨rStack, σ 6⟩ ∧ fin.getG 12 = .ptr ⟨rStack, σ 7⟩ ∧
      fin.getG 14 = .ptr ⟨rG, σ 8⟩ ∧ fin.getG 13 = .ptr ⟨rNum, σ 11⟩ ∧
      fin.getG 15 = .ptr ⟨rNum, σ 12⟩ := by
  have h0 := mem0RelW_of_wf rodata [] env0 σ mem0c hw he
  have hPr := (slice_sound env0 σ (mem0sW 4 rodata []) mem0c h0 prog 4 orc0 orcC 4 entryW K0 []
    slice0 entryW_err (K0_assumeOk σ hc)).1
  simp only
  rw [hPr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mapState, K0_halted]
  · simp only [mapState, K0_err]
  · simp only [mapState, K0_tail]
  · simp only [mapState, K0_mem]
    rfl
  · rw [getG_hom, getG_of _ _ _ K0_g4]; simp only [mapVal, mapAddr, sAt_eval]; congr 2; omega
  · rw [getG_hom, getG_of _ _ _ K0_g3]; simp only [mapVal, mapAddr, Lin.eval_sym]
  · rw [getG_hom, getG_of _ _ _ K0_g5]; simp only [mapVal, mapAddr, Lin.eval_sym]
  · rw [getG_hom, getG_of _ _ _ K0_g12]; simp only [mapVal, mapAddr, Lin.eval_sym]
  · rw [getG_hom, getG_of _ _ _ K0_g14]; simp only [mapVal, mapAddr, Lin.eval_sym]
  · rw [getG_hom, getG_of _ _ _ K0_g13]; simp only [mapVal, mapAddr, Lin.eval_sym]
  · rw [getG_hom, getG_of _ _ _ K0_g15]; simp only [mapVal, mapAddr, Lin.eval_sym]

/-! ## `0 < c < 4`: the early exit to the x1 tail -/

def orcK : Nat → Bool := fun pc => decide (pc ∈ ([2,6] : List Nat))

/-- The cut at the x4 `jmpTail ...x1` instruction after the early exit. -/
def KSm : State E Lin := abstract (run prog 4 (mem0sW 4 rodata []) orcK 8 entryW)

theorem sliceSm : sliceCheck prog 4 (mem0sW 4 rodata []) orcK 8 entryW KSm [] = true := by
  decide +kernel
theorem KSm_pc : KSm.pc = 4143 := by decide +kernel
theorem KSm_halted : KSm.halted = true := by decide +kernel
theorem KSm_tail : KSm.tail = some "hashtree_sha256_avx_x1" := by decide +kernel
theorem KSm_mem : KSm.mem = [] := by decide +kernel
theorem KSm_err : KSm.err = none := by decide +kernel
theorem KSm_gpr : KSm.gpr = entryW.gpr := by decide +kernel
theorem KSm_vr : KSm.vr = entryW.vr := by decide +kernel
theorem KSm_assume : KSm.assume =
    [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨4, []⟩ : Lin)), true),
     ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)] := by decide +kernel

theorem KSm_assumeOk (σ : Nat → Int) (hlt : σ 2 < 4) (hne : σ 2 ≠ 0) : AssumeOk σ KSm := by
  unfold AssumeOk
  intro p hp
  rw [KSm_assume] at hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]; omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, hne, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]

/-- **Counts 1-3**: the kernel reaches `jmpTail ...x1` with `entryW` registers, rsp restored
(`sub rsp,408` then `add rsp,408`), an empty log, and `rdx` unchanged.  The cut is halted with the
tail name recorded, ready to be composed with the x1 contract. -/
theorem small_prefix (env0 : Key → W32) (σ : Nat → Int)
    (mem0c : Addr Int → Cell W32 Int) (orcC : Nat → Bool)
    (hw : WfMemW rodata [] env0 σ mem0c) (he : EnvMem env0 σ mem0c)
    (hlt : σ 2 < 4) (hne : σ 2 ≠ 0) :
    run prog 4 mem0c orcC 8 (mapState env0 σ entryW) =
      mapState (envAbs env0 (run prog 4 (mem0sW 4 rodata []) orcK 8 entryW)) σ KSm := by
  have h0 := mem0RelW_of_wf rodata [] env0 σ mem0c hw he
  exact (slice_sound env0 σ (mem0sW 4 rodata []) mem0c h0 prog 4 orcK orcC 8 entryW KSm []
    sliceSm entryW_err (KSm_assumeOk σ hlt hne)).1

end Hashtree.Proofs.AvxX4Small
