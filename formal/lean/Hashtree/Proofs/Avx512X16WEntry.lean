import Hashtree.Proofs.Avx512X16WBody
import Hashtree.Asm.X86Loop2
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
  Hashtree.Kernels.X86.Avx512X16

namespace Hashtree.Proofs.Avx512X16WEntry
open Hashtree.Gen.Avx512X16P
open Hashtree.Proofs.Avx512X16WBody

/-!
# The AVX-512 kernel at the wrapper's call state: entry paths, loop head and loop tail

`entryW` is the state the Go wrapper calls a kernel with (`Hashtree.Asm.X86SymW`).  This file
supplies the cuts of the `avx512_x16` kernel that the fixed-count pilot certificate
(`Avx512X16P`) does not have at the wrapper's state:

* the count-0 early return (`KZ`) and the `0 < c < 16` early exit into `avx2_x8` (`KSm`);
* the entry path into the body head at `pc = 9` (`wcutE K1`), and the bridge from it to the
  body's head cuts (`wcutH`, which carry the output base in `rax` on an otherwise unused
  symbol `10` so that the loop substitution does not move it);
* the loop head `KT` reached after one turn (`jb` not taken) and the exit cut `KTE`
  (`jb` taken, tail call into `avx2_x8`);
* the substitution `tau` of one turn, and the shape lemmas `KT_gpr`/`KT_vr`/`KT_shape` /
  `KT_inst`: one turn's end cut is the loop head under `tau`, register by register (the four
  scratch vector registers are the body's, and general registers match up to their
  location variables).

The loop itself is in `Avx512X16WLoop`.
-/

/-! ## Oracles (the branch decisions the slices expect) -/

/-- `jne` at pc 2 taken (count nonzero). -/
def orcEntry : Nat → Bool := fun pc => decide (pc ∈ ([2] : List Nat))

/-- `jne` at pc 2 taken and `jb` at pc 8 taken (count below the lane width). -/
def orcSmall : Nat → Bool := fun pc => decide (pc ∈ ([2, 8] : List Nat))

/-- `jb` at pc 8 taken: the residual blocks go to `avx2_x8`. -/
def orcExit : Nat → Bool := fun pc => decide (pc ∈ ([8] : List Nat))

/-- No branch taken. -/
def orcNone : Nat → Bool := fun _ => false

theorem K1_pc : K1.pc = 9 := by decide +kernel
theorem K216_pc : K216.pc = 3227 := by decide +kernel
theorem K1_err : K1.err = none := by decide +kernel
theorem K216_err : K216.err = none := by decide +kernel
theorem K1_assume : K1.assume = A0 := by decide +kernel
theorem K216_assume : K216.assume = A0 := by decide +kernel
theorem ew0 : ew 0 = (Val.ptr (⟨rOut, Lin.sym 1⟩ : Addr Lin)) := by decide +kernel
theorem wcutH0 : (wcutH K1).gpr[0]? = some (Val.ptr (⟨rOut, Lin.sym 10⟩ : Addr Lin)) := by decide +kernel

/-! ## The three count classes -/

/-- Count zero: `nop; cmp rdx,0; jne` not taken; `ret`. -/
def KZ : State E Lin := abstract (run prog 4 mW orcNone 4 entryW)

theorem sliceW_zero : sliceCheck prog 4 mW orcNone 4 entryW KZ [] = true := by decide +kernel
theorem KZ_pc : KZ.pc = 3 := by decide +kernel
theorem KZ_halted : KZ.halted = true := by decide +kernel
theorem KZ_tail : KZ.tail = none := by decide +kernel
theorem KZ_err : KZ.err = none := by decide +kernel
theorem KZ_mem : KZ.mem = [] := by decide +kernel
theorem KZ_assume : KZ.assume =
    [((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), false)] := by decide +kernel

/-- Counts `0 < c < 16`: the `jne` and the `jb` are taken and the kernel tails into
`avx2_x8` after eight instructions. -/
def KSm : State E Lin := abstract (run prog 4 mW orcSmall 8 entryW)

theorem sliceW_small : sliceCheck prog 4 mW orcSmall 8 entryW KSm [] = true := by decide +kernel
theorem KSm_halted : KSm.halted = true := by decide +kernel
theorem KSm_tail : KSm.tail = some "hashtree_sha256_avx2_x8" := by decide +kernel
theorem KSm_err : KSm.err = none := by decide +kernel
theorem KSm_mem : KSm.mem = [] := by decide +kernel
/-- The small path's recorded conditions: `c < 16` (taken) and `c != 0` (taken). -/
def A0S : List (Cond Lin × Bool) :=
  [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨16, []⟩ : Lin)), true),
   ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]

theorem KSm_assume : KSm.assume = A0S := by decide +kernel

/-- The small path's conditions, for a count in `(0, 16)`. -/
theorem asmSmall (σ : Nat → Int) (h0 : 0 < σ 2) (h16 : σ 2 < 16) :
    ∀ p ∈ A0S, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A0S, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega

/-- The count-0 path's condition: `c == 0`. -/
theorem asmZero (σ : Nat → Int) (h0 : σ 2 = 0) :
    ∀ p ∈ (KZ.assume), (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  rw [KZ_assume] at hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
  omega

/-- The entry path into the body: `nop; cmp rdx,0; jne` taken; the three `lea`s; `cmp rdx,16`;
`jb` not taken; eight instructions reach the body head at `pc = 9`. -/
theorem sliceW_entry : sliceCheck prog 4 mW orcEntry 8 entryW (wcutE K1) T0 = true := by
  decide +kernel

theorem wcutE_K1_pc : (wcutE K1).pc = 9 := by decide +kernel
theorem wcutE_K1_err : (wcutE K1).err = none := by decide +kernel
theorem wcutE_K1_assume : (wcutE K1).assume = A0 := by decide +kernel

/-- The entry cut denotes the body head under the symbol agreement `σ 10 = σ 1`: the only
difference is `rax`, which the body never reads (it keeps the output base there, on the
untouched symbol `10`). -/
theorem mapState_wcutE (e : Key → W32) (σ : Nat → Int) (h10 : σ 10 = σ 1) :
    mapState e σ (wcutE K1) = mapState e σ (wcutH K1) := by
  have hE : wcutE K1 =
      { wcutH K1 with gpr := (wcutH K1).gpr.set 0 (Val.ptr (⟨rOut, Lin.sym 1⟩ : Addr Lin)) } := by
    simp only [wcutE, ew0]
  rw [hE]
  have hv : mapVal e σ (Val.ptr (⟨rOut, Lin.sym 1⟩ : Addr Lin)) =
      Val.ptr (⟨rOut, σ 1⟩ : Addr Int) := by
    simp [mapVal, mapAddr, Lin.eval_sym]
  have h0 : ((wcutH K1).gpr.map (mapVal e σ))[0]? = some (Val.ptr (⟨rOut, σ 10⟩ : Addr Int)) := by
    rw [List.getElem?_map, wcutH0]
    simp [mapVal, mapAddr, Lin.eval_sym]
  have hset : ((wcutH K1).gpr.map (mapVal e σ)).set 0 (Val.ptr (⟨rOut, σ 1⟩ : Addr Int)) =
      (wcutH K1).gpr.map (mapVal e σ) := by
    rw [h10] at h0
    cases h : (wcutH K1).gpr.map (mapVal e σ) with
    | nil => simp [h] at h0
    | cons x xs => simp_all [List.set]
  simp only [mapState, List.map_set, hv, hset]

/-! ## The loop head, the turn tail and the exit -/

/-- The loop substitution: one turn advances the input (`sym 0`) by 1024 and the output
(`sym 1`) by 512 bytes and lowers the count (`sym 2`) by 16.  Symbols past the count (in
particular symbol `10`, the output base carried in `rax`) are untouched. -/
def tau : List Lin := [⟨1024, [1]⟩, ⟨512, [0, 1]⟩, ⟨-16, [0, 0, 1]⟩]

/-- The loop tail (22 instructions from the pilot's end cut) with `jb` not taken: back at the
body head `pc = 9`. -/
def KT : State E Lin := abstract (run prog 4 mW orcNone 22 (wcutH K216))

theorem sliceW_turn : sliceCheck prog 4 mW orcNone 22 (wcutH K216) KT [] = true := by
  decide +kernel

theorem KT_pc : KT.pc = 9 := by decide +kernel
theorem KT_halted : KT.halted = false := by decide +kernel
theorem KT_tail : KT.tail = none := by decide +kernel
theorem KT_err : KT.err = none := by decide +kernel
theorem KT_assume : KT.assume =
    ((.lt (⟨-16, [0, 0, 1]⟩ : Lin) (⟨16, []⟩ : Lin)), false) :: A0 := by decide +kernel

/-- The exit: the same 22 instructions with `jb` taken; the kernel tails into `avx2_x8` with
the residual count `c - 16`. -/
def KTE : State E Lin := abstract (run prog 4 mW orcExit 22 (wcutH K216))

theorem sliceW_exit : sliceCheck prog 4 mW orcExit 22 (wcutH K216) KTE [] = true := by
  decide +kernel

theorem KTE_halted : KTE.halted = true := by decide +kernel
theorem KTE_tail : KTE.tail = some "hashtree_sha256_avx2_x8" := by decide +kernel
theorem KTE_err : KTE.err = none := by decide +kernel
theorem KTE_assume : KTE.assume =
    ((.lt (⟨-16, [0, 0, 1]⟩ : Lin) (⟨16, []⟩ : Lin)), true) :: A0 := by decide +kernel

/-- Overwrite the scratch vector registers listed in `rs` with the pilot's end-of-body values
(`K216`). -/
def vfixAt (rs : List Nat) (vr : List (List E)) : List (List E) :=
  rs.foldl (fun vr r => vr.set r (K216.vr.getD r [])) vr

/-- The fix of a cut: the registers the body has not yet written carry the value the loop pass
brings into them.  The body writes `zmm24` first in slice 3, `zmm13`/`zmm14` in slice 7 and
`zmm15` in slice 13, and reads none of them before writing it, so the replay of the body in
`Avx512X16WBodyV` fixes exactly the not-yet-written ones at each cut. -/
def wfixS (rs : List Nat) (s : State E Lin) : State E Lin := { s with vr := vfixAt rs s.vr }

/-- The loop invariant head: the first-pass head with the four scratch registers as the body
leaves them. -/
def KH : State E Lin := wfixS [13, 14, 15, 24] (wcutH K1)

/-- **The loop shape, register by register.**  The turn's end cut has the invariant head's
general registers up to the register variables of their locations, and the head's vector
registers: the body overwrites the four scratch registers before reading them. -/
theorem KT_gpr : gprRel 0 (KH.substL tau).gpr KT.gpr = true := by decide +kernel

theorem KT_vr : vrRel 0 KH.vr KT.vr = true := by decide +kernel

/-- **The loop shape.**  One turn's end cut, with its registers replaced by the invariant
head's and stripped of its write log and recorded conditions, is the head under the turn
substitution. -/
theorem KT_shape :
    { ({ KT with gpr := (KH.substL tau).gpr, vr := KH.vr } : State E Lin) with
      mem := [], assume := [] } = KH.substL tau := by decide +kernel

/-- **The loop shape at the concrete level.**  The end cut of one turn denotes the same state
with the invariant head's registers: the run's end state witnesses the register relation
(`mapState_inst` over the tail's slice check). -/
theorem KT_inst (env0 : Key → W32) (σ : Nat → Int) :
    mapState (envAbs env0 (run prog 4 mW orcNone 22 (wcutH K216))) σ KT =
      mapState (envAbs env0 (run prog 4 mW orcNone 22 (wcutH K216))) σ
        { KT with gpr := (KH.substL tau).gpr, vr := KH.vr } :=
  mapState_inst env0 σ prog 4 mW orcNone 22 (wcutH K216) KT [] sliceW_turn
    (KH.substL tau).gpr KH.vr KT_gpr KT_vr

/-- The substitution lowers the count by the lane width. -/
theorem tau_count (σ : Nat → Int) : sigmaOf tau σ 2 = σ 2 - 16 := by
  have ht : tauAt tau 2 = (⟨-16, [0, 0, 1]⟩ : Lin) := rfl
  show (tauAt tau 2).eval σ = σ 2 - 16
  rw [ht]
  simp [Lin.eval, dotC]
  omega

/-- The invariant head only reads numbered variables, so its concrete meaning does not depend
on the memory part of the environment. -/
theorem KH_nOnly : KH.nOnly = true := by decide +kernel

end Hashtree.Proofs.Avx512X16WEntry
