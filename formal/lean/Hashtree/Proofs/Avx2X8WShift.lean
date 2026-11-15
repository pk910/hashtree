import Hashtree.Proofs.Avx2X8Align
import Hashtree.Gen.Avx2X8P.D0
import Hashtree.Gen.Avx2X8P.D1
import Hashtree.Gen.Avx2X8P.D2
import Hashtree.Gen.Avx2X8P.D3
import Hashtree.Gen.Avx2X8P.D209
import Hashtree.Gen.Avx2X8P.D210
import Hashtree.Asm.Subst
import Hashtree.Asm.X86Loop
import Hashtree.Asm.X86Loop2
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.Avx2X8
open Hashtree.Gen.Avx2X8P
open Hashtree.Proofs.AvxX4W (entryWx)
open Hashtree.Proofs.AvxX4LoopWFrame (logOkBW)
open Hashtree.Proofs.Avx2X8Align

/-!
# The `avx2_x8` pilot cuts rebased on the wrapper call state, per residue

The fixed-count pilot `Gen/Avx2X8P` is stated at `entryS 24`: the stack pointer is the
constant `24`, the aligned frame top is `0` (`24 - 8 = 16`, `16 & -32 = 0`), the pushed `rbp`
sits at `[16, 24)` and the saved `r12..r15` at `[-32, 0)`.  At the wrapper call state the same
frame is relative to the entry stack pointer `σ 9` *and* to the alignment residue
`r = (σ 9 - 8) % 32` (`Avx2X8Align`): the pushed `rbp` is at `sAt (-8)` whatever `r` is, the
frame top at `sAt (-8 - r)`.  So a pilot stack offset `k` becomes

    k ≥ 16 (the pushed rbp, the marker):  sAt (k - 24)
    k < 16 (the frame):                    sAt (k - 8 - r)

which is uniform (`k - 24`) exactly at `r = 16`, the residue of a caller that aligned to 32
before its `CALL`.  `shiftK8 r` is this rebasing of a cut: the stack addresses in registers and
in the write log move as above, the callee-saved registers the kernel never writes (`rax`,
`rbx`, `r12..r15`) take the wrapper's values (`wReg8`, with `rax` on the spare symbol `15` of
`entryWx`), and the saved-register cells become pointer bytes (`shiftCell8`: the kernel saves
pointers, the pilot saved numbers).  The body (`pc 17 .. 6069`) never reads `rbp`, `rbx`,
`r12..r15` or the saved cells, so every pilot slice re-checks at the rebased cuts
(`Avx2X8WBodyR0`/`R16` for the two residues the wrapper ABI allows, `residue_abi`).

The loop.  The body head is the pilot cut `K2` (pc 17, after `lea rcx` and the loads of
`ymm0`, `ymm1`).  Every vector register is loaded before it is read from there (`ymm2..7` at pc
17-22 from the table, `ymm8..15` at pc 24-31 from the input), so the loop-carried vector state
only matters at the cuts before those loads: `KH r` fixes `ymm2..15` at `K2` and `KH3 r`
fixes `ymm9..15` at `K3` (pc 25) to the values one turn leaves in them (`KT r`), and from `K4`
on the pass-1 cuts are the loop's cuts.  `KT r` is the turn's end (the 22-instruction tail
`6052..6073` and the re-entry `cmp rdx,8; jb; lea; vmovdqa; vmovdqa`, 27 instructions), and
`KT_shape` shows it is `KH r` under the loop substitution `tau8` (input `+512`, output `+256`,
count `-8`).  `KTE r` is the exit (the same tail with the `jb` taken, 31 instructions: the
four restores, `mov rsp,rbp; pop rbp`, `jmp avx_x4`).
-/

namespace Hashtree.Proofs.Avx2X8WShift

/-! ## The rebasing -/

/-- A pilot stack offset at residue `r`. -/
def shOff (r : Nat) (k : Int) : Int := if 16 ≤ k then k - 24 else k - 8 - (r : Int)

def shiftA8 (r : Nat) (a : Addr Lin) : Addr Lin :=
  if a.region = rStack then ⟨rStack, sAt (shOff r a.off.k)⟩ else a

def shiftV8 (r : Nat) : Val E Lin → Val E Lin
  | .num lo hi => .num lo hi
  | .ptr a => .ptr (shiftA8 r a)

/-- The pointer the kernel saved at frame offset `896 + 8 i` (pilot address `-32 + 8 i`):
`r12`, `r13`, `r14`, `r15` of the wrapper call state. -/
def savedPtr (k : Int) : Addr Lin :=
  match (k + 32) / 8 with
  | 0 => ⟨rStack, Lin.sym 7⟩
  | 1 => ⟨rNum, Lin.sym 11⟩
  | 2 => ⟨rG, Lin.sym 8⟩
  | _ => ⟨rNum, Lin.sym 12⟩

/-- A pilot log entry rebased: the pushed `rbp` (`[16, 24)`) and the saved registers
(`[-32, 0)`) become pointer bytes of the wrapper's registers; everything else keeps its cell. -/
def shiftCell8 (r : Nat) (p : Addr Lin × Cell E Lin) : Addr Lin × Cell E Lin :=
  let k := p.1.off.k
  if p.1.region = rStack ∧ 16 ≤ k ∧ k < 24 then
    (shiftA8 r p.1, .pb ⟨rStack, Lin.sym 6⟩ (k - 16).toNat)
  else if p.1.region = rStack ∧ -32 ≤ k ∧ k < 0 then
    (shiftA8 r p.1, .pb (savedPtr k) ((k + 32) % 8).toNat)
  else
    (shiftA8 r p.1, match p.2 with | .dat x j => .dat x j | .pb a j => .pb (shiftA8 r a) j)

/-- The wrapper entry value of a register the x8 kernel never writes. -/
def wReg8 : Nat → Val E Lin
  | 0 => .ptr ⟨rOut, Lin.sym 15⟩
  | 3 => .ptr ⟨rStack, Lin.sym 5⟩
  | 12 => .ptr ⟨rStack, Lin.sym 7⟩
  | 13 => .ptr ⟨rNum, Lin.sym 11⟩
  | 14 => .ptr ⟨rG, Lin.sym 8⟩
  | 15 => .ptr ⟨rNum, Lin.sym 12⟩
  | _ => .num (.const 0) (.const 0)

/-- A pilot cut rebased on the wrapper call state at residue `r`. -/
def shiftK8 (r : Nat) (K : State E Lin) : State E Lin :=
  let g := K.gpr.map (shiftV8 r)
  let g2 := (((((g.set 0 (wReg8 0)).set 3 (wReg8 3)).set 12 (wReg8 12)).set 13 (wReg8 13)).set 14
    (wReg8 14)).set 15 (wReg8 15)
  { K with gpr := g2, mem := K.mem.map (shiftCell8 r) }

theorem shiftK8_pc (r : Nat) (K : State E Lin) : (shiftK8 r K).pc = K.pc := rfl
theorem shiftK8_halted (r : Nat) (K : State E Lin) : (shiftK8 r K).halted = K.halted := rfl
theorem shiftK8_tail (r : Nat) (K : State E Lin) : (shiftK8 r K).tail = K.tail := rfl
theorem shiftK8_err (r : Nat) (K : State E Lin) : (shiftK8 r K).err = K.err := rfl
theorem shiftK8_flags (r : Nat) (K : State E Lin) : (shiftK8 r K).flags = K.flags := rfl
theorem shiftK8_assume (r : Nat) (K : State E Lin) : (shiftK8 r K).assume = K.assume := rfl

/-! ## The body's entry conditions -/

/-- The pilot's two entry conditions on every body cut: `c < 8` false, `c ≠ 0` true. -/
def A0 : List (Cond Lin × Bool) :=
  [((.lt (⟨0, [0, 0, 1]⟩ : Lin) (⟨8, []⟩ : Lin)), false),
   ((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]

theorem asmge (σ : Nat → Int) (hge : 8 ≤ σ 2) :
    ∀ p ∈ A0, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A0, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega

/-- No branch (the body slices and the loop tail with `jb` not taken). -/
def orcB : Nat → Bool := fun _ => false

/-- `jb` at pc 13 taken (the loop exit). -/
def orcEx : Nat → Bool := fun pc => decide (pc ∈ ([13] : List Nat))

/-- The body's instruction count (the pilot slices 2..209). -/
def BODYLEN : Nat := 6035

/-- The loop substitution: input `+512`, output `+256`, count `-8`. -/
def tau8 : List Lin := [⟨512, [1]⟩, ⟨256, [0, 1]⟩, ⟨-8, [0, 0, 1]⟩]

/-! ## The loop cuts at residue `r` -/

/-- The turn's end: the loop tail from the body's last cut back to the body head (pc 17). -/
def KT (r : Nat) : State E Lin := abstract (run prog 4 m8 orcB 27 (shiftK8 r K210))

/-- Overwrite the vector registers in `rs` with the values one turn leaves in them. -/
def vfixAt (r : Nat) (rs : List Nat) (vr : List (List E)) : List (List E) :=
  rs.foldl (fun vr i => vr.set i ((KT r).vr.getD i [])) vr

def wfixS (r : Nat) (rs : List Nat) (s : State E Lin) : State E Lin :=
  { s with vr := vfixAt r rs s.vr }

/-- The loop invariant head: the body head `K2` with the loop-carried `ymm2..15`. -/
def KH (r : Nat) : State E Lin :=
  wfixS r [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] (shiftK8 r K2)

/-- The second loop cut: `K3` (pc 25) with the still-unwritten `ymm9..15`. -/
def KH3 (r : Nat) : State E Lin := wfixS r [9, 10, 11, 12, 13, 14, 15] (shiftK8 r K3)

/-- The exit: the loop tail with the `jb` taken, through the epilogue to the `avx_x4` tail. -/
def KTE (r : Nat) : State E Lin := abstract (run prog 4 m8 orcEx 31 (shiftK8 r K210))

/-- The recorded conditions after a turn: the residual count's `jb` (not taken) on top of `A0`. -/
def AT : List (Cond Lin × Bool) :=
  ((.lt (⟨-8, [0, 0, 1]⟩ : Lin) (⟨8, []⟩ : Lin)), false) :: A0

/-- The recorded conditions at the exit: the residual count's `jb` (taken) on top of `A0`. -/
def AX : List (Cond Lin × Bool) :=
  ((.lt (⟨-8, [0, 0, 1]⟩ : Lin) (⟨8, []⟩ : Lin)), true) :: A0

/-- The residual count after a turn is still at least 8. -/
theorem asmT (σ : Nat → Int) (hge : 16 ≤ σ 2) :
    ∀ p ∈ AT, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [AT, A0, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega

/-- The residual count at the exit is below 8. -/
theorem asmX (σ : Nat → Int) (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) :
    ∀ p ∈ AX, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [AX, A0, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega
  · simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
    omega

/-- The general registers at the exit: the wrapper call state's, with the input, output and
count advanced by one batch (`rsi + 512`, `rdi + 256`, `rdx - 8`) and `rcx` on the table. -/
def exitGpr : List (Val E Lin) :=
  (((entryWx.gpr.set 2 (.ptr ⟨rNum, ⟨-8, [0, 0, 1]⟩⟩)).set 6 (.ptr ⟨rIn, ⟨512, [1]⟩⟩)).set 7
    (.ptr ⟨rOut, ⟨256, [0, 1]⟩⟩)).set 1 (.ptr ⟨4, ⟨2048, []⟩⟩)

/-! ## The kernel checks at the two ABI residues -/

/-! ### Residue 0 -/

theorem sliceE_0 : sliceCheck prog 4 m8 orcB 10 (x8A 0) (shiftK8 0 K2) T1 = true := by decide +kernel
theorem sliceV2_0 : sliceCheck prog 4 m8 orcB 8 (KH 0) (KH3 0) T2 = true := by decide +kernel
theorem sliceV3_0 : sliceCheck prog 4 m8 orcB 8 (KH3 0) (shiftK8 0 K4) T3 = true := by decide +kernel
theorem sliceT_0 : sliceCheck prog 4 m8 orcB 27 (shiftK8 0 K210) (KT 0) [] = true := by decide +kernel
theorem sliceX_0 : sliceCheck prog 4 m8 orcEx 31 (shiftK8 0 K210) (KTE 0) [] = true := by decide +kernel
theorem KT_pc_0 : (KT 0).pc = 17 := by decide +kernel
theorem KT_assume_0 : (KT 0).assume = AT := by decide +kernel
theorem KT_logB_0 : (KT 0).mem.all logOkBW = true := by decide +kernel
theorem KH_nOnly_0 : (KH 0).nOnly = true := by decide +kernel
theorem KTE_tail_0 : (KTE 0).tail = some "hashtree_sha256_avx_x4" := by decide +kernel
theorem KTE_err_0 : (KTE 0).err = none := by decide +kernel
theorem KTE_halted_0 : (KTE 0).halted = true := by decide +kernel
theorem KTE_pc_0 : (KTE 0).pc = 6080 := by decide +kernel
theorem KTE_assume_0 : (KTE 0).assume = AX := by decide +kernel
theorem KTE_logB_0 : (KTE 0).mem.all logOkBW = true := by decide +kernel
theorem KTE_gpr_0 : (KTE 0).gpr = exitGpr := by decide +kernel

/-! ### Residue 16 -/

theorem sliceE_16 : sliceCheck prog 4 m8 orcB 10 (x8A 16) (shiftK8 16 K2) T1 = true := by decide +kernel
theorem sliceV2_16 : sliceCheck prog 4 m8 orcB 8 (KH 16) (KH3 16) T2 = true := by decide +kernel
theorem sliceV3_16 : sliceCheck prog 4 m8 orcB 8 (KH3 16) (shiftK8 16 K4) T3 = true := by decide +kernel
theorem sliceT_16 : sliceCheck prog 4 m8 orcB 27 (shiftK8 16 K210) (KT 16) [] = true := by decide +kernel
theorem sliceX_16 : sliceCheck prog 4 m8 orcEx 31 (shiftK8 16 K210) (KTE 16) [] = true := by decide +kernel
theorem KT_pc_16 : (KT 16).pc = 17 := by decide +kernel
theorem KT_assume_16 : (KT 16).assume = AT := by decide +kernel
theorem KT_logB_16 : (KT 16).mem.all logOkBW = true := by decide +kernel
theorem KH_nOnly_16 : (KH 16).nOnly = true := by decide +kernel
theorem KTE_tail_16 : (KTE 16).tail = some "hashtree_sha256_avx_x4" := by decide +kernel
theorem KTE_err_16 : (KTE 16).err = none := by decide +kernel
theorem KTE_halted_16 : (KTE 16).halted = true := by decide +kernel
theorem KTE_pc_16 : (KTE 16).pc = 6080 := by decide +kernel
theorem KTE_assume_16 : (KTE 16).assume = AX := by decide +kernel
theorem KTE_logB_16 : (KTE 16).mem.all logOkBW = true := by decide +kernel
theorem KTE_gpr_16 : (KTE 16).gpr = exitGpr := by decide +kernel

end Hashtree.Proofs.Avx2X8WShift
