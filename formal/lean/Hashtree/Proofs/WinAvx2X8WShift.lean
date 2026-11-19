import Hashtree.Gen.WinAvx2X8P.Ro
import Hashtree.Gen.WinAvx2X8P.D0
import Hashtree.Gen.WinAvx2X8P.D1
import Hashtree.Gen.WinAvx2X8P.D2
import Hashtree.Gen.WinAvx2X8P.D3
import Hashtree.Gen.WinAvx2X8P.D4
import Hashtree.Gen.WinAvx2X8P.D5
import Hashtree.Gen.WinAvx2X8P.D210
import Hashtree.Gen.WinAvx2X8P.D211
import Hashtree.Proofs.AvxX4WPrep
import Hashtree.Proofs.WrapperPre
import Hashtree.Proofs.WinWrapperPre
import Hashtree.Proofs.WinLogW
import Hashtree.Asm.Slice
import Hashtree.Asm.Chain
import Hashtree.Asm.Subst
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinWrapper (entryWin)

/-!
# The windows `avx2_x8` pilot cuts rebased on the wrapper call state, per residue

The fixed-count windows pilot `Gen/WinAvx2X8P` (count 8, 211 slices `K1 .. K212`) is stated at
`entrySW 24`: `rsp` is the constant `24`.  The kernel pushes `rbp` and `rsi`, sets
`rbp := rsp`, aligns `and rsp,-32` and reserves 1248 bytes: in the pilot the pushes sit at
`[16, 24)` / `[8, 16)`, `rbp = 8`, the aligned frame top is `0`, the `r12..r15` saves at
`[-352, -320)` and the ten `ymm6..15` saves at `[-320, 0)`.  At the wrapper call state
(`WinWrapper.entryWin`, return marker at `σ 9`) the pushes sit at `sAt (-8)` / `sAt (-16)`,
`rbp = sAt (-16)`, and the frame top at `sAt (-16 - r)` for the alignment residue
`r = (σ 9 - 16) % 32`, so a pilot stack offset `k` becomes

    k ≥ 8 (the pushes, the marker):  sAt (k - 24)
    k < 8 (the frame):                sAt (k - 16 - r)

which is uniform at `r = 8` (the pilot's residue).  The wrapper ABI (`σ 9 % 16 = 8`) allows
`r = 8` and `r = 24`.  `shiftK8W r` rebases a cut: stack addresses move as above, the registers
the kernel never writes take the wrapper's pointers (`wReg8W`), and the pushed `rbp` and the
saved `r12..r15` become pointer bytes (`shiftCell8W`).

Loop shape (windows pcs): the body runs from the guard `cmp r8,8; jb` at 23/24 through
`25 .. 6085` (`jmp 23`); the pilot cut `K3` (pc 25) is the loop head.  Every `ymm` is loaded
before it is read from there (`ymm0..7` at 26-33 from the table, `ymm8..15` at 35-42 from the
input), so the loop-carried vector state matters only at `K3` (all sixteen), `K4` (pc 33:
`ymm7..15`) and `K5` (pc 41: `ymm14, ymm15`).  `KT r` is the turn's end (`K211` at 6064, the
22-instruction tail, `cmp; jb` not taken: 24 instructions to pc 25); `KTE r` the exit (the same
with `jb` taken, the ten `ymm` and four `r12..r15` restores, `mov rsp,rbp; pop rsi; pop rbp;
jmp avx_x4`).
-/

namespace Hashtree.Proofs.WinAvx2X8W

/-- The wrapper-call symbolic memory: the kernel's table in region 4, nothing pushed. -/
def m8W : Addr Lin → Cell E Lin := mem0qW 4 roC []

/-! ## The prologue up to the alignment -/

/-- `jne` at pc 2 taken (count nonzero). -/
def orcNZ : Nat → Bool := fun pc => decide (pc ∈ ([2] : List Nat))
/-- No branch taken. -/
def orcB : Nat → Bool := fun _ => false
/-- `jb` at pc 24 taken (the loop exit). -/
def orcEx : Nat → Bool := fun pc => decide (pc ∈ ([24] : List Nat))

/-- Six instructions (`nop; cmp r8,0; jne; push rbp; push rsi; mov rbp,rsp`) to the alignment. -/
def x8P : State E Lin := abstract (run prog 4 m8W orcNZ 6 entryWin)

def alignI8 : Instr := .alu .and 64 4 (.imm (-32))

/-- The state after `and rsp,-32` at residue `r`. -/
def x8A (r : Nat) : State E Lin :=
  { x8P with gpr := x8P.gpr.set 4 (.ptr ⟨rStack, sAt (-16 - (r : Int))⟩), flags := none, pc := 8 }

/-! ## The rebasing -/

/-- A pilot stack offset at residue `r`. -/
def shOff (r : Nat) (k : Int) : Int := if 8 ≤ k then k - 24 else k - 16 - (r : Int)

def shiftA8 (r : Nat) (a : Addr Lin) : Addr Lin :=
  if a.region = rStack then ⟨rStack, sAt (shOff r a.off.k)⟩ else a

def shiftV8 (r : Nat) : Val E Lin → Val E Lin
  | .num lo hi => .num lo hi
  | .ptr a => .ptr (shiftA8 r a)

/-- The pointer the kernel saved at pilot address `-352 + 8 i`: `r12`, `r13`, `r14`, `r15` of the
wrapper call state. -/
def savedPtr (k : Int) : Addr Lin :=
  match (k + 352) / 8 with
  | 0 => ⟨rNum, Lin.sym 7⟩
  | 1 => ⟨rNum, Lin.sym 11⟩
  | 2 => ⟨rG, Lin.sym 8⟩
  | _ => ⟨rNum, Lin.sym 12⟩

/-- A pilot log entry rebased: the pushed `rbp` (`[16, 24)`) and the saved `r12..r15`
(`[-352, -320)`) become pointer bytes of the wrapper's registers; everything else keeps its
cell (the pushed `rsi` and the `ymm` saves are data in both states). -/
def shiftCell8 (r : Nat) (p : Addr Lin × Cell E Lin) : Addr Lin × Cell E Lin :=
  let k := p.1.off.k
  if p.1.region = rStack ∧ 16 ≤ k ∧ k < 24 then
    (shiftA8 r p.1, .pb ⟨rStack, Lin.sym 6⟩ (k - 16).toNat)
  else if p.1.region = rStack ∧ -352 ≤ k ∧ k < -320 then
    (shiftA8 r p.1, .pb (savedPtr k) ((k + 352) % 8).toNat)
  else
    (shiftA8 r p.1, match p.2 with | .dat x j => .dat x j | .pb a j => .pb (shiftA8 r a) j)

/-- The wrapper entry value of a register the kernel never writes. -/
def wReg8 : Nat → Val E Lin
  | 3 => .ptr ⟨rStack, Lin.sym 5⟩
  | 12 => .ptr ⟨rNum, Lin.sym 7⟩
  | 13 => .ptr ⟨rNum, Lin.sym 11⟩
  | 14 => .ptr ⟨rG, Lin.sym 8⟩
  | 15 => .ptr ⟨rNum, Lin.sym 12⟩
  | _ => .num (.const 0) (.const 0)

/-- A pilot cut rebased on the wrapper call state at residue `r`. -/
def shiftK8 (r : Nat) (K : State E Lin) : State E Lin :=
  let g := K.gpr.map (shiftV8 r)
  let g2 := ((((g.set 3 (wReg8 3)).set 12 (wReg8 12)).set 13 (wReg8 13)).set 14
    (wReg8 14)).set 15 (wReg8 15)
  { K with gpr := g2, mem := K.mem.map (shiftCell8 r) }

/-! ## The loop cuts at residue `r` -/

/-- The loop substitution: input `+512`, output `+256`, count `-8`. -/
def tau8 : List Lin := [⟨512, [1]⟩, ⟨256, [0, 1]⟩, ⟨-8, [0, 0, 1]⟩]

/-- The turn's end: the loop tail from the body's last cut back to the loop head (pc 25). -/
def KT (r : Nat) : State E Lin := abstract (run prog 4 m8W orcB 24 (shiftK8 r K211))

/-- The exit: the loop tail with the `jb` taken, through the epilogue to the `avx_x4` tail. -/
def KTE (r : Nat) : State E Lin := abstract (run prog 4 m8W orcEx 42 (shiftK8 r K211))

/-- The rebased `K2` (pc 17): its flags come from `sub rsp,1248`, whose first operand is the
aligned stack pointer `sAt (-16 - r)`; `shiftK8` leaves flags alone. -/
def K2W (r : Nat) : State E Lin :=
  { shiftK8 r K2 with flags := some (sAt (-16 - (r : Int)), ⟨1248, []⟩) }

/-! ## Facts of the prologue and the alignment -/

theorem m8W_eq : m8W = mem0sW 4 rodata [] :=
  mem0qW_eq 4 rodata [] roC 70 roC_eq (by decide +kernel)

theorem m8W_keyed : MemKeyed m8W :=
  mem0qW_keyed 4 rodata [] roC 70 roC_eq (by decide +kernel) (by decide +kernel)

/-- The prologue up to the alignment, one kernel evaluation. -/
def preOk : Bool :=
  sliceCheck prog 4 m8W orcNZ 6 entryWin x8P [] && decide (x8P.pc = 7) &&
  decide (x8P.halted = false) && decide (x8P.err = none) &&
  decide (x8P.gpr[4]? = some (.ptr ⟨rStack, sAt (-16)⟩)) &&
  decide (prog[7]? = some alignI8)

theorem preOk_true : preOk = true := by decide +kernel

theorem preFacts :
    sliceCheck prog 4 m8W orcNZ 6 entryWin x8P [] = true ∧ x8P.pc = 7 ∧ x8P.halted = false ∧
    x8P.err = none ∧ x8P.gpr[4]? = some (.ptr ⟨rStack, sAt (-16)⟩) ∧
    prog[7]? = some alignI8 := by
  have h := preOk_true
  simp only [preOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem sliceP : sliceCheck prog 4 m8W orcNZ 6 entryWin x8P [] = true := preFacts.1
theorem x8P_pc : x8P.pc = 7 := preFacts.2.1
theorem x8P_halted : x8P.halted = false := preFacts.2.2.1
theorem x8P_err : x8P.err = none := preFacts.2.2.2.1
theorem x8P_rsp : x8P.gpr[4]? = some (.ptr ⟨rStack, sAt (-16)⟩) := preFacts.2.2.2.2.1
theorem prog_7 : prog[7]? = some alignI8 := preFacts.2.2.2.2.2
theorem entryWin_err : entryWin.err = none := rfl
theorem x8A_err (r : Nat) : (x8A r).err = none := x8P_err

/-- The prologue's recorded condition: the count is nonzero. -/
def A1nz : List (Cond Lin × Bool) :=
  [((.not (.eq (⟨0, [0, 0, 1]⟩ : Lin) (⟨0, []⟩ : Lin))), true)]

theorem asmNZ (σ : Nat → Int) (h0 : 0 < σ 2) :
    ∀ p ∈ A1nz, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [A1nz, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt]
  omega

/-- **The alignment at the concrete state.**  `rsp` is the integer `σ 9 - 16` there, so
`andInt` is total; the result is `x8A r` for the residue `r = (σ 9 - 16) % 32`. -/
theorem align_hom8 (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (r : Nat) (hr : (r : Int) = (σ 9 - 16) % 32) :
    exec 4 m orc alignI8 (mapState env σ x8P) = mapState env σ (x8A r) := by
  have hsp : (mapState env σ x8P).getG 4 = .ptr ⟨rStack, σ 9 - 16⟩ := by
    rw [getG_hom, Hashtree.Proofs.WrapperAmd64.getG_of _ _ _ x8P_rsp]
    simp only [mapVal, mapAddr, Hashtree.Proofs.WrapperAmd64.sAt_eval]; congr 2; omega
  have hh : (mapState env σ x8P).halted = false := by simp only [mapState, x8P_halted]
  simp only [exec, alignI8, hh, Bool.false_eq_true, ite_false]
  simp [okOr, gCtl, hsp, andInt, Ctl.asInt, Ctl.ofInt, bind, Except.bind, pure, Except.pure]
  simp only [mapState, x8A, clearFlags, State.setG, State.next, x8P_pc, List.map_set, mapVal,
    mapAddr, Hashtree.Proofs.WrapperAmd64.sAt_eval]
  congr 4
  omega

theorem run1_align (env : Key → W32) (σ : Nat → Int) (m : Addr Int → Cell W32 Int)
    (orc : Nat → Bool) (r : Nat) (hr : (r : Int) = (σ 9 - 16) % 32) :
    run prog 4 m orc 1 (mapState env σ x8P) = mapState env σ (x8A r) := by
  have hh : (mapState env σ x8P).halted = false := by simp only [mapState, x8P_halted]
  have hpc : (mapState env σ x8P).pc = 7 := by simp only [mapState, x8P_pc]
  show run prog 4 m orc (0 + 1) (mapState env σ x8P) = mapState env σ (x8A r)
  simp only [run, hh, Bool.false_eq_true, ite_false, hpc, prog_7]
  exact align_hom8 env σ m orc r hr

/-- The wrapper ABI (`σ 9 % 16 = 8`) leaves the residues 8 and 24. -/
theorem residue_abi (σ : Nat → Int) (h : σ 9 % 16 = 8) :
    (8 : Int) = (σ 9 - 16) % 32 ∨ (24 : Int) = (σ 9 - 16) % 32 := by
  omega

/-! ## The body's conditions -/

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

/-- The recorded conditions after a turn: the residual count's `jb` (not taken) on top of `A0`. -/
def AT : List (Cond Lin × Bool) :=
  ((.lt (⟨-8, [0, 0, 1]⟩ : Lin) (⟨8, []⟩ : Lin)), false) :: A0

/-- The recorded conditions at the exit: the residual count's `jb` (taken) on top of `A0`. -/
def AX : List (Cond Lin × Bool) :=
  ((.lt (⟨-8, [0, 0, 1]⟩ : Lin) (⟨8, []⟩ : Lin)), true) :: A0

theorem asmT (σ : Nat → Int) (hge : 16 ≤ σ 2) :
    ∀ p ∈ AT, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [AT, A0, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;>
    omega

theorem asmX (σ : Nat → Int) (hge : 8 ≤ σ 2) (hlt : σ 2 < 16) :
    ∀ p ∈ AX, (mapCond σ p.1).decideC = some p.2 := by
  intro p hp
  simp only [AX, A0, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp [mapCond, Cond.decideC, Lin.eval, dotC, Ctl.sub, Ctl.add, Ctl.smul, Ctl.asInt] <;>
    omega

/-- The general registers at the exit: the wrapper call state's, with the output, input and
count advanced by one batch (`rcx + 256`, `rdx + 512`, `r8 - 8`); `rsi`, `rbp` popped,
`r12..r15` restored, `rsp` back at the marker. -/
def exitGprW : List (Val E Lin) :=
  ((entryWin.gpr.set 1 (.ptr ⟨rOut, ⟨256, [0, 1]⟩⟩)).set 2 (.ptr ⟨rIn, ⟨512, [1]⟩⟩)).set 8
    (.ptr ⟨rNum, ⟨-8, [0, 0, 1]⟩⟩)

/-- The body's instruction count from the loop head `K3` to `K211` (the pilot slices 3..210). -/
def BODYLEN : Nat := 6039

/-! ## The kernel checks at one residue

All pass-1 facts of a residue are one boolean, so that the kernel evaluates the turn's end
`KT r` and the exit `KTE r` once; the named facts are read off it. -/

def shiftOk (r : Nat) : Bool :=
  sliceCheck prog 4 m8W orcB 9 (x8A r) (K2W r) [] &&
  sliceCheck prog 4 m8W orcB 8 (K2W r) (shiftK8 r K3) T2 &&
  sliceCheck prog 4 m8W orcB 24 (shiftK8 r K211) (KT r) [] &&
  sliceCheck prog 4 m8W orcEx 42 (shiftK8 r K211) (KTE r) [] &&
  decide ((KT r).pc = 25) && decide ((KT r).assume = AT) &&
  decide ((KTE r).tail = some "hashtree_sha256_avx_x4") && decide ((KTE r).err = none) &&
  decide ((KTE r).halted = true) && decide ((KTE r).pc = 6103) &&
  decide ((KTE r).assume = AX) && decide ((KTE r).gpr = exitGprW) &&
  (KT r).mem.all Hashtree.Proofs.WinLogW.logOkBW && (KTE r).mem.all Hashtree.Proofs.WinLogW.logOkBW

theorem shiftFacts (r : Nat) (h : shiftOk r = true) :
    sliceCheck prog 4 m8W orcB 9 (x8A r) (K2W r) [] = true ∧
    sliceCheck prog 4 m8W orcB 8 (K2W r) (shiftK8 r K3) T2 = true ∧
    sliceCheck prog 4 m8W orcB 24 (shiftK8 r K211) (KT r) [] = true ∧
    sliceCheck prog 4 m8W orcEx 42 (shiftK8 r K211) (KTE r) [] = true ∧
    (KT r).pc = 25 ∧ (KT r).assume = AT ∧
    (KTE r).tail = some "hashtree_sha256_avx_x4" ∧ (KTE r).err = none ∧
    (KTE r).halted = true ∧ (KTE r).pc = 6103 ∧ (KTE r).assume = AX ∧ (KTE r).gpr = exitGprW ∧
    (KT r).mem.all Hashtree.Proofs.WinLogW.logOkBW = true ∧
    (KTE r).mem.all Hashtree.Proofs.WinLogW.logOkBW = true := by
  simp only [shiftOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

end Hashtree.Proofs.WinAvx2X8W
