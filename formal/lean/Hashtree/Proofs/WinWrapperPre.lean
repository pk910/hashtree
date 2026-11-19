import Hashtree.Proofs.WrapperPre
import Hashtree.Proofs.WrapperEntry
import Hashtree.Kernels.X86Win.WrapperWindows

/-!
# R5: the windows wrapper's prefix and call state (symbolic, decided)

The windows/amd64 Go wrapper `HashtreeHash` (model in `Kernels/X86Win/WrapperWindows`):
its ABI0 entry state, its prefix `pre F` (assembler prologue, argument loads, `MOVQ SP, BX ;
ADDQ $2048, SP`), the `ANDQ $-32, SP` alignment, the call's return marker, and the
windows kernel call state.

Symbols, as in the linux model: 0 input, 1 output, 2 count, (3, 4 flags), 5 `rbx`,
6 the caller's frame pointer, 8 g, 9 `SPe` (entry `rsp`; the return address is at `[SPe]`,
the argument slots at `SPe+8..SPe+32`), 11/12 the caller's `r13`/`r15`, 13 the incoming
`r8` (which the wrapper saves in `r12` and restores after the call).  Windows ABI0:
arguments arrive in `rcx`, `rdx`, `r8`; the wrapper loads them from the ABI0 slots.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.WinWrapper
open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.WrapperWindows
open Hashtree.Proofs.WrapperAmd64 (m0W l10 sAt_eval getG_of)

/-- The windows wrapper's ABI0 entry state: `rsp = SPe`, `rcx`/`rdx`/`r8` the argument
registers, the caller's frame pointer in `rbp`, g in `r14`, the incoming `r8` value
(symbol 13) saved by the wrapper in `r12`, and caller numbers in the other registers. -/
def wEntryW : State E Lin :=
  let g := (List.range 16).map fun i =>
    if i = 4 then Val.ptr ⟨rStack, sAt 0⟩
    else if i = 1 then Val.ptr ⟨rOut, Lin.sym 1⟩
    else if i = 2 then Val.ptr ⟨rIn, Lin.sym 0⟩
    else if i = 8 then Val.ptr ⟨rNum, Lin.sym 13⟩
    else if i = 3 then Val.ptr ⟨rStack, Lin.sym 5⟩
    else if i = 5 then Val.ptr ⟨rStack, Lin.sym 6⟩
    else if i = 12 then Val.ptr ⟨rNum, Lin.sym 7⟩
    else if i = 13 then Val.ptr ⟨rNum, Lin.sym 11⟩
    else if i = 14 then Val.ptr ⟨rG, Lin.sym 8⟩
    else if i = 15 then Val.ptr ⟨rNum, Lin.sym 12⟩
    else Val.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))
  { gpr := g, vr := (List.range 32).map (fun i => (List.range 16).map fun l => .var (.n (vId i l))),
    flags := none, mem := [], pc := 0, halted := false, tail := none, err := none, assume := [] }

/-- The windows kernel call state at a wrapper `CALL`: `rcx` = output, `rdx` = input,
`r8` = count, the kernel's entry `rsp` (symbol 9), the wrapper's frame base in `rbx`
(symbol 5), its frame pointer in `rbp` (symbol 6), the saved incoming `r8` in `r12`
(symbol 7, `rNum`), g in `r14`, and caller values in the other callee-saved registers. -/
def entryWin : State E Lin :=
  let g := (List.range 16).map fun i =>
    if i = 4 then Val.ptr ⟨rStack, sAt 0⟩
    else if i = 1 then Val.ptr ⟨rOut, Lin.sym 1⟩
    else if i = 2 then Val.ptr ⟨rIn, Lin.sym 0⟩
    else if i = 8 then Val.ptr ⟨rNum, Lin.sym 2⟩
    else if i = 3 then Val.ptr ⟨rStack, Lin.sym 5⟩
    else if i = 5 then Val.ptr ⟨rStack, Lin.sym 6⟩
    else if i = 12 then Val.ptr ⟨rNum, Lin.sym 7⟩
    else if i = 13 then Val.ptr ⟨rNum, Lin.sym 11⟩
    else if i = 14 then Val.ptr ⟨rG, Lin.sym 8⟩
    else if i = 15 then Val.ptr ⟨rNum, Lin.sym 12⟩
    else Val.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))
  { gpr := g, vr := (List.range 32).map (fun i => (List.range 16).map fun l => .var (.n (vId i l))),
    flags := none, mem := [], pc := 0, halted := false, tail := none, err := none, assume := [] }

/-- The wrapper's prefix, symbolically. -/
def KpreW (F : Int) : State E Lin := abstract (run (pre F) 4 m0W (fun _ => false) 9 wEntryW)

/-- The wrapper's call rsp, symbolically: `SPe + 2040 - F` before the alignment. -/
def aW (F : Int) : Lin := sAt (2040 - F)

theorem slicePreW_shipped : sliceCheck (pre shippedFrame) 4 m0W (fun _ => false) 9 wEntryW
    (KpreW shippedFrame) [] = true := by decide +kernel

theorem slicePreW_fixed : sliceCheck (pre fixedFrame) 4 m0W (fun _ => false) 9 wEntryW
    (KpreW fixedFrame) [] = true := by decide +kernel

theorem KpreW_shipped_assume : (KpreW shippedFrame).assume = [] := by decide +kernel
theorem KpreW_fixed_assume : (KpreW fixedFrame).assume = [] := by decide +kernel

theorem KpreW_shipped_rsp : (KpreW shippedFrame).gpr[4]? = some (.ptr ⟨rStack, aW shippedFrame⟩) := by decide +kernel
theorem KpreW_fixed_rsp : (KpreW fixedFrame).gpr[4]? = some (.ptr ⟨rStack, aW fixedFrame⟩) := by decide +kernel

theorem KpreW_shipped_bx : (KpreW shippedFrame).gpr[3]? = some (.ptr ⟨rStack, sAt (-8 - shippedFrame)⟩) := by decide +kernel
theorem KpreW_fixed_bx : (KpreW fixedFrame).gpr[3]? = some (.ptr ⟨rStack, sAt (-8 - fixedFrame)⟩) := by decide +kernel

theorem KpreW_shipped_bp : (KpreW shippedFrame).gpr[5]? = some (.ptr ⟨rStack, sAt (-8)⟩) := by decide +kernel
theorem KpreW_fixed_bp : (KpreW fixedFrame).gpr[5]? = some (.ptr ⟨rStack, sAt (-8)⟩) := by decide +kernel

theorem KpreW_shipped_r12 : (KpreW shippedFrame).gpr[12]? = some (.ptr ⟨rNum, Lin.sym 13⟩) := by decide +kernel
theorem KpreW_fixed_r12 : (KpreW fixedFrame).gpr[12]? = some (.ptr ⟨rNum, Lin.sym 13⟩) := by decide +kernel

theorem KpreW_shipped_r8 : (KpreW shippedFrame).gpr[8]? = some (.ptr ⟨rNum, Lin.sym 2⟩) := by decide +kernel
theorem KpreW_fixed_r8 : (KpreW fixedFrame).gpr[8]? = some (.ptr ⟨rNum, Lin.sym 2⟩) := by decide +kernel

theorem KpreW_shipped_r1 : (KpreW shippedFrame).gpr[1]? = some (.ptr ⟨rOut, Lin.sym 1⟩) := by decide +kernel
theorem KpreW_fixed_r1 : (KpreW fixedFrame).gpr[1]? = some (.ptr ⟨rOut, Lin.sym 1⟩) := by decide +kernel

theorem KpreW_shipped_r2 : (KpreW shippedFrame).gpr[2]? = some (.ptr ⟨rIn, Lin.sym 0⟩) := by decide +kernel
theorem KpreW_fixed_r2 : (KpreW fixedFrame).gpr[2]? = some (.ptr ⟨rIn, Lin.sym 0⟩) := by decide +kernel

theorem KpreW_shipped_pc : (KpreW shippedFrame).pc = 9 := by decide +kernel
theorem KpreW_fixed_pc : (KpreW fixedFrame).pc = 9 := by decide +kernel

theorem KpreW_shipped_halted : (KpreW shippedFrame).halted = false := by decide +kernel
theorem KpreW_fixed_halted : (KpreW fixedFrame).halted = false := by decide +kernel

theorem KpreW_shipped_err : (KpreW shippedFrame).err = none := by decide +kernel
theorem KpreW_fixed_err : (KpreW fixedFrame).err = none := by decide +kernel

theorem KpreW_shipped_len : (KpreW shippedFrame).gpr.length = 16 := by decide +kernel
theorem KpreW_fixed_len : (KpreW fixedFrame).gpr.length = 16 := by decide +kernel

theorem entryW_nOnly : wEntryW.nOnly = true := by decide +kernel
theorem entryWin_nOnly : entryWin.nOnly = true := by decide +kernel

/-- After the alignment: `rsp = s10 + 8` (symbol 10 names the aligned call rsp `A - 8`). -/
def KalW (F : Int) : State E Lin :=
  { KpreW F with gpr := (KpreW F).gpr.set 4 (.ptr ⟨rStack, l10 8⟩), flags := none, pc := 10 }

def aKW : Addr Lin := ⟨rStack, l10 8⟩

/-- The kernel's entry state: the wrapper's aligned call rsp, the return marker pushed at it. -/
def KCW (F : Int) : State E Lin :=
  { (storeVal (KalW F) (aKW.plusI (-8)) (.ptr ⟨rRet, Lin.ofInt 0⟩)).setG 4
      (.ptr (aKW.plusI (-8))) with pc := 0 }

/-- Kernel symbols in terms of the wrapper's: input, output, count, flags, flags, rbx =
`SPe - 8 - F`, rbp = `SPe - 8`, r12 = the incoming `r8` (symbol 13), g, rsp. -/
def tauCW (F : Int) : List Lin :=
  [Lin.sym 0, Lin.sym 1, Lin.sym 2, Lin.sym 3, Lin.sym 4, sAt (-8 - F), sAt (-8),
    Lin.sym 13, Lin.sym 8, l10 0]

theorem KCW_shape_shipped : { KCW shippedFrame with mem := [], assume := [] } =
    entryWin.substL (tauCW shippedFrame) := by decide +kernel

theorem KCW_shape_fixed : { KCW fixedFrame with mem := [], assume := [] } =
    entryWin.substL (tauCW fixedFrame) := by decide +kernel

/-- The call marker cell at the aligned call `rsp` itself (offset `l10 0`) is in the call log. -/
theorem KCW_head_shipped :
    ((⟨rStack, l10 0⟩ : Addr Lin), Cell.pb ⟨rRet, Lin.ofInt 0⟩ 0) ∈
      (KCW shippedFrame).mem.take 8 := by decide +kernel
theorem KCW_head_fixed :
    ((⟨rStack, l10 0⟩ : Addr Lin), Cell.pb ⟨rRet, Lin.ofInt 0⟩ 0) ∈
      (KCW fixedFrame).mem.take 8 := by decide +kernel

end Hashtree.Proofs.WinWrapper
