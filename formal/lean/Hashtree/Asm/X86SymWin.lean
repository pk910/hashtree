import Hashtree.Asm.X86Sym
import Hashtree.Asm.X86SymW

/-!
The Win64 call state of the slice certificates (the analogue of `entryS` for the windows
kernels): `rcx`/`rdx`/`r8` hold the output pointer, the input pointer and the count under the
same symbols `sOut`/`sIn`/`sCnt`, `rsp` the concrete `sp0`; every other register and every vector
lane is a fresh variable.  A separate module so that adding it rebuilds nothing.
-/

namespace Hashtree.Asm.X86Sym

open Hashtree.Asm Hashtree.Asm.X86

def entrySW (sp0 : Int) : State E Lin :=
  let g := (List.range 16).map fun i =>
    if i = 1 then Val.ptr ⟨rOut, Lin.sym sOut⟩
    else if i = 2 then Val.ptr ⟨rIn, Lin.sym sIn⟩
    else if i = 8 then Val.ptr ⟨rNum, Lin.sym sCnt⟩
    else if i = 4 then Val.ptr ⟨rStack, Lin.ofInt sp0⟩
    else Val.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))
  { gpr := g, vr := (List.range 32).map (fun i => (List.range 16).map fun l => .var (.n (vId i l))),
    flags := none, mem := [], pc := 0, halted := false, tail := none, err := none, assume := [] }

/-- The windows wrapper's kernel call state (the symbolic twin of `Proofs.WinWrapper.entryWin`):
`rcx`/`rdx`/`r8` = output/input/count, `rsp = σ9`, `rbx`/`rbp` the wrapper's stack pointers (symbols
5, 6), `r12` the saved incoming `r8` (symbol 7), `r13`/`r15` the caller's values (symbols 11, 12),
`r14` = g (symbol 8); every other register and every vector lane a fresh variable.  The loop-mode
windows certificates (`x86loop1w wsse|wavx`) start here. -/
def entryWinS : State E Lin :=
  let g := (List.range 16).map fun i =>
    if i = 4 then Val.ptr ⟨rStack, X86SymW.sAt 0⟩
    else if i = 1 then Val.ptr ⟨rOut, Lin.sym 1⟩
    else if i = 2 then Val.ptr ⟨rIn, Lin.sym 0⟩
    else if i = 8 then Val.ptr ⟨rNum, Lin.sym 2⟩
    else if i = 3 then Val.ptr ⟨rStack, Lin.sym 5⟩
    else if i = 5 then Val.ptr ⟨rStack, Lin.sym 6⟩
    else if i = 12 then Val.ptr ⟨rNum, Lin.sym 7⟩
    else if i = 13 then Val.ptr ⟨rNum, Lin.sym 11⟩
    else if i = 14 then Val.ptr ⟨X86SymW.rG, Lin.sym 8⟩
    else if i = 15 then Val.ptr ⟨rNum, Lin.sym 12⟩
    else Val.num (.var (.n (gId i 0))) (.var (.n (gId i 1)))
  { gpr := g, vr := (List.range 32).map (fun i => (List.range 16).map fun l => .var (.n (vId i l))),
    flags := none, mem := [], pc := 0, halted := false, tail := none, err := none, assume := [] }

end Hashtree.Asm.X86Sym
