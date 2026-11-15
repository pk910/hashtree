import Hashtree.Asm.X86Sym

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

end Hashtree.Asm.X86Sym
