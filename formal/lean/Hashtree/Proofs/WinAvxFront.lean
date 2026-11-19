import Hashtree.Proofs.WinX1Front
import Hashtree.Kernels.X86Win.AvxX1

/-!
# R5: the windows `avx_x1` prologue replay

The instance of `WinX1Front` for the shipped `avx_x1` stream: `endbr64` (`nop`) at pc 0, the nine
pushes at 1-9, `sub rsp, 192` at 10 and the eight `xmm6`-`xmm13` saves at 11-18 (`p0 = 1`).
`run_front`: from a state with `rsp = a` at pc 0, the state after 19 steps is `frontSt st a 8`
(`rsp = a - 264`, the flags of the `sub`, the save slots over the push cells, pc 19).
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinAvxFront

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinX1Front (pushRegs saveStep pushLog saveLog)

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.AvxX1.prog

theorem nop_lookup : winProg[0]? = some .nop := by decide +kernel

theorem push_lookup (k : Nat) (hk : k < 9) : winProg[0 + 1 + k]? = some (.push (pushRegs.getD k 0)) := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem sub_lookup : winProg[0 + 1 + 9]? = some (.sub 64 4 (.imm 192)) := by decide +kernel

theorem save_lookup (m : Nat) (hm : m < 8) : winProg[0 + 1 + 10 + m]? = some (saveStep m) := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- The state after the nine pushes, the `sub` and `m` saves (pc `11 + m`). -/
abbrev frontSt (st : State W32 Int) (a : Addr Int) (m : Nat) : State W32 Int :=
  Hashtree.Proofs.WinX1Front.frontSt (0 + 1) st a m

/-- **The `avx_x1` prologue** (19 steps including the `endbr64`). -/
theorem run_front (mem0 : Addr Int → Cell W32 Int) (orc : Nat → Bool) (st : State W32 Int) (a : Addr Int)
    (hh : st.halted = false) (h4 : st.getG rsp = .ptr a) (hlen : st.gpr.length = 16) :
    run winProg 4 mem0 orc 19 { st with pc := 0 } = frontSt st a 8 :=
  Hashtree.Proofs.WinX1Front.run_front_nop winProg 0 mem0 orc nop_lookup push_lookup sub_lookup save_lookup st a hh h4 hlen

end Hashtree.Proofs.WinAvxFront
