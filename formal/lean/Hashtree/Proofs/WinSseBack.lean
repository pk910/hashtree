import Hashtree.Proofs.WinX1Back
import Hashtree.Proofs.WinSseX1

/-!
# R5: the windows `sse_x1` epilogue replay

The instance of `WinX1Back` for the shipped `sse_x1` stream: restores at pcs 4198-4205 (non-VEX),
`add rsp, 192` at 4206, the nine pops at 4207-4215, `ret` at 4216 (`q0 = 4198`, `vex = false`).
The lookups come from the kernel-checked scans of `WinSseX1` (one new `decide +kernel` for the `ret`).
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinSseBack

open Hashtree.Asm Hashtree.Asm.X86
open Hashtree.Proofs.WinX1Front (pushRegs pushLog saveLog)
open Hashtree.Proofs.WinX1Back (restStep popReg backFinal)
open Hashtree.Proofs.WinShaniEpi (Outside)

abbrev winProg : Array Instr := Hashtree.Kernels.X86Win.SseX1.prog

theorem rest_lookup (m : Nat) (hm : m < 8) : winProg[4198 + m]? = some (restStep false m) := by
  have h := List.all_eq_true.mp Hashtree.Proofs.WinSseX1.sse_epilogue_restores m (List.mem_range.mpr hm)
  exact of_decide_eq_true h

theorem add_lookup : winProg[4198 + 8]? = some (.alu .add 64 rsp (.imm 192)) :=
  Hashtree.Proofs.WinSseX1.sse_rsp_balanced.2.1

theorem pop_lookup (k : Nat) (hk : k < 9) : winProg[4198 + 9 + k]? = some (.pop (popReg k)) := by
  have h := List.all_eq_true.mp Hashtree.Proofs.WinSseX1.sse_epilogue_pops k (List.mem_range.mpr hk)
  have h' := of_decide_eq_true h
  rw [show 4198 + 9 + k = 4207 + k from by omega]
  exact h'

theorem ret_lookup : winProg[4198 + 18]? = some .ret := by decide +kernel

/-- The state after the epilogue (`WinX1Back.backFinal false`). -/
abbrev backFinalS (t0 st : State W32 Int) (a : Addr Int) : State W32 Int := backFinal false t0 st a

/-- **The `sse_x1` epilogue**: nineteen steps from the body-exit state at pc 4198. -/
theorem run_back {mem0 : Addr Int → Cell W32 Int} {orc : Nat → Bool}
    (t0 st : State W32 Int) (a : Addr Int) (tail W : CLog)
    (hh : t0.halted = false) (hpc : t0.pc = 4198) (hrsp : t0.getG rsp = .ptr (a.plusI (-264)))
    (hlen : t0.gpr.length = 16)
    (hW : Outside (a.plusI (-200)) 208 W)
    (hmem : t0.mem = W ++ saveLog st (a.plusI (-264)) 8 (pushLog st a 9 tail))
    (hvlen : ∀ k, k < 8 → 4 ≤ (st.getV (6 + k)).length)
    (hretv : loadVal mem0 { t0 with mem := tail } a = .ok (.ptr (⟨rRet, Ctl.ofInt 0⟩ : Addr Int))) :
    run winProg 4 mem0 orc 19 t0 = backFinalS t0 st a :=
  Hashtree.Proofs.WinX1Back.run_back winProg 4198 false rest_lookup add_lookup pop_lookup ret_lookup
    t0 st a tail W hh hpc hrsp hlen hW hmem hvlen hretv

end Hashtree.Proofs.WinSseBack
