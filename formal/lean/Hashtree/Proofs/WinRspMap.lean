import Hashtree.Asm.RspMap
import Hashtree.Kernels.X86Win.SseX1
import Hashtree.Kernels.X86Win.AvxX1
import Hashtree.Kernels.X86Win.Avx2X8
import Hashtree.Kernels.X86Win.AvxX4
import Hashtree.Kernels.X86Win.Shani
import Hashtree.Kernels.X86Win.Avx512X16

/-!
# R5: the static rsp maps of the six windows kernels (frame-slot certificate, step 1)

Each map is a segment table (`Asm/RspMap`), produced by `RspMap.compute` and verified per pc
by `RspMap.ok` (`decide +kernel`; a linear sweep over the instruction list, the length passed explicitly): every rsp write is a supported form, successors carry the
stepped value, exits are at the entry rsp.  `slotsOk`: no rsp-based operand is indexed, and
every rsp-based access is at a mapped pc.  The unmapped pcs (`none` segments) are the `nop`
padding after unconditional jumps (dead code: avx_x4 705, 1736-1737; the trailing nops).

The frame slots (`RspMap.slots`, deduplicated `(base, offset, size)`): sse_x1/avx_x1 31 each
(nine 8-byte push slots at `-8..-72`, the return slot `0`, eight 16-byte xmm saves at `-200..-88`,
one 16-byte and twelve 4-byte scratch cells at `-264..-204`); avx2_x8 45 (the return slot and
the two push slots on base 0; on the aligned base 1: four 8-byte r12-r15 saves at `-352..-328`,
ten 32-byte ymm saves at `-320..-32`, and twenty-seven 32-byte scratch cells at `-1248..-384`);
avx_x4 35 (return slot, ten xmm saves at `-184..-40`, twenty-four 16-byte scratch cells at
`-568..-200`); shani 15 (return slot, fourteen 16-byte cells at `-248..-40`); avx512 1 (the
return slot only).
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinRspMap

open Hashtree.Asm.RspMap

/-- sse_x1: nine pushes (pcs 0-8), `sub rsp, 192` (9), body at `-264`, epilogue 4207-4216. -/
def segsSse : List (Nat × Option Fact) :=
  [(0, some { sp := (0, 0) }), (1, some { sp := (0, -8) }), (2, some { sp := (0, -16) }),
   (3, some { sp := (0, -24) }), (4, some { sp := (0, -32) }), (5, some { sp := (0, -40) }),
   (6, some { sp := (0, -48) }), (7, some { sp := (0, -56) }), (8, some { sp := (0, -64) }),
   (9, some { sp := (0, -72) }), (10, some { sp := (0, -264) }),
   (4207, some { sp := (0, -72) }), (4208, some { sp := (0, -64) }), (4209, some { sp := (0, -56) }),
   (4210, some { sp := (0, -48) }), (4211, some { sp := (0, -40) }), (4212, some { sp := (0, -32) }),
   (4213, some { sp := (0, -24) }), (4214, some { sp := (0, -16) }), (4215, some { sp := (0, -8) }),
   (4216, some { sp := (0, 0) }), (4217, none)]

theorem sse_size : Hashtree.Kernels.X86Win.SseX1.prog.size = 4243 := by decide +kernel
theorem sse_ok : ok 4243 Hashtree.Kernels.X86Win.SseX1.prog segsSse = true := by decide +kernel
theorem sse_slotsOk : slotsOk Hashtree.Kernels.X86Win.SseX1.prog segsSse = true := by decide +kernel
theorem sse_slots : (slots Hashtree.Kernels.X86Win.SseX1.prog segsSse).length = 31 := by decide +kernel

/-- avx_x1: `nop`, nine pushes (pcs 1-9), `sub rsp, 192` (10), body at `-264`, epilogue 4077-4086. -/
def segsAvx1 : List (Nat × Option Fact) :=
  [(0, some { sp := (0, 0) }), (2, some { sp := (0, -8) }), (3, some { sp := (0, -16) }),
   (4, some { sp := (0, -24) }), (5, some { sp := (0, -32) }), (6, some { sp := (0, -40) }),
   (7, some { sp := (0, -48) }), (8, some { sp := (0, -56) }), (9, some { sp := (0, -64) }),
   (10, some { sp := (0, -72) }), (11, some { sp := (0, -264) }),
   (4077, some { sp := (0, -72) }), (4078, some { sp := (0, -64) }), (4079, some { sp := (0, -56) }),
   (4080, some { sp := (0, -48) }), (4081, some { sp := (0, -40) }), (4082, some { sp := (0, -32) }),
   (4083, some { sp := (0, -24) }), (4084, some { sp := (0, -16) }), (4085, some { sp := (0, -8) }),
   (4086, some { sp := (0, 0) }), (4087, none)]

theorem avx1_size : Hashtree.Kernels.X86Win.AvxX1.prog.size = 4116 := by decide +kernel
theorem avx1_ok : ok 4116 Hashtree.Kernels.X86Win.AvxX1.prog segsAvx1 = true := by decide +kernel
theorem avx1_slotsOk : slotsOk Hashtree.Kernels.X86Win.AvxX1.prog segsAvx1 = true := by decide +kernel
theorem avx1_slots : (slots Hashtree.Kernels.X86Win.AvxX1.prog segsAvx1).length = 31 := by decide +kernel

/-- avx2_x8: `push rbp; push rsi; mov rbp, rsp; and rsp, -32` (base 1), `sub rsp, 1248`;
`mov rsp, rbp; pop rsi; pop rbp; ret` at 6100-6103. -/
def segsAvx2 : List (Nat × Option Fact) :=
  [(0, some { sp := (0, 0) }), (5, some { sp := (0, -8) }), (6, some { sp := (0, -16) }),
   (7, some { sp := (0, -16), saved := some (0, -16) }), (8, some { sp := (1, 0), saved := some (0, -16) }),
   (9, some { sp := (1, -1248), saved := some (0, -16) }),
   (6101, some { sp := (0, -16), saved := some (0, -16) }), (6102, some { sp := (0, -8), saved := some (0, -16) }),
   (6103, some { sp := (0, 0) }), (6104, none)]

theorem avx2_size : Hashtree.Kernels.X86Win.Avx2X8.prog.size = 6107 := by decide +kernel
theorem avx2_ok : ok 6107 Hashtree.Kernels.X86Win.Avx2X8.prog segsAvx2 = true := by decide +kernel
theorem avx2_slotsOk : slotsOk Hashtree.Kernels.X86Win.Avx2X8.prog segsAvx2 = true := by decide +kernel
theorem avx2_slots : (slots Hashtree.Kernels.X86Win.Avx2X8.prog segsAvx2).length = 45 := by decide +kernel

/-- avx_x4: `sub rsp, 568` at 4 (after the `c = 0` return), `add rsp, 568` at 4161, tail at 4162;
705 and 1736-1737 are dead `nop`s after `jmp`s. -/
def segsAvx4 : List (Nat × Option Fact) :=
  [(0, some { sp := (0, 0) }), (5, some { sp := (0, -568) }), (705, none), (706, some { sp := (0, -568) }),
   (1736, none), (1738, some { sp := (0, -568) }), (4162, some { sp := (0, 0) })]

theorem avx4_size : Hashtree.Kernels.X86Win.AvxX4.prog.size = 4163 := by decide +kernel
theorem avx4_ok : ok 4163 Hashtree.Kernels.X86Win.AvxX4.prog segsAvx4 = true := by decide +kernel
theorem avx4_slotsOk : slotsOk Hashtree.Kernels.X86Win.AvxX4.prog segsAvx4 = true := by decide +kernel
theorem avx4_slots : (slots Hashtree.Kernels.X86Win.AvxX4.prog segsAvx4).length = 35 := by decide +kernel

/-- shani: `sub rsp, 248` at 0, `add rsp, 248` at 689, `ret` at 690. -/
def segsShani : List (Nat × Option Fact) :=
  [(0, some { sp := (0, 0) }), (1, some { sp := (0, -248) }), (690, some { sp := (0, 0) }), (691, none)]

theorem shani_size : Hashtree.Kernels.X86Win.Shani.prog.size = 702 := by decide +kernel
theorem shani_ok : ok 702 Hashtree.Kernels.X86Win.Shani.prog segsShani = true := by decide +kernel
theorem shani_slotsOk : slotsOk Hashtree.Kernels.X86Win.Shani.prog segsShani = true := by decide +kernel
theorem shani_slots : (slots Hashtree.Kernels.X86Win.Shani.prog segsShani).length = 15 := by decide +kernel

/-- avx512_x16: no frame; the tail jump and the `c = 0` return are at the entry rsp. -/
def segsAvx512 : List (Nat × Option Fact) := [(0, some { sp := (0, 0) }), (3247, none)]

theorem avx512_size : Hashtree.Kernels.X86Win.Avx512X16.prog.size = 3292 := by decide +kernel
theorem avx512_ok : ok 3292 Hashtree.Kernels.X86Win.Avx512X16.prog segsAvx512 = true := by decide +kernel
theorem avx512_slotsOk : slotsOk Hashtree.Kernels.X86Win.Avx512X16.prog segsAvx512 = true := by decide +kernel
theorem avx512_slots : (slots Hashtree.Kernels.X86Win.Avx512X16.prog segsAvx512).length = 1 := by decide +kernel

end Hashtree.Proofs.WinRspMap
