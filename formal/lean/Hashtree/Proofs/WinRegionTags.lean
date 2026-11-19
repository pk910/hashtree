import Hashtree.Asm.RegionTags
import Hashtree.Kernels.X86Win.SseX1
import Hashtree.Kernels.X86Win.AvxX1
import Hashtree.Kernels.X86Win.Avx2X8

/-!
# R5: the region certificates of the push-saving windows kernels

Per-pc known regions of the general registers (`Asm/RegionTags`), from the windows call state
`entryWinRegs`, verified by `regCert` (`decide +kernel`): every memory base other than rsp
(rbp/rsi after the prologue, rcx, rdx) is a pointer of a region other than `rStack` wherever it
is used.  The tables have 6/6/10 segments (the bodies define their pointers once).
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinRegionTags

open Hashtree.Asm.RegionTags

def regsSse : RSegs :=
  [(0, some [some 0, some 2, some 1, some 3, some 3, some 3, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 6, some 0]),
   (22, some [some 0, some 2, some 1, some 3, some 3, some 3, some 0, some 0, none, some 0, some 0, some 0, some 0, some 0, some 6, some 0]),
   (23, some [none, some 2, some 1, none, some 3, none, none, none, none, none, none, none, none, none, none, none]),
   (26, some [none, some 2, some 1, none, some 3, some 4, none, none, none, none, none, none, none, none, none, none]),
   (4198, some [none, some 2, some 1, none, some 3, none, none, none, none, none, none, none, none, none, none, none]),
   (4217, none)]

theorem sse_regCert : regCert 4243 Hashtree.Kernels.X86Win.SseX1.prog regsSse entryWinRegs = true := by decide +kernel

def regsAvx1 : RSegs :=
  [(0, some [some 0, some 2, some 1, some 3, some 3, some 3, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 6, some 0]),
   (23, some [some 0, some 2, some 1, some 3, some 3, some 3, some 0, some 0, none, some 0, some 0, some 0, some 0, some 0, some 6, some 0]),
   (24, some [none, some 2, some 1, none, some 3, none, none, none, none, none, none, none, none, none, none, none]),
   (27, some [none, some 2, some 1, none, some 3, none, some 4, none, none, none, none, none, none, none, none, none]),
   (4068, some [none, some 2, some 1, none, some 3, none, none, none, none, none, none, none, none, none, none, none]),
   (4087, none)]

theorem avx1_regCert : regCert 4116 Hashtree.Kernels.X86Win.AvxX1.prog regsAvx1 entryWinRegs = true := by decide +kernel

def regsAvx2 : RSegs :=
  [(0, some [some 0, some 2, some 1, some 3, some 3, some 3, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 6, some 0]),
   (23, some [some 0, some 2, some 1, some 3, some 3, some 3, none, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 6, some 0]),
   (26, some [some 0, some 2, some 1, some 3, some 3, some 3, some 4, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 6, some 0]),
   (6086, some [some 0, some 2, some 1, some 3, some 3, some 3, none, some 0, some 0, some 0, some 0, some 0, some 0, some 0, some 6, some 0]),
   (6097, some [some 0, some 2, some 1, some 3, some 3, some 3, none, some 0, some 0, some 0, some 0, some 0, none, some 0, some 6, some 0]),
   (6098, some [some 0, some 2, some 1, some 3, some 3, some 3, none, some 0, some 0, some 0, some 0, some 0, none, none, some 6, some 0]),
   (6099, some [some 0, some 2, some 1, some 3, some 3, some 3, none, some 0, some 0, some 0, some 0, some 0, none, none, none, some 0]),
   (6100, some [some 0, some 2, some 1, some 3, some 3, some 3, none, some 0, some 0, some 0, some 0, some 0, none, none, none, none]),
   (6103, some [some 0, some 2, some 1, some 3, some 3, none, none, some 0, some 0, some 0, some 0, some 0, none, none, none, none]),
   (6104, none)]

theorem avx2_regCert : regCert 6107 Hashtree.Kernels.X86Win.Avx2X8.prog regsAvx2 entryWinRegs = true := by decide +kernel

end Hashtree.Proofs.WinRegionTags
