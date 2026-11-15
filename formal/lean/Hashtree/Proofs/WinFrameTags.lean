import Hashtree.Asm.FrameTags
import Hashtree.Proofs.WinRspMap

/-!
# R5: the frame-slot certificates of the push-saving windows kernels (sse_x1, avx_x1, avx2_x8)

Tag tables (`Asm/FrameTags`, computed by `tags` and verified per pc by `tagCert`, `decide +kernel`)
for the Win64 callee-saved set `[3, 5, 6, 7, 12, 13, 14, 15]`.  sse_x1/avx_x1: the nine pushes
tag the slots `-8..-72` (push `r8` at `-16` is untagged), the body from pc 23/24 keeps only the
slot tags (every callee-saved register is written before it is read), the nine pops re-tag the
registers, and at `ret` every callee-saved register is tagged with itself.  avx2_x8: `rbp`/`rsi`
pushed on base 0 (`-8`, `-16`), `r12`-`r15` saved with `mov [rsp+k]` on the aligned base 1
(`-352..-328`), `rbx` and `rdi` never touched (tagged throughout), restores at 6096-6102.
-/

set_option autoImplicit false

namespace Hashtree.Proofs.WinFrameTags

open Hashtree.Asm.FrameTags Hashtree.Asm.RspMap Hashtree.Proofs.WinRspMap

/-- The Win64 callee-saved general registers. -/
def cs : List Nat := [3, 5, 6, 7, 12, 13, 14, 15]

def tagsSse : TagSegs :=
  [(0, some [(.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (1, some [(.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (3, some [(.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (4, some [(.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (5, some [(.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (6, some [(.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (7, some [(.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (8, some [(.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (9, some [(.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (23, some [(.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4208, some [(.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4209, some [(.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4210, some [(.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4211, some [(.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4212, some [(.reg 5, 5), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4213, some [(.reg 7, 7), (.reg 5, 5), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4214, some [(.reg 6, 6), (.reg 7, 7), (.reg 5, 5), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4216, some [(.reg 3, 3), (.reg 6, 6), (.reg 7, 7), (.reg 5, 5), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4217, none)]

theorem sse_tagCert : tagCert 4243 Hashtree.Kernels.X86Win.SseX1.prog segsSse tagsSse cs = true := by decide +kernel
theorem sse_entry : atT tagsSse 0 = some (entryTags cs) := by decide +kernel
theorem sse_exitOk : (atT tagsSse 4216).map (exitOk cs) = some true := by decide +kernel

def tagsAvx1 : TagSegs :=
  [(0, some [(.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (2, some [(.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (4, some [(.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (5, some [(.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (6, some [(.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (7, some [(.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (8, some [(.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (9, some [(.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (10, some [(.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (24, some [(.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4078, some [(.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4079, some [(.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4080, some [(.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4081, some [(.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4082, some [(.reg 5, 5), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4083, some [(.reg 7, 7), (.reg 5, 5), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4084, some [(.reg 6, 6), (.reg 7, 7), (.reg 5, 5), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4086, some [(.reg 3, 3), (.reg 6, 6), (.reg 7, 7), (.reg 5, 5), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15), (.slot (0, -72, 8), 15), (.slot (0, -64, 8), 14), (.slot (0, -56, 8), 13), (.slot (0, -48, 8), 12), (.slot (0, -40, 8), 5), (.slot (0, -32, 8), 7), (.slot (0, -24, 8), 6), (.slot (0, -8, 8), 3)]),
   (4087, none)]

theorem avx1_tagCert : tagCert 4116 Hashtree.Kernels.X86Win.AvxX1.prog segsAvx1 tagsAvx1 cs = true := by decide +kernel
theorem avx1_entry : atT tagsAvx1 0 = some (entryTags cs) := by decide +kernel
theorem avx1_exitOk : (atT tagsAvx1 4086).map (exitOk cs) = some true := by decide +kernel

def tagsAvx2 : TagSegs :=
  [(0, some [(.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (5, some [(.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (6, some [(.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 5, 5), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (7, some [(.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (10, some [(.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (11, some [(.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (12, some [(.slot (1, -336, 8), 14), (.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (13, some [(.slot (1, -328, 8), 15), (.slot (1, -336, 8), 14), (.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 6, 6), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (23, some [(.slot (1, -328, 8), 15), (.slot (1, -336, 8), 14), (.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 7, 7), (.reg 12, 12), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (6097, some [(.reg 12, 12), (.slot (1, -328, 8), 15), (.slot (1, -336, 8), 14), (.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 7, 7), (.reg 13, 13), (.reg 14, 14), (.reg 15, 15)]),
   (6098, some [(.reg 13, 13), (.reg 12, 12), (.slot (1, -328, 8), 15), (.slot (1, -336, 8), 14), (.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 7, 7), (.reg 14, 14), (.reg 15, 15)]),
   (6099, some [(.reg 14, 14), (.reg 13, 13), (.reg 12, 12), (.slot (1, -328, 8), 15), (.slot (1, -336, 8), 14), (.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 7, 7), (.reg 15, 15)]),
   (6100, some [(.reg 15, 15), (.reg 14, 14), (.reg 13, 13), (.reg 12, 12), (.slot (1, -328, 8), 15), (.slot (1, -336, 8), 14), (.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 7, 7)]),
   (6102, some [(.reg 6, 6), (.reg 15, 15), (.reg 14, 14), (.reg 13, 13), (.reg 12, 12), (.slot (1, -328, 8), 15), (.slot (1, -336, 8), 14), (.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 7, 7)]),
   (6103, some [(.reg 5, 5), (.reg 6, 6), (.reg 15, 15), (.reg 14, 14), (.reg 13, 13), (.reg 12, 12), (.slot (1, -328, 8), 15), (.slot (1, -336, 8), 14), (.slot (1, -344, 8), 13), (.slot (1, -352, 8), 12), (.slot (0, -16, 8), 6), (.slot (0, -8, 8), 5), (.reg 3, 3), (.reg 7, 7)]),
   (6104, none)]

theorem avx2_tagCert : tagCert 6107 Hashtree.Kernels.X86Win.Avx2X8.prog segsAvx2 tagsAvx2 cs = true := by decide +kernel
theorem avx2_entry : atT tagsAvx2 0 = some (entryTags cs) := by decide +kernel
theorem avx2_exitOk : (atT tagsAvx2 6103).map (exitOk cs) = some true := by decide +kernel

end Hashtree.Proofs.WinFrameTags
