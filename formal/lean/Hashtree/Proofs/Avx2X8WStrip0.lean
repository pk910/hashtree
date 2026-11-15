import Hashtree.Proofs.Avx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86.Avx2X8
open Hashtree.Gen.Avx2X8P
open Hashtree.Proofs.AvxX4LoopWFrame (logOkBW)
open Hashtree.Proofs.Avx2X8Align
open Hashtree.Proofs.Avx2X8WShift

namespace Hashtree.Proofs.Avx2X8WStrip

/-- Residue 0: the stripped-cut facts, one kernel evaluation. -/
theorem stripOk_0 : stripOk 0 = true := by decide +kernel

end Hashtree.Proofs.Avx2X8WStrip
