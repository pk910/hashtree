import Hashtree.Proofs.WinAvx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip

/-! Residue 24: part c of `stripOk 24`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8WStrip

theorem stripOk_24_c6 : sliceCheck prog 4 (m8P 24) orcEx 42 (stripK8 24 K211) (KTEs 24) [] = true := by
  decide +kernel

theorem stripOk_24_c12 : decide ((KTEs 24).tail = some "hashtree_sha256_avx_x4") = true := by
  decide +kernel

theorem stripOk_24_c13 : decide ((KTEs 24).err = none) = true := by
  decide +kernel

theorem stripOk_24_c14 : decide ((KTEs 24).halted = true) = true := by
  decide +kernel

theorem stripOk_24_c15 : decide ((KTEs 24).pc = 6103) = true := by
  decide +kernel

theorem stripOk_24_c16 : decide ((KTEs 24).assume = AX) = true := by
  decide +kernel

theorem stripOk_24_c17 : (KTEs 24).mem.all logOkBW = true := by
  decide +kernel

theorem stripOk_24_c18 : decide ((KTEs 24).gpr = exitGprW) = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8WStrip
