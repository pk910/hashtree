import Hashtree.Proofs.WinAvx2X8WShift
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W

/-! Residue 24: part c of `shiftOk 24`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8W

theorem shiftOk_24_c4 : sliceCheck prog 4 m8W orcEx 42 (shiftK8 24 K211) (KTE 24) [] = true := by
  decide +kernel

theorem shiftOk_24_c7 : decide ((KTE 24).tail = some "hashtree_sha256_avx_x4") = true := by
  decide +kernel

theorem shiftOk_24_c8 : decide ((KTE 24).err = none) = true := by
  decide +kernel

theorem shiftOk_24_c9 : decide ((KTE 24).halted = true) = true := by
  decide +kernel

theorem shiftOk_24_c10 : decide ((KTE 24).pc = 6103) = true := by
  decide +kernel

theorem shiftOk_24_c11 : decide ((KTE 24).assume = AX) = true := by
  decide +kernel

theorem shiftOk_24_c12 : decide ((KTE 24).gpr = exitGprW) = true := by
  decide +kernel

theorem shiftOk_24_c14 : (KTE 24).mem.all Hashtree.Proofs.WinLogW.logOkBW = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8W
