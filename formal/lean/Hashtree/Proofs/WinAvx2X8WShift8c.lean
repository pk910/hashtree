import Hashtree.Proofs.WinAvx2X8WShift
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W

/-! Residue 8: part c of `shiftOk 8`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8W

theorem shiftOk_8_c4 : sliceCheck prog 4 m8W orcEx 42 (shiftK8 8 K211) (KTE 8) [] = true := by
  decide +kernel

theorem shiftOk_8_c7 : decide ((KTE 8).tail = some "hashtree_sha256_avx_x4") = true := by
  decide +kernel

theorem shiftOk_8_c8 : decide ((KTE 8).err = none) = true := by
  decide +kernel

theorem shiftOk_8_c9 : decide ((KTE 8).halted = true) = true := by
  decide +kernel

theorem shiftOk_8_c10 : decide ((KTE 8).pc = 6103) = true := by
  decide +kernel

theorem shiftOk_8_c11 : decide ((KTE 8).assume = AX) = true := by
  decide +kernel

theorem shiftOk_8_c12 : decide ((KTE 8).gpr = exitGprW) = true := by
  decide +kernel

theorem shiftOk_8_c14 : (KTE 8).mem.all Hashtree.Proofs.WinLogW.logOkBW = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8W
