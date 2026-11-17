import Hashtree.Proofs.WinAvx2X8WShift
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W

/-! Residue 8: part a of `shiftOk 8`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8W

theorem shiftOk_8_c1 : sliceCheck prog 4 m8W orcB 9 (x8A 8) (K2W 8) [] = true := by
  decide +kernel

theorem shiftOk_8_c2 : sliceCheck prog 4 m8W orcB 8 (K2W 8) (shiftK8 8 K3) T2 = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8W
