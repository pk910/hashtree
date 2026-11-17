import Hashtree.Proofs.WinAvx2X8WShift
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W

/-! Residue 24: part a of `shiftOk 24`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8W

theorem shiftOk_24_c1 : sliceCheck prog 4 m8W orcB 9 (x8A 24) (K2W 24) [] = true := by
  decide +kernel

theorem shiftOk_24_c2 : sliceCheck prog 4 m8W orcB 8 (K2W 24) (shiftK8 24 K3) T2 = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8W
