import Hashtree.Proofs.WinAvx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip

/-! Residue 24: part a of `stripOk 24`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8WStrip

theorem stripOk_24_c1 : decide ((stripK8 24 K3).mem = []) = true := by
  decide +kernel

theorem stripOk_24_c2 : sliceCheck prog 4 (m8P 24) orcB 8 (KHs 24) (KH4s 24) T3 = true := by
  decide +kernel

theorem stripOk_24_c3 : sliceCheck prog 4 (m8P 24) orcB 8 (KH4s 24) (KH5s 24) T4 = true := by
  decide +kernel

theorem stripOk_24_c4 : sliceCheck prog 4 (m8P 24) orcB 8 (KH5s 24) (stripK8 24 K6) T5 = true := by
  decide +kernel

theorem stripOk_24_c11 : (KHs 24).nOnly = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8WStrip
