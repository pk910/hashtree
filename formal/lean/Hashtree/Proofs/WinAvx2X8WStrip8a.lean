import Hashtree.Proofs.WinAvx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip

/-! Residue 8: part a of `stripOk 8`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8WStrip

theorem stripOk_8_c1 : decide ((stripK8 8 K3).mem = []) = true := by
  decide +kernel

theorem stripOk_8_c2 : sliceCheck prog 4 (m8P 8) orcB 8 (KHs 8) (KH4s 8) T3 = true := by
  decide +kernel

theorem stripOk_8_c3 : sliceCheck prog 4 (m8P 8) orcB 8 (KH4s 8) (KH5s 8) T4 = true := by
  decide +kernel

theorem stripOk_8_c4 : sliceCheck prog 4 (m8P 8) orcB 8 (KH5s 8) (stripK8 8 K6) T5 = true := by
  decide +kernel

theorem stripOk_8_c11 : (KHs 8).nOnly = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8WStrip
