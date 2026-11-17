import Hashtree.Proofs.WinAvx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip

/-! Residue 24: part b of `stripOk 24`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8WStrip

theorem stripOk_24_c5 : sliceCheck prog 4 (m8P 24) orcB 24 (stripK8 24 K211) (KTs 24) [] = true := by
  decide +kernel

theorem stripOk_24_c7 : decide (({ KTs 24 with mem := [], assume := [] } : State E Lin) = (KHs 24).substL tau8) = true := by
  decide +kernel

theorem stripOk_24_c8 : decide ((KTs 24).pc = 25) = true := by
  decide +kernel

theorem stripOk_24_c9 : decide ((KTs 24).assume = AT) = true := by
  decide +kernel

theorem stripOk_24_c10 : (KTs 24).mem.all logOkBW = true := by
  decide +kernel

theorem stripOk_24_c21 : (KTs 24).mem.all (fun p => decide (p.1.region ≠ rStack ∨ p.1.off.k < -368 - ((24 : Nat) : Int))) = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8WStrip
