import Hashtree.Proofs.WinAvx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip

/-! Residue 8: part b of `stripOk 8`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8WStrip

theorem stripOk_8_c5 : sliceCheck prog 4 (m8P 8) orcB 24 (stripK8 8 K211) (KTs 8) [] = true := by
  decide +kernel

theorem stripOk_8_c7 : decide (({ KTs 8 with mem := [], assume := [] } : State E Lin) = (KHs 8).substL tau8) = true := by
  decide +kernel

theorem stripOk_8_c8 : decide ((KTs 8).pc = 25) = true := by
  decide +kernel

theorem stripOk_8_c9 : decide ((KTs 8).assume = AT) = true := by
  decide +kernel

theorem stripOk_8_c10 : (KTs 8).mem.all logOkBW = true := by
  decide +kernel

theorem stripOk_8_c21 : (KTs 8).mem.all (fun p => decide (p.1.region ≠ rStack ∨ p.1.off.k < -368 - ((8 : Nat) : Int))) = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8WStrip
