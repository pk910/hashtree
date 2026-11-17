import Hashtree.Proofs.WinAvx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip

/-! Residue 24: part d of `stripOk 24`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8WStrip

theorem stripOk_24_c19 : decide (({ KT 24 with mem := [], assume := [] } : State E Lin) = (KHs 24).substL tau8) = true := by
  decide +kernel

theorem stripOk_24_c20 : (pushC 24).all (savedIn (KT 24).mem) = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8WStrip
