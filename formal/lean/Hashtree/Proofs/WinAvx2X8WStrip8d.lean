import Hashtree.Proofs.WinAvx2X8WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0

open Hashtree.Asm Hashtree.Asm.X86 Hashtree.Asm.X86Sym Hashtree.Asm.X86SymW
open Hashtree.Kernels.X86Win.Avx2X8
open Hashtree.Gen.WinAvx2X8P
open Hashtree.Proofs.WinLogW (logOkBW)
open Hashtree.Proofs.WinAvx2X8W
open Hashtree.Proofs.WinAvx2X8WStrip

/-! Residue 8: part d of `stripOk 8`, one kernel evaluation per conjunct (the conjuncts share no cache; a single evaluation of the whole bundle exceeds 80 GB). -/
namespace Hashtree.Proofs.WinAvx2X8WStrip

theorem stripOk_8_c19 : decide (({ KT 8 with mem := [], assume := [] } : State E Lin) = (KHs 8).substL tau8) = true := by
  decide +kernel

theorem stripOk_8_c20 : (pushC 8).all (savedIn (KT 8).mem) = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8WStrip
