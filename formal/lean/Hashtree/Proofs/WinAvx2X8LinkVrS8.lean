import Hashtree.Proofs.WinAvx2X8WStripDefs
import Hashtree.Proofs.WinAvxX4CertFacts
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-! Residue 8: the vector file of the loop exit cut `KTEs 8` is 32 x 16 (one kernel evaluation). -/
namespace Hashtree.Proofs.WinAvx2X8Link

theorem KTEs_vr_8 : Hashtree.Proofs.WinAvxX4Cert.vrOk (Hashtree.Proofs.WinAvx2X8WStrip.KTEs 8) = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8Link
