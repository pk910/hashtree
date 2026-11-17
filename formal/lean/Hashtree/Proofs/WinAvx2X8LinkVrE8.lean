import Hashtree.Proofs.WinAvx2X8WShift
import Hashtree.Proofs.WinAvxX4CertFacts
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-! Residue 8: the vector file of the one-pass exit cut `KTE 8` is 32 x 16 (one kernel evaluation). -/
namespace Hashtree.Proofs.WinAvx2X8Link

theorem KTE_vr_8 : Hashtree.Proofs.WinAvxX4Cert.vrOk (Hashtree.Proofs.WinAvx2X8W.KTE 8) = true := by
  decide +kernel

end Hashtree.Proofs.WinAvx2X8Link
