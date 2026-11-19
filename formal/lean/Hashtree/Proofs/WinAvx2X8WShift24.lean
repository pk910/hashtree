import Hashtree.Proofs.WinAvx2X8WShift24a
import Hashtree.Proofs.WinAvx2X8WShift24b
import Hashtree.Proofs.WinAvx2X8WShift24c
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.WinAvx2X8W

/-- Residue 24: the cut facts, assembled from the per-conjunct kernel checks. -/
theorem shiftOk_24 : shiftOk 24 = true := by
  unfold shiftOk
  simp only [shiftOk_24_c1, shiftOk_24_c2, shiftOk_24_c3, shiftOk_24_c4, shiftOk_24_c5, shiftOk_24_c6, shiftOk_24_c7, shiftOk_24_c8, shiftOk_24_c9, shiftOk_24_c10, shiftOk_24_c11, shiftOk_24_c12, shiftOk_24_c13, shiftOk_24_c14, Bool.and_true]

end Hashtree.Proofs.WinAvx2X8W
