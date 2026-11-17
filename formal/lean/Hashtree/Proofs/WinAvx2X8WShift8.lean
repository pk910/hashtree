import Hashtree.Proofs.WinAvx2X8WShift8a
import Hashtree.Proofs.WinAvx2X8WShift8b
import Hashtree.Proofs.WinAvx2X8WShift8c
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.WinAvx2X8W

/-- Residue 8: the cut facts, assembled from the per-conjunct kernel checks. -/
theorem shiftOk_8 : shiftOk 8 = true := by
  unfold shiftOk
  simp only [shiftOk_8_c1, shiftOk_8_c2, shiftOk_8_c3, shiftOk_8_c4, shiftOk_8_c5, shiftOk_8_c6, shiftOk_8_c7, shiftOk_8_c8, shiftOk_8_c9, shiftOk_8_c10, shiftOk_8_c11, shiftOk_8_c12, shiftOk_8_c13, shiftOk_8_c14, Bool.and_true]

end Hashtree.Proofs.WinAvx2X8W
