import Hashtree.Proofs.WinAvx2X8WStrip8a
import Hashtree.Proofs.WinAvx2X8WStrip8b
import Hashtree.Proofs.WinAvx2X8WStrip8c
import Hashtree.Proofs.WinAvx2X8WStrip8d
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.WinAvx2X8WStrip

/-- Residue 8: the cut facts, assembled from the per-conjunct kernel checks. -/
theorem stripOk_8 : stripOk 8 = true := by
  unfold stripOk
  simp only [stripOk_8_c1, stripOk_8_c2, stripOk_8_c3, stripOk_8_c4, stripOk_8_c5, stripOk_8_c6, stripOk_8_c7, stripOk_8_c8, stripOk_8_c9, stripOk_8_c10, stripOk_8_c11, stripOk_8_c12, stripOk_8_c13, stripOk_8_c14, stripOk_8_c15, stripOk_8_c16, stripOk_8_c17, stripOk_8_c18, stripOk_8_c19, stripOk_8_c20, stripOk_8_c21, Bool.and_true]

end Hashtree.Proofs.WinAvx2X8WStrip
