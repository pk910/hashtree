import Hashtree.Proofs.WinAvx2X8WStrip24a
import Hashtree.Proofs.WinAvx2X8WStrip24b
import Hashtree.Proofs.WinAvx2X8WStrip24c
import Hashtree.Proofs.WinAvx2X8WStrip24d
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Hashtree.Proofs.WinAvx2X8WStrip

/-- Residue 24: the cut facts, assembled from the per-conjunct kernel checks. -/
theorem stripOk_24 : stripOk 24 = true := by
  unfold stripOk
  simp only [stripOk_24_c1, stripOk_24_c2, stripOk_24_c3, stripOk_24_c4, stripOk_24_c5, stripOk_24_c6, stripOk_24_c7, stripOk_24_c8, stripOk_24_c9, stripOk_24_c10, stripOk_24_c11, stripOk_24_c12, stripOk_24_c13, stripOk_24_c14, stripOk_24_c15, stripOk_24_c16, stripOk_24_c17, stripOk_24_c18, stripOk_24_c19, stripOk_24_c20, stripOk_24_c21, Bool.and_true]

end Hashtree.Proofs.WinAvx2X8WStrip
