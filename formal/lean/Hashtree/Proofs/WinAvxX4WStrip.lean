import Hashtree.Proofs.WinAvxX4WStripDefs
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-! The windows avx_x4 stripped-cut facts: one kernel evaluation of `stripOk`
(`WinAvxX4WStripDefs`). -/

namespace Hashtree.Proofs.WinAvxX4WStrip

theorem stripOk_true : stripOk = true := by decide +kernel

end Hashtree.Proofs.WinAvxX4WStrip
