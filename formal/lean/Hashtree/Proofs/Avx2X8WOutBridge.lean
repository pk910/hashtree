import Hashtree.Proofs.Avx2X8WOut
import Hashtree.Proofs.WinAvx2X8Bridge

/-!
# R2c — `TurnOut8` / `TurnOut8Last` in R5's names

`Avx2X8WOut.TurnOut8` / `TurnOut8Last` are R5's `WinAvx2X8Bridge` text copied verbatim, with
`Avx512X16WOut.OutOk` for `WinWrapper.OutOk` (same text); unfolding both gives R5's statements.
-/

namespace Hashtree.Proofs.Avx2X8WOut

theorem turnOut8_R5 : Hashtree.Proofs.WinAvx2X8Bridge.TurnOut8 := by
  unfold Hashtree.Proofs.WinAvx2X8Bridge.TurnOut8 Hashtree.Proofs.WinWrapper.OutOk
  exact turnOut8

theorem turnOut8Last_R5 : Hashtree.Proofs.WinAvx2X8Bridge.TurnOut8Last := by
  unfold Hashtree.Proofs.WinAvx2X8Bridge.TurnOut8Last Hashtree.Proofs.WinWrapper.OutOk
  exact turnOut8Last

end Hashtree.Proofs.Avx2X8WOut
