import Hashtree.Proofs.AvxX4LoopWOutLast
import Hashtree.Proofs.Avx2X8OutLink

/-!
# R2c — `TurnOut4Last` as R2 states it

`Avx2X8OutLink.TurnOut4Last` (research/formal-r2-amd64 2da19f1) from
`AvxX4LoopWOutLast.turnOut4Last`: the same text, R2's `OutOk` being `ShaniW.OutOk` and its step
count `Avx2X8X4WAgree.x4LastSteps` (both unfolded; the definitions are the same).
-/

namespace Hashtree.Proofs.AvxX4LoopWOutLast

theorem turnOut4Last_R2 : Hashtree.Proofs.Avx2X8OutLink.TurnOut4Last := by
  unfold Hashtree.Proofs.Avx2X8OutLink.TurnOut4Last Hashtree.Proofs.ShaniW.OutOk
    Hashtree.Proofs.Avx2X8X4WAgree.x4LastSteps
  have h := turnOut4Last
  unfold TurnOut4Last Hashtree.Proofs.Avx512X16WOut.OutOk x4LastSteps at h
  exact h

end Hashtree.Proofs.AvxX4LoopWOutLast
