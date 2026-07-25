import Relico.Correctness.Correspondence
import Relico.DTR.PriorityTimingWellFormed
import Relico.LF.PriorityTimingInvariant

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
When two corresponding source messages have the same logical arrival
time and both generated actions have microstep zero, the generated
actions have the same complete LF tag.

This is the bridge needed to transport source same-time priority order
to target same-tag reaction order.
-/
theorem PendingCorresponds.targetTag_eq_of_sameTime_and_zero
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hLeft :
      PendingCorresponds
        sourceLeft
        targetLeft)
    (hRight :
      PendingCorresponds
        sourceRight
        targetRight)
    (hSameTime :
      sourceLeft.arrivalTime =
        sourceRight.arrivalTime)
    (hLeftZero :
      targetLeft.tag.microstep = 0)
    (hRightZero :
      targetRight.tag.microstep = 0) :
    targetLeft.tag =
      targetRight.tag := by

  have hTime :
      targetLeft.tag.time =
        targetRight.tag.time :=

    hLeft.logicalTime.trans
      (hSameTime.trans
        hRight.logicalTime.symm)

  have hMicrostep :
      targetLeft.tag.microstep =
        targetRight.tag.microstep :=

    hLeftZero.trans
      hRightZero.symm

  cases hLeftTag : targetLeft.tag with

  | mk leftTime leftMicrostep =>
      cases hRightTag : targetRight.tag with

      | mk rightTime rightMicrostep =>
          have hTimeFields :
              leftTime =
                rightTime := by

            simpa [
              hLeftTag,
              hRightTag
            ] using
              hTime

          have hMicrostepFields :
              leftMicrostep =
                rightMicrostep := by

            simpa [
              hLeftTag,
              hRightTag
            ] using
              hMicrostep

          cases hTimeFields
          cases hMicrostepFields
          rfl

/--
The zero-microstep queue invariant supplies the microstep premise for
any member of the target queue.
-/
theorem PendingCorresponds.target_microstep_zero
    {sourceMessage :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    {targetQueue :
      LF.ActionQueue}
    (_hCorresponds :
      PendingCorresponds
        sourceMessage
        targetAction)
    (hMember :
      targetAction ∈ targetQueue)
    (hQueue :
      LF.ActionQueue.AllMicrostepsZero
        targetQueue) :
    targetAction.tag.microstep = 0 := by

  exact
    hQueue
      targetAction
      hMember

end Correctness
end Relico
