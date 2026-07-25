import Relico.Correctness.Correspondence

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
A payload-aware strengthening of pending-occurrence correspondence.

`PendingCorresponds` continues to capture generated action naming and logical
arrival time. This relation additionally requires exact ordered payload
equality.
-/
structure PendingPayloadCorresponds
    (sourceMessage : DTR.PendingMessage)
    (targetAction : LF.PendingAction) :
    Prop where

  occurrence :
    PendingCorresponds
      sourceMessage
      targetAction

  payload :
    targetAction.payload =
      sourceMessage.payload

/--
Scheduling the generated LF action with the same payload as the source
message establishes payload-aware pending-occurrence correspondence.
-/
theorem pendingPayloadCorresponds_scheduled
    (currentTime : LogicalTime)
    (currentTag : LF.Tag)
    (messageName : MsgName)
    (payload : Payload)
    (delay : Delay)
    (hCurrentTime :
      currentTag.time =
        currentTime) :
    PendingPayloadCorresponds
      {
        name :=
          messageName

        arrivalTime :=
          LogicalTime.after
            currentTime
            delay

        payload :=
          payload
      }
      {
        name :=
          Translation.actionNameFor
            messageName

        tag :=
          LF.Tag.schedule
            currentTag
            delay

        payload :=
          payload
      } := by

  refine {
    occurrence := ?_
    payload := rfl
  }

  refine {
    actionName := rfl
    logicalTime := ?_
  }

  calc
    (LF.Tag.schedule
      currentTag
      delay).time =
        LogicalTime.after
          currentTag.time
          delay := by
            exact
              LF.Tag.schedule_time
                currentTag
                delay

    _ =
        LogicalTime.after
          currentTime
          delay := by
            rw [
              hCurrentTime
            ]

/--
The existing empty-payload fragment is a direct special case.
-/
theorem pendingPayloadCorresponds_scheduled_empty
    (currentTime : LogicalTime)
    (currentTag : LF.Tag)
    (messageName : MsgName)
    (delay : Delay)
    (hCurrentTime :
      currentTag.time =
        currentTime) :
    PendingPayloadCorresponds
      {
        name :=
          messageName

        arrivalTime :=
          LogicalTime.after
            currentTime
            delay
      }
      {
        name :=
          Translation.actionNameFor
            messageName

        tag :=
          LF.Tag.schedule
            currentTag
            delay
      } := by

  exact
    pendingPayloadCorresponds_scheduled
      currentTime
      currentTag
      messageName
      []
      delay
      hCurrentTime

end Correctness
end Relico
