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

namespace Relico
namespace Correctness

/--
Ordered payload-aware correspondence between complete pending queues.
-/
inductive PayloadQueueCorresponds :
    DTR.MessageBag →
    LF.ActionQueue →
    Prop where

  | nil :
      PayloadQueueCorresponds
        []
        []

  | cons
      {sourceMessage : DTR.PendingMessage}
      {targetAction : LF.PendingAction}
      {sourceQueue : DTR.MessageBag}
      {targetQueue : LF.ActionQueue}
      (head :
        PendingPayloadCorresponds
          sourceMessage
          targetAction)
      (tail :
        PayloadQueueCorresponds
          sourceQueue
          targetQueue) :
      PayloadQueueCorresponds
        (sourceMessage :: sourceQueue)
        (targetAction :: targetQueue)

theorem payloadQueueCorresponds_nil :
    PayloadQueueCorresponds
      []
      [] := by

  exact
    PayloadQueueCorresponds.nil

theorem payloadQueueCorresponds_singleton
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hPending :
      PendingPayloadCorresponds
        sourceMessage
        targetAction) :
    PayloadQueueCorresponds
      [sourceMessage]
      [targetAction] := by

  exact
    PayloadQueueCorresponds.cons
      hPending
      PayloadQueueCorresponds.nil

/--
The canonical source and target scheduling constructors preserve the
message name, logical time, and complete ordered payload.
-/
theorem pendingPayloadCorresponds_scheduleWithPayload
    (currentTime : LogicalTime)
    (currentTag : LF.Tag)
    (messageName : MsgName)
    (payload : Payload)
    (delay : Delay)
    (hCurrentTime :
      currentTag.time =
        currentTime) :
    PendingPayloadCorresponds
      (DTR.PendingMessage.scheduleWithPayload
        currentTime
        messageName
        payload
        delay)
      (LF.PendingAction.scheduleWithPayload
        currentTag
        (Translation.actionNameFor
          messageName)
        payload
        delay) := by

  simpa [
    DTR.PendingMessage.scheduleWithPayload,
    LF.PendingAction.scheduleWithPayload
  ] using
    pendingPayloadCorresponds_scheduled
      currentTime
      currentTag
      messageName
      payload
      delay
      hCurrentTime

/--
Appending one newly scheduled payload-bearing source occurrence and its
generated LF action preserves queue correspondence.
-/
theorem payloadQueueCorresponds_append_scheduleWithPayload
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueue :
      PayloadQueueCorresponds
        sourceQueue
        targetQueue)
    (currentTime : LogicalTime)
    (currentTag : LF.Tag)
    (messageName : MsgName)
    (payload : Payload)
    (delay : Delay)
    (hCurrentTime :
      currentTag.time =
        currentTime) :
    PayloadQueueCorresponds
      (sourceQueue ++ [
        DTR.PendingMessage.scheduleWithPayload
          currentTime
          messageName
          payload
          delay
      ])
      (targetQueue ++ [
        LF.PendingAction.scheduleWithPayload
          currentTag
          (Translation.actionNameFor
            messageName)
          payload
          delay
      ]) := by

  induction hQueue with

  | nil =>
      exact
        PayloadQueueCorresponds.cons
          (pendingPayloadCorresponds_scheduleWithPayload
            currentTime
            currentTag
            messageName
            payload
            delay
            hCurrentTime)
          PayloadQueueCorresponds.nil

  | cons hPending hRemaining ih =>
      exact
        PayloadQueueCorresponds.cons
          hPending
          ih

end Correctness
end Relico
