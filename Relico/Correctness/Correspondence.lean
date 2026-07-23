import Relico.DTR.Semantics
import Relico.LF.Semantics
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
A pending DTR message corresponds to a pending LF action when:

- the generated action name comes from the source message name;
- both occurrences have the same logical arrival time.

The LF microstep is intentionally not required to equal a source
component because vertical-slice DTR state has no microstep.
-/
structure PendingCorresponds
    (sourceMessage : DTR.PendingMessage)
    (targetAction : LF.PendingAction) :
    Prop where

  actionName :
    targetAction.name =
      Translation.actionNameFor sourceMessage.name

  logicalTime :
    targetAction.tag.time =
      sourceMessage.arrivalTime

/--
Occurrence-preserving correspondence between the DTR message bag and
the generated LF action queue.

The relation is list based so duplicate messages and duplicate actions
remain distinct occurrences.
-/
inductive QueueCorresponds :
    DTR.MessageBag →
    LF.ActionQueue →
    Prop where

  | nil :
      QueueCorresponds [] []

  | cons
      {sourceMessage : DTR.PendingMessage}
      {targetAction : LF.PendingAction}
      {sourceRemaining : DTR.MessageBag}
      {targetRemaining : LF.ActionQueue}
      (headCorresponds :
        PendingCorresponds
          sourceMessage
          targetAction)
      (tailCorresponds :
        QueueCorresponds
          sourceRemaining
          targetRemaining) :
      QueueCorresponds
        (sourceMessage :: sourceRemaining)
        (targetAction :: targetRemaining)

/--
Appending one corresponding occurrence preserves queue correspondence.
-/
theorem QueueCorresponds.append_one
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      QueueCorresponds sourceQueue targetQueue)
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hPending :
      PendingCorresponds
        sourceMessage
        targetAction) :
    QueueCorresponds
      (sourceQueue ++ [sourceMessage])
      (targetQueue ++ [targetAction]) := by
  induction hQueues with
  | nil =>
      exact
        QueueCorresponds.cons
          hPending
          QueueCorresponds.nil

  | cons headCorresponds tailCorresponds inductionHypothesis =>
      exact
        QueueCorresponds.cons
          headCorresponds
          inductionHypothesis

/--
A newly scheduled LF logical action corresponds to the DTR message
created by the same self-send.
-/
theorem pendingCorresponds_scheduled
    (currentTime : LogicalTime)
    (currentTag : LF.Tag)
    (messageName : MsgName)
    (delay : Delay)
    (hCurrentTime :
      currentTag.time = currentTime) :
    PendingCorresponds
      {
        name := messageName
        arrivalTime :=
          LogicalTime.after currentTime delay
      }
      {
        name :=
          Translation.actionNameFor messageName
        tag :=
          LF.Tag.schedule currentTag delay
      } := by
  refine {
    actionName := rfl
    logicalTime := ?_
  }

  calc
    (LF.Tag.schedule currentTag delay).time
        =
      LogicalTime.after currentTag.time delay := by
        exact LF.Tag.schedule_time currentTag delay

    _ =
      LogicalTime.after currentTime delay := by
        rw [hCurrentTime]

/--
Correspondence between source and target transition labels.

Internal computation remains internal. A source send corresponds to
scheduling the generated LF action at the same logical time.
-/
inductive LabelCorresponds :
    DTR.Label →
    LF.Label →
    Prop where

  | internal :
      LabelCorresponds
        DTR.Label.internal
        LF.Label.internal

  | send
      (messageName : MsgName)
      (arrivalTime : LogicalTime)
      (targetTag : LF.Tag)
      (hLogicalTime :
        targetTag.time = arrivalTime) :
      LabelCorresponds
        (DTR.Label.send
          messageName
          arrivalTime)
        (LF.Label.schedule
          (Translation.actionNameFor messageName)
          targetTag)

/--
Runtime correspondence for vertical slice v0.

The relation preserves logical time, integer state, pending event
occurrences, and the executable body produced by `compileBody`.
-/
structure StateCorresponds
    (sourceState : DTR.State)
    (targetState : LF.State) :
    Prop where

  currentTime :
    targetState.currentTag.time =
      sourceState.currentTime

  stateValue :
    targetState.stateValue =
      sourceState.stateValue

  pendingEvents :
    QueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions

  activeBody :
    targetState.activeBody =
      Translation.compileBody
        sourceState.activeBody

end Correctness
end Relico
