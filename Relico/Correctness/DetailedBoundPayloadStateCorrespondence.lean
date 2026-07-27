import Relico.Correctness.BoundPayloadState
import Relico.DTR.DetailedBoundPayloadSemantics
import Relico.LF.DetailedBoundPayloadSemantics
import Relico.Translation.BoundPayloadBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Payload-preserving correspondence data for one selected detailed dispatch.

The server and generated reaction are fixed by the surrounding detailed state
indices. The witness retains stable-state correspondence before and after
dispatch and exact payload-aware correspondence of the selected occurrence.
-/
structure DetailedBoundPayloadDispatchWitnessCorresponds
    (server : DTR.PayloadMessageServer)
    (sourceBefore : DTR.BoundPayloadState)
    (selectedMessage : DTR.PendingMessage)
    (sourceAfter : DTR.BoundPayloadState)
    (targetBefore : LF.BoundPayloadState)
    (selectedAction : LF.PendingAction)
    (targetAfter : LF.BoundPayloadState) :
    Prop where

  beforeState :
    BoundPayloadStateCorresponds
      sourceBefore
      targetBefore

  selectedOccurrence :
    PendingPayloadCorresponds
      selectedMessage
      selectedAction

  afterState :
    BoundPayloadStateCorresponds
      sourceAfter
      targetAfter

/--
Phase-aware correspondence between detailed parameter-aware source and
generated-LF states.

The relation retains exact payload queue correspondence and equality of
activation-local parameter stores through `BoundPayloadStateCorresponds`.
-/
inductive DetailedBoundPayloadStateCorresponds
    (server : DTR.PayloadMessageServer) :
    DTR.DetailedBoundPayloadState
        server →
    LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server) →
    Prop where

  | stable
      {sourceState : DTR.BoundPayloadState}
      {targetState : LF.BoundPayloadState}
      (hStable :
        BoundPayloadStateCorresponds
          sourceState
          targetState) :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceState)
        (.stable targetState)

  | futureAfterTime
      {sourceBefore sourceAfter :
        DTR.BoundPayloadState}
      {selectedMessage :
        DTR.PendingMessage}
      {sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter}
      {targetBefore targetAfter :
        LF.BoundPayloadState}
      {selectedAction :
        LF.PendingAction}
      {targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter}
      (hSourceFuture :
        sourceBefore.currentTime <
          sourceAfter.currentTime)
      (hTargetFuture :
        targetBefore.currentTag.time <
          targetAfter.currentTag.time)
      (hWitness :
        DetailedBoundPayloadDispatchWitnessCorresponds
          server
          sourceBefore
          selectedMessage
          sourceAfter
          targetBefore
          selectedAction
          targetAfter) :
      DetailedBoundPayloadStateCorresponds
        server
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)

  | futureReady
      {sourceBefore sourceAfter :
        DTR.BoundPayloadState}
      {selectedMessage :
        DTR.PendingMessage}
      {sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter}
      {targetBefore targetAfter :
        LF.BoundPayloadState}
      {selectedAction :
        LF.PendingAction}
      {targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter}
      (hSourceFuture :
        sourceBefore.currentTime <
          sourceAfter.currentTime)
      (hTargetFuture :
        targetBefore.currentTag.time <
          targetAfter.currentTag.time)
      (hPositiveMicrostep :
        0 <
          targetAfter.currentTag.microstep)
      (hWitness :
        DetailedBoundPayloadDispatchWitnessCorresponds
          server
          sourceBefore
          selectedMessage
          sourceAfter
          targetBefore
          selectedAction
          targetAfter) :
      DetailedBoundPayloadStateCorresponds
        server
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          sourceDispatch)
        (.dispatchReady
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)

  | sameTimeMicrostepAhead
      {sourceBefore sourceAfter :
        DTR.BoundPayloadState}
      {selectedMessage :
        DTR.PendingMessage}
      (sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter)
      {targetBefore targetAfter :
        LF.BoundPayloadState}
      {selectedAction :
        LF.PendingAction}
      {targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter}
      (hSourceSameTime :
        sourceBefore.currentTime =
          sourceAfter.currentTime)
      (hTargetSameTime :
        targetBefore.currentTag.time =
          targetAfter.currentTag.time)
      (hTargetLaterMicrostep :
        targetBefore.currentTag.microstep <
          targetAfter.currentTag.microstep)
      (hWitness :
        DetailedBoundPayloadDispatchWitnessCorresponds
          server
          sourceBefore
          selectedMessage
          sourceAfter
          targetBefore
          selectedAction
          targetAfter) :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.dispatchReady
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)

namespace DetailedBoundPayloadStateCorresponds

/--
Stable detailed-state correspondence is exactly bound-payload runtime-state
correspondence.
-/
theorem stable_iff
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState} :
    DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceState)
          (.stable targetState) ↔
      BoundPayloadStateCorresponds
        sourceState
        targetState := by

  constructor

  · intro hCorresponds

    cases hCorresponds with
    | stable hStable =>
        exact hStable

  · intro hStable

    exact
      DetailedBoundPayloadStateCorresponds.stable
        hStable

/--
Stable detailed-state correspondence preserves equality of the
activation-local parameter environments.
-/
theorem stable_parameters
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState}
    (hCorresponds :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceState)
        (.stable targetState)) :
    targetState.parameters =
      sourceState.parameters := by

  exact
    (stable_iff.mp hCorresponds).parameters

/--
Stable detailed-state correspondence preserves complete ordered
payload-aware queue correspondence.
-/
theorem stable_pendingEvents
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState}
    (hCorresponds :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceState)
        (.stable targetState)) :
    PayloadQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions := by

  exact
    (stable_iff.mp hCorresponds).pendingEvents

end DetailedBoundPayloadStateCorresponds


end Correctness
end Relico
