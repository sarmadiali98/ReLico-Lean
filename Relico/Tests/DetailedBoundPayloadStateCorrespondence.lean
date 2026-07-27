import Relico.Correctness.DetailedBoundPayloadStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadStateCorrespondence

theorem stable_interface
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState}
    (hStates :
      Correctness.BoundPayloadStateCorresponds
        sourceState
        targetState) :
    Correctness.DetailedBoundPayloadStateCorresponds
      server
      (.stable sourceState)
      (.stable targetState) := by

  exact
    Correctness.DetailedBoundPayloadStateCorresponds.stable
      hStates

theorem stable_iff_interface
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState} :
    Correctness.DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceState)
          (.stable targetState) ↔
      Correctness.BoundPayloadStateCorresponds
        sourceState
        targetState := by

  exact
    Correctness.DetailedBoundPayloadStateCorresponds.stable_iff

theorem stable_parameters_interface
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState}
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceState)
        (.stable targetState)) :
    targetState.parameters =
      sourceState.parameters := by

  exact
    Correctness.DetailedBoundPayloadStateCorresponds.stable_parameters
      hStates

theorem stable_payload_queue_interface
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState}
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceState)
        (.stable targetState)) :
    Correctness.PayloadQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions := by

  exact
    Correctness.DetailedBoundPayloadStateCorresponds.stable_pendingEvents
      hStates

theorem future_after_time_interface
    {server : DTR.PayloadMessageServer}
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
      Correctness.DetailedBoundPayloadDispatchWitnessCorresponds
        server
        sourceBefore
        selectedMessage
        sourceAfter
        targetBefore
        selectedAction
        targetAfter) :
    Correctness.DetailedBoundPayloadStateCorresponds
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
        targetDispatch) := by

  exact
    Correctness.DetailedBoundPayloadStateCorresponds.futureAfterTime
      hSourceFuture
      hTargetFuture
      hWitness

theorem future_ready_interface
    {server : DTR.PayloadMessageServer}
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
      Correctness.DetailedBoundPayloadDispatchWitnessCorresponds
        server
        sourceBefore
        selectedMessage
        sourceAfter
        targetBefore
        selectedAction
        targetAfter) :
    Correctness.DetailedBoundPayloadStateCorresponds
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
        targetDispatch) := by

  exact
    Correctness.DetailedBoundPayloadStateCorresponds.futureReady
      hSourceFuture
      hTargetFuture
      hPositiveMicrostep
      hWitness

theorem same_time_microstep_interface
    {server : DTR.PayloadMessageServer}
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
      Correctness.DetailedBoundPayloadDispatchWitnessCorresponds
        server
        sourceBefore
        selectedMessage
        sourceAfter
        targetBefore
        selectedAction
        targetAfter) :
    Correctness.DetailedBoundPayloadStateCorresponds
      server
      (.stable sourceBefore)
      (.dispatchReady
        targetBefore
        selectedAction
        targetAfter
        targetDispatch) := by

  exact
    Correctness.DetailedBoundPayloadStateCorresponds.sameTimeMicrostepAhead
      sourceDispatch
      hSourceSameTime
      hTargetSameTime
      hTargetLaterMicrostep
      hWitness

end DetailedBoundPayloadStateCorrespondence
end Tests
end Relico
