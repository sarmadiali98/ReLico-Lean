import Relico.Correctness.DetailedBoundPayloadBackwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadBackwardWeakSimulation

theorem statement_backward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {targetLabel : LF.BoundPayloadLabel}
    (hTargetStep :
      LF.BoundPayloadStep
        (Translation.compilePayloadMessageServer
          server).logicalAction
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    Correctness.DetailedBoundPayloadBackwardMatch
      server
      .tau
      (.stable targetAfter)
      (.stable sourceBefore) := by

  exact
    Correctness.detailedBoundPayload_statement_backward_weak
      hTargetStep
      hStates

theorem timeAdvance_backward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hTargetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter)
    (hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    Correctness.DetailedBoundPayloadBackwardMatch
      server
      (.timeAdvance
        targetBefore.currentTag.time
        targetAfter.currentTag.time)
      (.afterTime
        targetBefore
        selectedAction
        targetAfter
        hTargetDispatch)
      (.stable sourceBefore) := by

  exact
    Correctness.detailedBoundPayload_timeAdvance_backward_weak
      hTargetDispatch
      hTargetFuture
      hStates

theorem microstepAfterTime_backward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hPositiveMicrostep :
      0 <
        targetAfter.currentTag.microstep)
    (hStates :
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
          targetDispatch)) :
    Correctness.DetailedBoundPayloadBackwardMatch
      server
      (.microstepAdvance
        {
          time :=
            targetAfter.currentTag.time

          microstep :=
            0
        }
        targetAfter.currentTag)
      (.dispatchReady
        targetBefore
        selectedAction
        targetAfter
        targetDispatch)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        sourceDispatch) := by

  exact
    Correctness.detailedBoundPayload_microstepAfterTime_backward_weak
      hPositiveMicrostep
      hStates

theorem microstepSameTime_backward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hTargetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter)
    (hTargetSameTime :
      targetBefore.currentTag.time =
        targetAfter.currentTag.time)
    (hLaterMicrostep :
      targetBefore.currentTag.microstep <
        targetAfter.currentTag.microstep)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    Correctness.DetailedBoundPayloadBackwardMatch
      server
      (.microstepAdvance
        targetBefore.currentTag
        targetAfter.currentTag)
      (.dispatchReady
        targetBefore
        selectedAction
        targetAfter
        hTargetDispatch)
      (.stable sourceBefore) := by

  exact
    Correctness.detailedBoundPayload_microstepSameTime_backward_weak
      hTargetDispatch
      hTargetSameTime
      hLaterMicrostep
      hStates

theorem consumeAfterTimeZero_backward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hZeroMicrostep :
      targetAfter.currentTag.microstep =
        0)
    (hStates :
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
          targetDispatch)) :
    Correctness.DetailedBoundPayloadBackwardMatch
      server
      (.consume selectedAction)
      (.stable targetAfter)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        sourceDispatch) := by

  exact
    Correctness.detailedBoundPayload_consumeAfterTimeZero_backward_weak
      hZeroMicrostep
      hStates

theorem consumeReadyFuture_backward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hStates :
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
          targetDispatch)) :
    Correctness.DetailedBoundPayloadBackwardMatch
      server
      (.consume selectedAction)
      (.stable targetAfter)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        sourceDispatch) := by

  exact
    Correctness.detailedBoundPayload_consumeReadyFuture_backward_weak
      hStates

theorem consumeReadySameTime_backward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.dispatchReady
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)) :
    Correctness.DetailedBoundPayloadBackwardMatch
      server
      (.consume selectedAction)
      (.stable targetAfter)
      (.stable sourceBefore) := by

  exact
    Correctness.detailedBoundPayload_consumeReadySameTime_backward_weak
      hStates

theorem consumeNow_backward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hTargetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter)
    (hTargetSameTag :
      targetBefore.currentTag =
        targetAfter.currentTag)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    Correctness.DetailedBoundPayloadBackwardMatch
      server
      (.consume selectedAction)
      (.stable targetAfter)
      (.stable sourceBefore) := by

  exact
    Correctness.detailedBoundPayload_consumeNow_backward_weak
      hTargetDispatch
      hTargetSameTag
      hStates

theorem source_corresponds_interface
    {server : DTR.PayloadMessageServer}
    {targetLabel :
      LF.DetailedBoundPayloadLabel}
    {targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    {sourceBefore :
      DTR.DetailedBoundPayloadState server}
    (hMatch :
      Correctness.DetailedBoundPayloadBackwardMatch
        server
        targetLabel
        targetAfter
        sourceBefore) :
    ∃ sourceAfter :
        DTR.DetailedBoundPayloadState server,
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        sourceAfter
        targetAfter := by

  exact
    Correctness.DetailedBoundPayloadBackwardMatch.source_corresponds
      hMatch

end DetailedBoundPayloadBackwardWeakSimulation
end Tests
end Relico
