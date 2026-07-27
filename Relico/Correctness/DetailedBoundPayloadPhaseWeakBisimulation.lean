import Relico.Correctness.DetailedBoundPayloadBackwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Complete phase-indexed weak-simulation interface for one payload message server
and its generated LF payload reaction.

The structure packages all five forward and eight backward detailed phase
obligations. Each field retains the exact premises of its underlying
single-transition theorem.
-/
structure DetailedBoundPayloadPhaseWeakBisimulation
    (server : DTR.PayloadMessageServer) :
    Prop where

  forwardStatementMatch :
    ∀ (sourceBefore sourceAfter :
        DTR.BoundPayloadState)
      (sourceLabel : DTR.BoundPayloadLabel)
      (targetBefore : LF.BoundPayloadState),
      DTR.BoundPayloadStep
          server.name
          sourceBefore
          sourceLabel
          sourceAfter →
        DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceBefore)
          (.stable targetBefore) →
        DetailedBoundPayloadForwardMatch
          server
          .tau
          (.stable sourceAfter)
          (.stable targetBefore)

  forwardTimeAdvanceMatch :
    ∀ (sourceBefore sourceAfter :
        DTR.BoundPayloadState)
      (selectedMessage : DTR.PendingMessage)
      (targetBefore : LF.BoundPayloadState)
      (sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter),
      sourceBefore.currentTime <
          sourceAfter.currentTime →
        DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceBefore)
          (.stable targetBefore) →
        BoundPayloadForwardDispatchCompatible
          selectedMessage
          sourceAfter.pendingMessages
          targetBefore →
        DetailedBoundPayloadForwardMatch
          server
          (.timeAdvance
            sourceBefore.currentTime
            sourceAfter.currentTime)
          (.dispatchReady
            sourceBefore
            selectedMessage
            sourceAfter
            sourceDispatch)
          (.stable targetBefore)

  forwardConsumeAfterTimeMatch :
    ∀ (sourceBefore sourceAfter :
        DTR.BoundPayloadState)
      (selectedMessage : DTR.PendingMessage)
      (sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter),
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
            targetDispatch) →
        DetailedBoundPayloadForwardMatch
          server
          (.consume selectedMessage)
          (.stable sourceAfter)
          (.afterTime
            targetBefore
            selectedAction
            targetAfter
            targetDispatch)

  forwardConsumeReadyMatch :
    ∀ (sourceBefore sourceAfter :
        DTR.BoundPayloadState)
      (selectedMessage : DTR.PendingMessage)
      (sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter),
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
            targetDispatch) →
        DetailedBoundPayloadForwardMatch
          server
          (.consume selectedMessage)
          (.stable sourceAfter)
          (.dispatchReady
            targetBefore
            selectedAction
            targetAfter
            targetDispatch)

  forwardConsumeNowMatch :
    ∀ (sourceBefore sourceAfter :
        DTR.BoundPayloadState)
      (selectedMessage : DTR.PendingMessage)
      (targetBefore : LF.BoundPayloadState)
      (_sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter),
      sourceBefore.currentTime =
          sourceAfter.currentTime →
        DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceBefore)
          (.stable targetBefore) →
        BoundPayloadForwardDispatchCompatible
          selectedMessage
          sourceAfter.pendingMessages
          targetBefore →
        DetailedBoundPayloadForwardMatch
          server
          (.consume selectedMessage)
          (.stable sourceAfter)
          (.stable targetBefore)

  backwardStatementMatch :
    ∀ (sourceBefore : DTR.BoundPayloadState)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (targetLabel : LF.BoundPayloadLabel),
      LF.BoundPayloadStep
          (Translation.compilePayloadMessageServer
            server).logicalAction
          targetBefore
          targetLabel
          targetAfter →
        DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceBefore)
          (.stable targetBefore) →
        DetailedBoundPayloadBackwardMatch
          server
          .tau
          (.stable targetAfter)
          (.stable sourceBefore)

  backwardTimeAdvanceMatch :
    ∀ (sourceBefore : DTR.BoundPayloadState)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter),
      targetBefore.currentTag.time <
          targetAfter.currentTag.time →
        DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceBefore)
          (.stable targetBefore) →
        DetailedBoundPayloadBackwardMatch
          server
          (.timeAdvance
            targetBefore.currentTag.time
            targetAfter.currentTag.time)
          (.afterTime
            targetBefore
            selectedAction
            targetAfter
            targetDispatch)
          (.stable sourceBefore)

  backwardMicrostepAfterTimeMatch :
    ∀ (sourceBefore sourceAfter :
        DTR.BoundPayloadState)
      (selectedMessage : DTR.PendingMessage)
      (sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter),
      0 <
          targetAfter.currentTag.microstep →
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
            targetDispatch) →
        DetailedBoundPayloadBackwardMatch
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
            sourceDispatch)

  backwardMicrostepSameTimeMatch :
    ∀ (sourceBefore : DTR.BoundPayloadState)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter),
      targetBefore.currentTag.time =
          targetAfter.currentTag.time →
        targetBefore.currentTag.microstep <
            targetAfter.currentTag.microstep →
        DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceBefore)
          (.stable targetBefore) →
        DetailedBoundPayloadBackwardMatch
          server
          (.microstepAdvance
            targetBefore.currentTag
            targetAfter.currentTag)
          (.dispatchReady
            targetBefore
            selectedAction
            targetAfter
            targetDispatch)
          (.stable sourceBefore)

  backwardConsumeAfterTimeZeroMatch :
    ∀ (sourceBefore sourceAfter :
        DTR.BoundPayloadState)
      (selectedMessage : DTR.PendingMessage)
      (sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter),
      targetAfter.currentTag.microstep =
          0 →
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
            targetDispatch) →
        DetailedBoundPayloadBackwardMatch
          server
          (.consume selectedAction)
          (.stable targetAfter)
          (.dispatchReady
            sourceBefore
            selectedMessage
            sourceAfter
            sourceDispatch)

  backwardConsumeReadyFutureMatch :
    ∀ (sourceBefore sourceAfter :
        DTR.BoundPayloadState)
      (selectedMessage : DTR.PendingMessage)
      (sourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter),
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
            targetDispatch) →
        DetailedBoundPayloadBackwardMatch
          server
          (.consume selectedAction)
          (.stable targetAfter)
          (.dispatchReady
            sourceBefore
            selectedMessage
            sourceAfter
            sourceDispatch)

  backwardConsumeReadySameTimeMatch :
    ∀ (sourceBefore : DTR.BoundPayloadState)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter),
      DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceBefore)
          (.dispatchReady
            targetBefore
            selectedAction
            targetAfter
            targetDispatch) →
        DetailedBoundPayloadBackwardMatch
          server
          (.consume selectedAction)
          (.stable targetAfter)
          (.stable sourceBefore)

  backwardConsumeNowMatch :
    ∀ (sourceBefore : DTR.BoundPayloadState)
      (targetBefore targetAfter :
        LF.BoundPayloadState)
      (selectedAction : LF.PendingAction)
      (_targetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter),
      targetBefore.currentTag =
          targetAfter.currentTag →
        DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceBefore)
          (.stable targetBefore) →
        DetailedBoundPayloadBackwardMatch
          server
          (.consume selectedAction)
          (.stable targetAfter)
          (.stable sourceBefore)

/--
The detailed bound-payload semantics satisfies every phase-indexed forward and
backward weak-simulation obligation.
-/
theorem detailedBoundPayload_phaseWeakBisimulation
    (server : DTR.PayloadMessageServer) :
    DetailedBoundPayloadPhaseWeakBisimulation
      server := by

  refine {
    forwardStatementMatch := ?_
    forwardTimeAdvanceMatch := ?_
    forwardConsumeAfterTimeMatch := ?_
    forwardConsumeReadyMatch := ?_
    forwardConsumeNowMatch := ?_
    backwardStatementMatch := ?_
    backwardTimeAdvanceMatch := ?_
    backwardMicrostepAfterTimeMatch := ?_
    backwardMicrostepSameTimeMatch := ?_
    backwardConsumeAfterTimeZeroMatch := ?_
    backwardConsumeReadyFutureMatch := ?_
    backwardConsumeReadySameTimeMatch := ?_
    backwardConsumeNowMatch := ?_
  }

  · intro sourceBefore sourceAfter sourceLabel targetBefore
      hSourceStep hStates

    exact
      detailedBoundPayload_statement_forward_weak
        hSourceStep
        hStates

  · intro sourceBefore sourceAfter selectedMessage targetBefore
      sourceDispatch hFuture hStates hCompatible

    exact
      detailedBoundPayload_timeAdvance_forward_weak
        sourceDispatch
        hFuture
        hStates
        hCompatible

  · intro sourceBefore sourceAfter selectedMessage sourceDispatch
      targetBefore targetAfter selectedAction targetDispatch hStates

    exact
      detailedBoundPayload_consume_afterTime_forward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hStates

  · intro sourceBefore sourceAfter selectedMessage sourceDispatch
      targetBefore targetAfter selectedAction targetDispatch hStates

    exact
      detailedBoundPayload_consume_ready_forward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hStates

  · intro sourceBefore sourceAfter selectedMessage targetBefore
      sourceDispatch hSameTime hStates hCompatible

    exact
      detailedBoundPayload_consumeNow_forward_weak
        sourceDispatch
        hSameTime
        hStates
        hCompatible

  · intro sourceBefore targetBefore targetAfter targetLabel
      hTargetStep hStates

    exact
      detailedBoundPayload_statement_backward_weak
        hTargetStep
        hStates

  · intro sourceBefore targetBefore targetAfter selectedAction
      targetDispatch hTargetFuture hStates

    exact
      detailedBoundPayload_timeAdvance_backward_weak
        targetDispatch
        hTargetFuture
        hStates

  · intro sourceBefore sourceAfter selectedMessage sourceDispatch
      targetBefore targetAfter selectedAction targetDispatch
      hPositiveMicrostep hStates

    exact
      detailedBoundPayload_microstepAfterTime_backward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hPositiveMicrostep
        hStates

  · intro sourceBefore targetBefore targetAfter selectedAction
      targetDispatch hTargetSameTime hLaterMicrostep hStates

    exact
      detailedBoundPayload_microstepSameTime_backward_weak
        targetDispatch
        hTargetSameTime
        hLaterMicrostep
        hStates

  · intro sourceBefore sourceAfter selectedMessage sourceDispatch
      targetBefore targetAfter selectedAction targetDispatch
      hZeroMicrostep hStates

    exact
      detailedBoundPayload_consumeAfterTimeZero_backward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hZeroMicrostep
        hStates

  · intro sourceBefore sourceAfter selectedMessage sourceDispatch
      targetBefore targetAfter selectedAction targetDispatch hStates

    exact
      detailedBoundPayload_consumeReadyFuture_backward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hStates

  · intro sourceBefore targetBefore targetAfter selectedAction
      targetDispatch hStates

    exact
      detailedBoundPayload_consumeReadySameTime_backward_weak
        (targetDispatch := targetDispatch)
        hStates

  · intro sourceBefore targetBefore targetAfter selectedAction
      targetDispatch hSameTag hStates

    exact
      detailedBoundPayload_consumeNow_backward_weak
        targetDispatch
        hSameTag
        hStates


end Correctness
end Relico
