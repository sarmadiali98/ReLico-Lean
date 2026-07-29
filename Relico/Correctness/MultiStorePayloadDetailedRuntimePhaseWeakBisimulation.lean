import Relico.Correctness.MultiStorePayloadDetailedDispatchWeakMatches
import Relico.Correctness.MultiStorePayloadDetailedStatementForwardWeakMatch
import Relico.Correctness.MultiStorePayloadDetailedStatementBackwardWeakMatch

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
The complete phase-indexed weak-simulation interface for the payload-aware
multi-server runtime.

The statement fields retain the explicit runtime-compatibility premise needed
when a payload self-send appends a new occurrence. The dispatch fields reuse
the published runtime-state correspondence directly. LF microsteps remain
target-only and are matched by DTR weak tau behavior.
-/
structure MultiStorePayloadDetailedRuntimePhaseWeakBisimulation
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    Prop where

  forwardStatementMatch :
    ∀ {
        sourceBefore sourceAfter :
          DTR.MultiStorePayloadState
      }
      {
        targetBefore :
          LF.MultiStorePayloadState
      },

      DTR.MultiStorePayloadStep
          sourceBefore
          sourceAfter →

        MultiStorePayloadDetailedRuntimeStateCorresponds
            messageServers
            (.stable sourceBefore)
            (.stable targetBefore) →

          MultiStorePayloadStatementRuntimeCompatible
              messageServers
              sourceBefore
              targetBefore →

            MultiStorePayloadDetailedForwardMatch
              messageServers
              .tau
              (.stable sourceAfter)
              (.stable targetBefore)

  forwardTimeAdvanceMatch :
    ∀ {
        sourceBefore sourceAfter :
          DTR.MultiStorePayloadState
      }
      {
        selectedMessage :
          DTR.PendingMessage
      }
      {
        selectedServer :
          DTR.MultiStorePayloadMessageServer
      }
      {
        targetBefore :
          LF.MultiStorePayloadState
      }
      (sourceDispatch :
        DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter),

      sourceBefore.currentTime <
          sourceAfter.currentTime →

        MultiStorePayloadDetailedRuntimeStateCorresponds
            messageServers
            (.stable sourceBefore)
            (.stable targetBefore) →

          MultiStorePayloadDetailedForwardMatch
            messageServers
            (.timeAdvance
              sourceBefore.currentTime
              sourceAfter.currentTime)
            (.dispatchReady
              sourceBefore
              selectedMessage
              selectedServer
              sourceAfter
              sourceDispatch)
            (.stable targetBefore)

  forwardConsumeAfterTimeMatch :
    ∀ {
        sourceBefore sourceAfter :
          DTR.MultiStorePayloadState
      }
      {
        selectedMessage :
          DTR.PendingMessage
      }
      {
        selectedServer :
          DTR.MultiStorePayloadMessageServer
      }
      {
        sourceDispatch :
          DTR.MultiStorePayloadDispatchStep
            messageServers
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      }
      {
        selectedAction :
          LF.PendingAction
      }
      {
        selectedReaction :
          LF.MultiStorePayloadReaction
      }
      {
        targetDispatch :
          LF.MultiStorePayloadDispatchStep
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers)
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
      },

      MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          (.dispatchReady
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
            sourceDispatch)
          (.afterTime
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch) →

        MultiStorePayloadDetailedForwardMatch
          messageServers
          (.consume
            selectedMessage
            selectedServer)
          (.stable sourceAfter)
          (.afterTime
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch)

  forwardConsumeReadyMatch :
    ∀ {
        sourceBefore sourceAfter :
          DTR.MultiStorePayloadState
      }
      {
        selectedMessage :
          DTR.PendingMessage
      }
      {
        selectedServer :
          DTR.MultiStorePayloadMessageServer
      }
      {
        sourceDispatch :
          DTR.MultiStorePayloadDispatchStep
            messageServers
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      }
      {
        selectedAction :
          LF.PendingAction
      }
      {
        selectedReaction :
          LF.MultiStorePayloadReaction
      }
      {
        targetDispatch :
          LF.MultiStorePayloadDispatchStep
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers)
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
      },

      MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          (.dispatchReady
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
            sourceDispatch)
          (.dispatchReady
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch) →

        MultiStorePayloadDetailedForwardMatch
          messageServers
          (.consume
            selectedMessage
            selectedServer)
          (.stable sourceAfter)
          (.dispatchReady
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch)

  forwardConsumeNowMatch :
    ∀ {
        sourceBefore sourceAfter :
          DTR.MultiStorePayloadState
      }
      {
        selectedMessage :
          DTR.PendingMessage
      }
      {
        selectedServer :
          DTR.MultiStorePayloadMessageServer
      }
      {
        targetBefore :
          LF.MultiStorePayloadState
      }
      (sourceDispatch :
        DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter),

      sourceBefore.currentTime =
          sourceAfter.currentTime →

        MultiStorePayloadDetailedRuntimeStateCorresponds
            messageServers
            (.stable sourceBefore)
            (.stable targetBefore) →

          MultiStorePayloadDetailedForwardMatch
            messageServers
            (.consume
              selectedMessage
              selectedServer)
            (.stable sourceAfter)
            (.stable targetBefore)

  backwardStatementMatch :
    ∀ {
        sourceBefore :
          DTR.MultiStorePayloadState
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      },

      LF.MultiStorePayloadStep
          targetBefore
          targetAfter →

        MultiStorePayloadDetailedRuntimeStateCorresponds
            messageServers
            (.stable sourceBefore)
            (.stable targetBefore) →

          MultiStorePayloadStatementRuntimeCompatible
              messageServers
              sourceBefore
              targetBefore →

            MultiStorePayloadDetailedBackwardMatch
              messageServers
              .tau
              (.stable targetAfter)
              (.stable sourceBefore)

  backwardTimeAdvanceMatch :
    ∀ {
        sourceBefore :
          DTR.MultiStorePayloadState
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      }
      {
        selectedAction :
          LF.PendingAction
      }
      {
        selectedReaction :
          LF.MultiStorePayloadReaction
      }
      (targetDispatch :
        LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),

      targetBefore.currentTag.time <
          targetAfter.currentTag.time →

        MultiStorePayloadDetailedRuntimeStateCorresponds
            messageServers
            (.stable sourceBefore)
            (.stable targetBefore) →

          MultiStorePayloadDetailedBackwardMatch
            messageServers
            (.timeAdvance
              targetBefore.currentTag.time
              targetAfter.currentTag.time)
            (.afterTime
              targetBefore
              selectedAction
              selectedReaction
              targetAfter
              targetDispatch)
            (.stable sourceBefore)

  backwardMicrostepAfterTimeMatch :
    ∀ {
        sourceBefore sourceAfter :
          DTR.MultiStorePayloadState
      }
      {
        selectedMessage :
          DTR.PendingMessage
      }
      {
        selectedServer :
          DTR.MultiStorePayloadMessageServer
      }
      {
        sourceDispatch :
          DTR.MultiStorePayloadDispatchStep
            messageServers
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      }
      {
        selectedAction :
          LF.PendingAction
      }
      {
        selectedReaction :
          LF.MultiStorePayloadReaction
      }
      {
        targetDispatch :
          LF.MultiStorePayloadDispatchStep
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers)
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
      },

      0 <
          targetAfter.currentTag.microstep →

        MultiStorePayloadDetailedRuntimeStateCorresponds
            messageServers
            (.dispatchReady
              sourceBefore
              selectedMessage
              selectedServer
              sourceAfter
              sourceDispatch)
            (.afterTime
              targetBefore
              selectedAction
              selectedReaction
              targetAfter
              targetDispatch) →

          MultiStorePayloadDetailedBackwardMatch
            messageServers
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
              selectedReaction
              targetAfter
              targetDispatch)
            (.dispatchReady
              sourceBefore
              selectedMessage
              selectedServer
              sourceAfter
              sourceDispatch)

  backwardMicrostepSameTimeMatch :
    ∀ {
        sourceBefore :
          DTR.MultiStorePayloadState
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      }
      {
        selectedAction :
          LF.PendingAction
      }
      {
        selectedReaction :
          LF.MultiStorePayloadReaction
      }
      (targetDispatch :
        LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),

      targetBefore.currentTag.time =
          targetAfter.currentTag.time →

        targetBefore.currentTag.microstep <
            targetAfter.currentTag.microstep →

          MultiStorePayloadDetailedRuntimeStateCorresponds
              messageServers
              (.stable sourceBefore)
              (.stable targetBefore) →

            MultiStorePayloadDetailedBackwardMatch
              messageServers
              (.microstepAdvance
                targetBefore.currentTag
                targetAfter.currentTag)
              (.dispatchReady
                targetBefore
                selectedAction
                selectedReaction
                targetAfter
                targetDispatch)
              (.stable sourceBefore)

  backwardConsumeAfterTimeZeroMatch :
    ∀ {
        sourceBefore sourceAfter :
          DTR.MultiStorePayloadState
      }
      {
        selectedMessage :
          DTR.PendingMessage
      }
      {
        selectedServer :
          DTR.MultiStorePayloadMessageServer
      }
      {
        sourceDispatch :
          DTR.MultiStorePayloadDispatchStep
            messageServers
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      }
      {
        selectedAction :
          LF.PendingAction
      }
      {
        selectedReaction :
          LF.MultiStorePayloadReaction
      }
      {
        targetDispatch :
          LF.MultiStorePayloadDispatchStep
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers)
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
      },

      targetAfter.currentTag.microstep =
          0 →

        MultiStorePayloadDetailedRuntimeStateCorresponds
            messageServers
            (.dispatchReady
              sourceBefore
              selectedMessage
              selectedServer
              sourceAfter
              sourceDispatch)
            (.afterTime
              targetBefore
              selectedAction
              selectedReaction
              targetAfter
              targetDispatch) →

          MultiStorePayloadDetailedBackwardMatch
            messageServers
            (.consume
              selectedAction
              selectedReaction)
            (.stable targetAfter)
            (.dispatchReady
              sourceBefore
              selectedMessage
              selectedServer
              sourceAfter
              sourceDispatch)

  backwardConsumeReadyFutureMatch :
    ∀ {
        sourceBefore sourceAfter :
          DTR.MultiStorePayloadState
      }
      {
        selectedMessage :
          DTR.PendingMessage
      }
      {
        selectedServer :
          DTR.MultiStorePayloadMessageServer
      }
      {
        sourceDispatch :
          DTR.MultiStorePayloadDispatchStep
            messageServers
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      }
      {
        selectedAction :
          LF.PendingAction
      }
      {
        selectedReaction :
          LF.MultiStorePayloadReaction
      }
      {
        targetDispatch :
          LF.MultiStorePayloadDispatchStep
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers)
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
      },

      MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          (.dispatchReady
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
            sourceDispatch)
          (.dispatchReady
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch) →

        MultiStorePayloadDetailedBackwardMatch
          messageServers
          (.consume
            selectedAction
            selectedReaction)
          (.stable targetAfter)
          (.dispatchReady
            sourceBefore
            selectedMessage
            selectedServer
            sourceAfter
            sourceDispatch)

  backwardConsumeReadySameTimeMatch :
    ∀ {
        sourceBefore :
          DTR.MultiStorePayloadState
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      }
      {
        selectedAction :
          LF.PendingAction
      }
      {
        selectedReaction :
          LF.MultiStorePayloadReaction
      }
      {
        targetDispatch :
          LF.MultiStorePayloadDispatchStep
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers)
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
      },

      MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.dispatchReady
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch) →

        MultiStorePayloadDetailedBackwardMatch
          messageServers
          (.consume
            selectedAction
            selectedReaction)
          (.stable targetAfter)
          (.stable sourceBefore)

  backwardConsumeNowMatch :
    ∀ {
        sourceBefore :
          DTR.MultiStorePayloadState
      }
      {
        targetBefore targetAfter :
          LF.MultiStorePayloadState
      }
      {
        selectedAction :
          LF.PendingAction
      }
      {
        selectedReaction :
          LF.MultiStorePayloadReaction
      }
      (targetDispatch :
        LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),

      targetBefore.currentTag.time =
          targetAfter.currentTag.time →

        targetBefore.currentTag.microstep =
            targetAfter.currentTag.microstep →

          MultiStorePayloadDetailedRuntimeStateCorresponds
              messageServers
              (.stable sourceBefore)
              (.stable targetBefore) →

            MultiStorePayloadDetailedBackwardMatch
              messageServers
              (.consume
                selectedAction
                selectedReaction)
              (.stable targetAfter)
              (.stable sourceBefore)

/--
Every phase-indexed payload statement and dispatch obligation is discharged by
the published forward and backward weak-match theorems.
-/
theorem multiStorePayloadDetailedRuntime_phaseWeakBisimulation
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    MultiStorePayloadDetailedRuntimePhaseWeakBisimulation
      messageServers :=

  {
    forwardStatementMatch :=
      multiStorePayloadDetailedRuntime_statement_forward_weak

    forwardTimeAdvanceMatch :=
      multiStorePayloadDetailedRuntime_timeAdvance_forward_weak

    forwardConsumeAfterTimeMatch :=
      multiStorePayloadDetailedRuntime_consume_afterTime_forward_weak

    forwardConsumeReadyMatch :=
      multiStorePayloadDetailedRuntime_consume_ready_forward_weak

    forwardConsumeNowMatch :=
      multiStorePayloadDetailedRuntime_consumeNow_forward_weak

    backwardStatementMatch :=
      multiStorePayloadDetailedRuntime_statement_backward_weak

    backwardTimeAdvanceMatch :=
      multiStorePayloadDetailedRuntime_timeAdvance_backward_weak

    backwardMicrostepAfterTimeMatch :=
      multiStorePayloadDetailedRuntime_microstepAfterTime_backward_weak

    backwardMicrostepSameTimeMatch :=
      multiStorePayloadDetailedRuntime_microstepSameTime_backward_weak

    backwardConsumeAfterTimeZeroMatch :=
      multiStorePayloadDetailedRuntime_consumeAfterTimeZero_backward_weak

    backwardConsumeReadyFutureMatch :=
      multiStorePayloadDetailedRuntime_consumeReadyFuture_backward_weak

    backwardConsumeReadySameTimeMatch :=
      multiStorePayloadDetailedRuntime_consumeReadySameTime_backward_weak

    backwardConsumeNowMatch :=
      multiStorePayloadDetailedRuntime_consumeNow_backward_weak
  }

end Correctness
end Relico
