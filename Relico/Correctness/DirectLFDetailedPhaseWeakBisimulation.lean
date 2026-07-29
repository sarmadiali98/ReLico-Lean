import Relico.Correctness.DirectLFDetailedBackwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Complete phase-indexed weak-bisimulation interface for the ordinary DirectLF
translation.

The structure packages all five forward and eight backward phase obligations.
Its premises remain explicit:

* statement scheduling requires `DirectLFStatementAppendCompatible`;
* backward statement matching requires source-body well-formedness;
* queue selection compatibility is carried by the runtime-state relation.

LF metric-time and microstep transitions use the ordinary LF detailed
semantics. LF-only microstep transitions are matched by DTR weak stuttering.
-/
structure DirectLFDetailedPhaseWeakBisimulation
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer) :
    Prop where

  forwardStatementMatch :
    ∀ {sourceBefore sourceAfter : DTR.StoreState}
      {sourceLabel : DTR.Label}
      {targetBefore : LF.StoreState},
      DTR.MultiStoreStep
          declaredVariables
          (DTR.messageServerNames messageServers)
          sourceBefore
          sourceLabel
          sourceAfter →
        DirectLFDetailedRuntimeStateCorresponds
            messageServers
            (.stable sourceBefore)
            (.stable targetBefore) →
          DirectLFStatementAppendCompatible
              messageServers
              sourceBefore
              targetBefore →
            DirectLFDetailedForwardMatch
              declaredVariables
              messageServers
              .tau
              (.stable sourceAfter)
              (.stable targetBefore)

  forwardTimeAdvanceMatch :
    ∀ {sourceBefore sourceAfter : DTR.StoreState}
      {selectedMessage : DTR.PendingMessage}
      {selectedServer : DTR.MessageServer}
      {targetBefore : LF.StoreState},
      (hSourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter) →
        sourceBefore.currentTime <
            sourceAfter.currentTime →
          DirectLFDetailedRuntimeStateCorresponds
              messageServers
              (.stable sourceBefore)
              (.stable targetBefore) →
            DirectLFDetailedForwardMatch
              declaredVariables
              messageServers
              (.timeAdvance
                sourceBefore.currentTime
                sourceAfter.currentTime)
              (.dispatchReady
                sourceBefore
                selectedMessage
                selectedServer
                sourceAfter
                hSourceDispatch)
              (.stable targetBefore)

  forwardConsumeAfterTimeMatch :
    ∀ {sourceBefore sourceAfter : DTR.StoreState}
      {selectedMessage : DTR.PendingMessage}
      {selectedServer : DTR.MessageServer}
      {sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter}
      {targetBefore targetAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction}
      {targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter},
      DirectLFDetailedRuntimeStateCorresponds
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
        DirectLFDetailedForwardMatch
          declaredVariables
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
    ∀ {sourceBefore sourceAfter : DTR.StoreState}
      {selectedMessage : DTR.PendingMessage}
      {selectedServer : DTR.MessageServer}
      {sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter}
      {targetBefore targetAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction}
      {targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter},
      DirectLFDetailedRuntimeStateCorresponds
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
        DirectLFDetailedForwardMatch
          declaredVariables
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
    ∀ {sourceBefore sourceAfter : DTR.StoreState}
      {selectedMessage : DTR.PendingMessage}
      {selectedServer : DTR.MessageServer}
      {targetBefore : LF.StoreState},
      DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter →
        sourceBefore.currentTime =
            sourceAfter.currentTime →
          DirectLFDetailedRuntimeStateCorresponds
              messageServers
              (.stable sourceBefore)
              (.stable targetBefore) →
            DirectLFDetailedForwardMatch
              declaredVariables
              messageServers
              (.consume
                selectedMessage
                selectedServer)
              (.stable sourceAfter)
              (.stable targetBefore)

  backwardStatementMatch :
    ∀ {sourceBefore : DTR.StoreState}
      {targetBefore targetAfter : LF.StoreState}
      {targetLabel : LF.Label},
      LF.MultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions messageServers)
          targetBefore
          targetLabel
          targetAfter →
        DirectLFDetailedRuntimeStateCorresponds
            messageServers
            (.stable sourceBefore)
            (.stable targetBefore) →
          DirectLFStatementAppendCompatible
              messageServers
              sourceBefore
              targetBefore →
            DTR.Body.MultiStoreWellFormed
                declaredVariables
                (DTR.messageServerNames messageServers)
                sourceBefore.activeBody →
              DirectLFDetailedBackwardMatch
                declaredVariables
                messageServers
                .tau
                (.stable targetAfter)
                (.stable sourceBefore)

  backwardTimeAdvanceMatch :
    ∀ {sourceBefore : DTR.StoreState}
      {targetBefore targetAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction},
      (hTargetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter) →
        targetBefore.currentTag.time <
            targetAfter.currentTag.time →
          DirectLFDetailedRuntimeStateCorresponds
              messageServers
              (.stable sourceBefore)
              (.stable targetBefore) →
            DirectLFDetailedBackwardMatch
              declaredVariables
              messageServers
              (.timeAdvance
                targetBefore.currentTag.time
                targetAfter.currentTag.time)
              (.afterTime
                targetBefore
                selectedAction
                selectedReaction
                targetAfter
                hTargetDispatch)
              (.stable sourceBefore)

  backwardMicrostepAfterTimeMatch :
    ∀ {sourceBefore sourceAfter : DTR.StoreState}
      {selectedMessage : DTR.PendingMessage}
      {sourceServer : DTR.MessageServer}
      {sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter}
      {targetBefore targetAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction}
      {targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter},
      0 < targetAfter.currentTag.microstep →
        DirectLFDetailedRuntimeStateCorresponds
            messageServers
            (.dispatchReady
              sourceBefore
              selectedMessage
              sourceServer
              sourceAfter
              sourceDispatch)
            (.afterTime
              targetBefore
              selectedAction
              selectedReaction
              targetAfter
              targetDispatch) →
          DirectLFDetailedBackwardMatch
            declaredVariables
            messageServers
            (.microstepAdvance
              {
                time := targetAfter.currentTag.time
                microstep := 0
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
              sourceServer
              sourceAfter
              sourceDispatch)

  backwardMicrostepSameTimeMatch :
    ∀ {sourceBefore : DTR.StoreState}
      {targetBefore targetAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction},
      (hTargetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter) →
        targetBefore.currentTag.time =
            targetAfter.currentTag.time →
          targetBefore.currentTag.microstep <
              targetAfter.currentTag.microstep →
            DirectLFDetailedRuntimeStateCorresponds
                messageServers
                (.stable sourceBefore)
                (.stable targetBefore) →
              DirectLFDetailedBackwardMatch
                declaredVariables
                messageServers
                (.microstepAdvance
                  targetBefore.currentTag
                  targetAfter.currentTag)
                (.dispatchReady
                  targetBefore
                  selectedAction
                  selectedReaction
                  targetAfter
                  hTargetDispatch)
                (.stable sourceBefore)

  backwardConsumeAfterTimeZeroMatch :
    ∀ {sourceBefore sourceAfter : DTR.StoreState}
      {selectedMessage : DTR.PendingMessage}
      {sourceServer : DTR.MessageServer}
      {sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter}
      {targetBefore targetAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction}
      {targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter},
      targetAfter.currentTag.microstep = 0 →
        DirectLFDetailedRuntimeStateCorresponds
            messageServers
            (.dispatchReady
              sourceBefore
              selectedMessage
              sourceServer
              sourceAfter
              sourceDispatch)
            (.afterTime
              targetBefore
              selectedAction
              selectedReaction
              targetAfter
              targetDispatch) →
          DirectLFDetailedBackwardMatch
            declaredVariables
            messageServers
            (.consume
              selectedAction
              selectedReaction)
            (.stable targetAfter)
            (.dispatchReady
              sourceBefore
              selectedMessage
              sourceServer
              sourceAfter
              sourceDispatch)

  backwardConsumeReadyFutureMatch :
    ∀ {sourceBefore sourceAfter : DTR.StoreState}
      {selectedMessage : DTR.PendingMessage}
      {sourceServer : DTR.MessageServer}
      {sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter}
      {targetBefore targetAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction}
      {targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter},
      DirectLFDetailedRuntimeStateCorresponds
          messageServers
          (.dispatchReady
            sourceBefore
            selectedMessage
            sourceServer
            sourceAfter
            sourceDispatch)
          (.dispatchReady
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch) →
        DirectLFDetailedBackwardMatch
          declaredVariables
          messageServers
          (.consume
            selectedAction
            selectedReaction)
          (.stable targetAfter)
          (.dispatchReady
            sourceBefore
            selectedMessage
            sourceServer
            sourceAfter
            sourceDispatch)

  backwardConsumeReadySameTimeMatch :
    ∀ {sourceBefore : DTR.StoreState}
      {targetBefore targetAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction}
      {targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter},
      DirectLFDetailedRuntimeStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.dispatchReady
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch) →
        DirectLFDetailedBackwardMatch
          declaredVariables
          messageServers
          (.consume
            selectedAction
            selectedReaction)
          (.stable targetAfter)
          (.stable sourceBefore)

  backwardConsumeNowMatch :
    ∀ {sourceBefore : DTR.StoreState}
      {targetBefore targetAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction},
      LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter →
        targetBefore.currentTag.time =
            targetAfter.currentTag.time →
          targetBefore.currentTag.microstep =
              targetAfter.currentTag.microstep →
            DirectLFDetailedRuntimeStateCorresponds
                messageServers
                (.stable sourceBefore)
                (.stable targetBefore) →
              DirectLFDetailedBackwardMatch
                declaredVariables
                messageServers
                (.consume
                  selectedAction
                  selectedReaction)
                (.stable targetAfter)
                (.stable sourceBefore)

/--
The ordinary DirectLF translation satisfies all thirteen phase-indexed
weak-simulation obligations.
-/
theorem directLFDetailedRuntime_phaseWeakBisimulation
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer) :
    DirectLFDetailedPhaseWeakBisimulation
      declaredVariables
      messageServers := by

  exact {
    forwardStatementMatch :=
      directLFDetailedRuntime_statement_forward_weak

    forwardTimeAdvanceMatch :=
      directLFDetailedRuntime_timeAdvance_forward_weak

    forwardConsumeAfterTimeMatch :=
      directLFDetailedRuntime_consume_afterTime_forward_weak

    forwardConsumeReadyMatch :=
      directLFDetailedRuntime_consume_ready_forward_weak

    forwardConsumeNowMatch :=
      directLFDetailedRuntime_consumeNow_forward_weak

    backwardStatementMatch :=
      directLFDetailedRuntime_statement_backward_weak

    backwardTimeAdvanceMatch :=
      directLFDetailedRuntime_timeAdvance_backward_weak

    backwardMicrostepAfterTimeMatch :=
      directLFDetailedRuntime_microstepAfterTime_backward_weak

    backwardMicrostepSameTimeMatch :=
      directLFDetailedRuntime_microstepSameTime_backward_weak

    backwardConsumeAfterTimeZeroMatch :=
      directLFDetailedRuntime_consumeAfterTimeZero_backward_weak

    backwardConsumeReadyFutureMatch :=
      directLFDetailedRuntime_consumeReadyFuture_backward_weak

    backwardConsumeReadySameTimeMatch :=
      directLFDetailedRuntime_consumeReadySameTime_backward_weak

    backwardConsumeNowMatch :=
      directLFDetailedRuntime_consumeNow_backward_weak
  }

end Correctness
end Relico
