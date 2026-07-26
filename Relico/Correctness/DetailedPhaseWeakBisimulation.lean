import Relico.Correctness.DetailedBackwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
The complete phase-indexed two-directional weak-simulation interface for the
concrete detailed finite-store translation.

Every field retains the exact side conditions of its underlying executable
correspondence theorem. This is therefore not a premise-free global
coinductive bisimulation over arbitrary related states.
-/
structure ConcreteDetailedPhaseWeakBisimulation
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer) :
    Prop where

  forwardStatementMatch :
    ∀ (sourceBefore sourceAfter : DTR.StoreState)
      (sourceLabel : DTR.Label)
      (targetBefore : LF.StoreState),
      DTR.MultiStoreStep
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          sourceBefore
          sourceLabel
          sourceAfter →
        ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.stable targetBefore) →
        ConcreteDetailedForwardMatch
          declaredVariables
          messageServers
          DTR.DetailedMultiStoreLabel.tau
          (.stable sourceAfter)
          (.stable targetBefore)

  forwardTimeAdvanceMatch :
    ∀ (sourceBefore sourceAfter : DTR.StoreState)
      (selectedMessage : DTR.PendingMessage)
      (selectedServer : DTR.MessageServer)
      (targetBefore : LF.StoreState)
      (sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter),
      sourceBefore.currentTime <
          sourceAfter.currentTime →
        ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.stable targetBefore) →
        StoreForwardDispatchCompatible
          selectedMessage
          sourceAfter.pendingMessages
          targetBefore →
        ConcreteDetailedForwardMatch
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
            sourceDispatch)
          (.stable targetBefore)

  forwardConsumeAfterTimeMatch :
    ∀ (sourceBefore sourceAfter : DTR.StoreState)
      (selectedMessage : DTR.PendingMessage)
      (selectedServer : DTR.MessageServer)
      (sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter)
      (targetBefore targetAfter : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),
      ConcreteDetailedStateCorresponds
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
        ConcreteDetailedForwardMatch
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
    ∀ (sourceBefore sourceAfter : DTR.StoreState)
      (selectedMessage : DTR.PendingMessage)
      (selectedServer : DTR.MessageServer)
      (sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter)
      (targetBefore targetAfter : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),
      ConcreteDetailedStateCorresponds
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
        ConcreteDetailedForwardMatch
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
    ∀ (sourceBefore sourceAfter : DTR.StoreState)
      (selectedMessage : DTR.PendingMessage)
      (selectedServer : DTR.MessageServer)
      (targetBefore : LF.StoreState),
      DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter →
        sourceBefore.currentTime =
            sourceAfter.currentTime →
        ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.stable targetBefore) →
        StoreForwardDispatchCompatible
          selectedMessage
          sourceAfter.pendingMessages
          targetBefore →
        ConcreteDetailedForwardMatch
          declaredVariables
          messageServers
          (.consume
            selectedMessage
            selectedServer)
          (.stable sourceAfter)
          (.stable targetBefore)

  backwardStatementMatch :
    ∀ (sourceBefore : DTR.StoreState)
      (targetBefore targetAfter : LF.StoreState)
      (targetLabel : LF.Label),
      LF.MultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          targetBefore
          targetLabel
          targetAfter →
        ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.stable targetBefore) →
        DTR.Body.MultiStoreWellFormed
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          sourceBefore.activeBody →
        ConcreteDetailedBackwardMatch
          declaredVariables
          messageServers
          LF.DetailedMultiStoreLabel.tau
          (.stable targetAfter)
          (.stable sourceBefore)

  backwardTimeAdvanceMatch :
    ∀ (sourceBefore : DTR.StoreState)
      (targetBefore targetAfter : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),
      targetBefore.currentTag.time <
          targetAfter.currentTag.time →
        ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.stable targetBefore) →
        LF.StoreState.PendingMicrostepsZero
          targetBefore →
        ConcreteDetailedBackwardMatch
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
            targetDispatch)
          (.stable sourceBefore)

  backwardMicrostepAfterTimeMatch :
    ∀ (sourceBefore sourceAfter : DTR.StoreState)
      (selectedMessage : DTR.PendingMessage)
      (sourceServer : DTR.MessageServer)
      (sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter)
      (targetBefore targetAfter : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),
      0 <
          targetAfter.currentTag.microstep →
        ConcreteDetailedStateCorresponds
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
        ConcreteDetailedBackwardMatch
          declaredVariables
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
            sourceServer
            sourceAfter
            sourceDispatch)

  backwardMicrostepSameTimeMatch :
    ∀ (sourceBefore : DTR.StoreState)
      (targetBefore targetAfter : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),
      targetBefore.currentTag.time =
          targetAfter.currentTag.time →
        targetBefore.currentTag.microstep <
            targetAfter.currentTag.microstep →
        ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.stable targetBefore) →
        LF.StoreState.PendingMicrostepsZero
          targetBefore →
        ConcreteDetailedBackwardMatch
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
            targetDispatch)
          (.stable sourceBefore)

  backwardConsumeAfterTimeZeroMatch :
    ∀ (sourceBefore sourceAfter : DTR.StoreState)
      (selectedMessage : DTR.PendingMessage)
      (sourceServer : DTR.MessageServer)
      (sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter)
      (targetBefore targetAfter : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),
      targetAfter.currentTag.microstep =
          0 →
        ConcreteDetailedStateCorresponds
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
        ConcreteDetailedBackwardMatch
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
    ∀ (sourceBefore sourceAfter : DTR.StoreState)
      (selectedMessage : DTR.PendingMessage)
      (sourceServer : DTR.MessageServer)
      (sourceDispatch :
        DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter)
      (targetBefore targetAfter : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),
      ConcreteDetailedStateCorresponds
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
        ConcreteDetailedBackwardMatch
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
    ∀ (sourceBefore : DTR.StoreState)
      (targetBefore targetAfter : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (targetDispatch :
        LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter),
      ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.dispatchReady
            targetBefore
            selectedAction
            selectedReaction
            targetAfter
            targetDispatch) →
        ConcreteDetailedBackwardMatch
          declaredVariables
          messageServers
          (.consume
            selectedAction
            selectedReaction)
          (.stable targetAfter)
          (.stable sourceBefore)

  backwardConsumeNowMatch :
    ∀ (sourceBefore : DTR.StoreState)
      (targetBefore targetAfter : LF.StoreState)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction),
      LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter →
        targetBefore.currentTag.time =
            targetAfter.currentTag.time →
        targetBefore.currentTag.microstep =
            targetAfter.currentTag.microstep →
        ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceBefore)
          (.stable targetBefore) →
        LF.StoreState.PendingMicrostepsZero
          targetBefore →
        ConcreteDetailedBackwardMatch
          declaredVariables
          messageServers
          (.consume
            selectedAction
            selectedReaction)
          (.stable targetAfter)
          (.stable sourceBefore)

/--
The concrete detailed semantics satisfies all phase-indexed forward and
backward weak-simulation obligations.
-/
theorem concreteDetailed_phaseWeakBisimulation
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer) :
    ConcreteDetailedPhaseWeakBisimulation
      declaredVariables
      messageServers := by

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
      concreteDetailed_statement_forward_weak
        hSourceStep
        hStates

  · intro sourceBefore sourceAfter selectedMessage selectedServer
      targetBefore sourceDispatch hFuture hStates hCompatible

    exact
      concreteDetailed_timeAdvance_forward_weak
        sourceDispatch
        hFuture
        hStates
        hCompatible

  · intro sourceBefore sourceAfter selectedMessage selectedServer
      sourceDispatch targetBefore targetAfter selectedAction
      selectedReaction targetDispatch hStates

    exact
      concreteDetailed_consume_afterTime_forward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hStates

  · intro sourceBefore sourceAfter selectedMessage selectedServer
      sourceDispatch targetBefore targetAfter selectedAction
      selectedReaction targetDispatch hStates

    exact
      concreteDetailed_consume_ready_forward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hStates

  · intro sourceBefore sourceAfter selectedMessage selectedServer
      targetBefore hSourceDispatch hSameTime hStates hCompatible

    exact
      concreteDetailed_consumeNow_forward_weak
        hSourceDispatch
        hSameTime
        hStates
        hCompatible

  · intro sourceBefore targetBefore targetAfter targetLabel
      hTargetStep hStates hSourceBodyWellFormed

    exact
      concreteDetailed_statement_backward_weak
        hTargetStep
        hStates
        hSourceBodyWellFormed

  · intro sourceBefore targetBefore targetAfter selectedAction
      selectedReaction targetDispatch hFuture hStates
      hTargetMicrostepsZero

    exact
      concreteDetailed_timeAdvance_backward_weak
        targetDispatch
        hFuture
        hStates
        hTargetMicrostepsZero

  · intro sourceBefore sourceAfter selectedMessage sourceServer
      sourceDispatch targetBefore targetAfter selectedAction
      selectedReaction targetDispatch hPositiveMicrostep hStates

    exact
      concreteDetailed_microstepAfterTime_backward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hPositiveMicrostep
        hStates

  · intro sourceBefore targetBefore targetAfter selectedAction
      selectedReaction targetDispatch hSameTime hLaterMicrostep
      hStates hTargetMicrostepsZero

    exact
      concreteDetailed_microstepSameTime_backward_weak
        targetDispatch
        hSameTime
        hLaterMicrostep
        hStates
        hTargetMicrostepsZero

  · intro sourceBefore sourceAfter selectedMessage sourceServer
      sourceDispatch targetBefore targetAfter selectedAction
      selectedReaction targetDispatch hZeroMicrostep hStates

    exact
      concreteDetailed_consumeAfterTimeZero_backward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hZeroMicrostep
        hStates

  · intro sourceBefore sourceAfter selectedMessage sourceServer
      sourceDispatch targetBefore targetAfter selectedAction
      selectedReaction targetDispatch hStates

    exact
      concreteDetailed_consumeReadyFuture_backward_weak
        (sourceDispatch := sourceDispatch)
        (targetDispatch := targetDispatch)
        hStates

  · intro sourceBefore targetBefore targetAfter selectedAction
      selectedReaction targetDispatch hStates

    exact
      concreteDetailed_consumeReadySameTime_backward_weak
        (targetDispatch := targetDispatch)
        hStates

  · intro sourceBefore targetBefore targetAfter selectedAction
      selectedReaction hTargetDispatch hSameTime hSameMicrostep
      hStates hTargetMicrostepsZero

    exact
      concreteDetailed_consumeNow_backward_weak
        hTargetDispatch
        hSameTime
        hSameMicrostep
        hStates
        hTargetMicrostepsZero

end Correctness
end Relico
