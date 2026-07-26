import Relico.Correctness.DetailedInvariantCarryingBackwardMatch

set_option autoImplicit false

namespace Relico
namespace Correctness

def ConcreteDetailedForwardInvariantMatch
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (sourceLabel :
      DTR.DetailedMultiStoreLabel)
    (sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers)
    (targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)) :
    Prop :=

  ∃ targetLabel :
      LF.DetailedMultiStoreLabel,

    ∃ targetAfter :
        LF.DetailedMultiStoreState
          (Translation.compileMessageReactions
            messageServers),

      LF.DetailedWeakStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          targetLabel
          targetAfter ∧

        ConcreteDetailedLabelCorresponds
          sourceLabel
          targetLabel ∧

        ConcreteDetailedStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧

        ConcreteDetailedSourceRuntimeInvariant
          declaredVariables
          messageServers
          sourceAfter ∧

        ConcreteDetailedTargetRuntimeInvariant
          messageServers
          targetAfter

theorem concreteDetailedForwardInvariantMatch
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers}
    {sourceLabel :
      DTR.DetailedMultiStoreLabel}
    {targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    (hSourceStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hSourceInvariant :
      ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceBefore)
    (hTargetInvariant :
      ConcreteDetailedTargetRuntimeInvariant
        messageServers
        targetBefore)
    (hMessageBodiesWellFormed :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.MultiStoreWellFormed
            declaredVariables
            (DTR.messageServerNames
              messageServers)
            messageServer.body)
    (hMessageBodiesTiming :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.PriorityTimingWellFormed
            messageServer.body) :
    ConcreteDetailedForwardInvariantMatch
      declaredVariables
      messageServers
      sourceLabel
      sourceAfter
      targetBefore := by

  have hFinalSourceInvariant :
      ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceAfter :=

    concreteDetailedSourceRuntimeInvariant_preserved
      hSourceStep
      hMessageBodiesWellFormed
      hMessageBodiesTiming
      hSourceInvariant

  cases hSourceStep with

  | statement hSourceStatement =>

      cases hStates with

      | stable hStable =>

          have hDetailedStates :
              ConcreteDetailedStateCorresponds
                messageServers
                (.stable _)
                (.stable _) :=

            DetailedStateCorresponds.stable
              hStable

          rcases
              concreteDetailed_statement_forward
                hSourceStatement
                hDetailedStates
            with
              ⟨targetStatementLabel,
               targetAfter,
               hTargetStatement,
               hStatementLabels,
               hTargetDetailedStep,
               hFinalStates⟩

          have hFinalTargetInvariant :
              ConcreteDetailedTargetRuntimeInvariant
                messageServers
                (.stable targetAfter) :=

            concreteDetailedTargetRuntimeInvariant_preserved
              hTargetDetailedStep
              hDetailedStates
              hSourceInvariant
              hTargetInvariant

          exact
            ⟨LF.DetailedMultiStoreLabel.tau,
             LF.DetailedMultiStoreState.stable
               targetAfter,
             LF.detailedWeakStep_of_step
               hTargetDetailedStep,
             ConcreteDetailedLabelCorresponds.tau,
             hFinalStates,
             hFinalSourceInvariant,
             hFinalTargetInvariant⟩

      | sameTimeMicrostepAhead =>
          simp [
            ConcreteDetailedTargetRuntimeInvariant
          ] at hTargetInvariant

  | timeAdvance
      hSourceDispatch
      hSourceFuture =>

      cases hStates with

      | stable hStable =>

          rename_i
            sourceBefore
            sourceAfter
            selectedMessage
            selectedServer
            targetBefore

          have hDetailedStates :
              ConcreteDetailedStateCorresponds
                messageServers
                (.stable _)
                (.stable _) :=

            DetailedStateCorresponds.stable
              hStable

          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          have hCompatible :
              StoreForwardDispatchCompatible
                _
                _
                _ :=

            storeForwardDispatchCompatible_of_priorityRuntimeInvariant
              hSourceDispatch
              hStable
              hTargetStable

          rcases
              concreteDetailed_dispatch_forward_of_compatible
                hSourceDispatch
                hDetailedStates
                hCompatible
            with
              ⟨selectedAction,
               selectedReaction,
               targetAfter,
               hTargetDispatch,
               hWitness⟩

          have hTargetFuture :
              targetBefore.currentTag.time <
                targetAfter.currentTag.time := by

            calc
              targetBefore.currentTag.time =
                  _ :=
                hWitness.beforeState.currentTime

              _ <
                  _ :=
                hSourceFuture

              _ =
                  targetAfter.currentTag.time :=
                hWitness.afterState.currentTime.symm

          have hTargetDetailedStep :
              LF.DetailedMultiStoreStep
                declaredVariables
                (Translation.compileLogicalActions
                  messageServers)
                (Translation.compileMessageReactions
                  messageServers)
                (.stable targetBefore)
                (.timeAdvance
                  targetBefore.currentTag.time
                  targetAfter.currentTag.time)
                (.afterTime
                  targetBefore
                  selectedAction
                  selectedReaction
                  targetAfter
                  hTargetDispatch) :=

            LF.DetailedMultiStoreStep.timeAdvance
              hTargetDispatch
              hTargetFuture

          have hFinalStates :
              ConcreteDetailedStateCorresponds
                messageServers
                (.dispatchReady
                  sourceBefore
                  selectedMessage
                  selectedServer
                  sourceAfter
                  hSourceDispatch)
                (.afterTime
                  targetBefore
                  selectedAction
                  selectedReaction
                  targetAfter
                  hTargetDispatch) :=

            DetailedStateCorresponds.futureAfterTime
              hSourceFuture
              hTargetFuture
              hWitness

          have hFinalTargetInvariant :
              ConcreteDetailedTargetRuntimeInvariant
                messageServers
                (.afterTime
                  targetBefore
                  selectedAction
                  selectedReaction
                  targetAfter
                  hTargetDispatch) :=

            concreteDetailedTargetRuntimeInvariant_preserved
              hTargetDetailedStep
              hDetailedStates
              hSourceInvariant
              hTargetInvariant

          exact
            ⟨LF.DetailedMultiStoreLabel.timeAdvance
                targetBefore.currentTag.time
                targetAfter.currentTag.time,
             LF.DetailedMultiStoreState.afterTime
               targetBefore
               selectedAction
               selectedReaction
               targetAfter
               hTargetDispatch,
             LF.detailedTimeAdvance_is_weak
               hTargetDetailedStep,
             ConcreteDetailedLabelCorresponds.timeAdvance
               hWitness.beforeState.currentTime
               hWitness.afterState.currentTime,
             hFinalStates,
             hFinalSourceInvariant,
             hFinalTargetInvariant⟩

      | sameTimeMicrostepAhead =>
          simp [
            ConcreteDetailedTargetRuntimeInvariant
          ] at hTargetInvariant

  | consumeReady hSourceDispatch =>

      cases hStates with

      | futureAfterTime
          hSourceFuture
          hTargetFuture
          hWitness =>

          rename_i
            sourceBeforeState
            sourceAfterState
            selectedMessage
            selectedServer
            targetBeforeState
            targetAfterState
            selectedAction
            selectedReaction
            targetDispatch
            sourceDispatchWitness

          have hTargetAfterInvariant :=
            concreteDetailedTargetRuntimeInvariant_afterTime.mp
              hTargetInvariant

          have hTargetDetailedStep :
              LF.DetailedMultiStoreStep
                declaredVariables
                (Translation.compileLogicalActions
                  messageServers)
                (Translation.compileMessageReactions
                  messageServers)
                (.afterTime
                  targetBeforeState
                  selectedAction
                  selectedReaction
                  targetAfterState
                  targetDispatch)
                (.consume
                  selectedAction
                  selectedReaction)
                (.stable
                  targetAfterState) :=

            LF.DetailedMultiStoreStep.consumeAfterTimeZero
              targetDispatch
              hTargetAfterInvariant.currentMicrostepZero

          have hFinalTargetInvariant :
              ConcreteDetailedTargetRuntimeInvariant
                messageServers
                (.stable
                  targetAfterState) :=

            concreteDetailedTargetRuntimeInvariant_stable.mpr
              hTargetAfterInvariant

          exact
            ⟨LF.DetailedMultiStoreLabel.consume
                selectedAction
                selectedReaction,
             LF.DetailedMultiStoreState.stable
               targetAfterState,
             LF.detailedConsume_is_weak
               hTargetDetailedStep,
             ConcreteDetailedLabelCorresponds.consume
               hWitness.selectedOccurrence
               hWitness.selectedHandler,
             DetailedStateCorresponds.stable
               hWitness.afterState,
             hFinalSourceInvariant,
             hFinalTargetInvariant⟩

      | futureReady =>
          simp [
            ConcreteDetailedTargetRuntimeInvariant
          ] at hTargetInvariant

  | consumeNow
      hSourceDispatch
      hSourceSameTime =>

      cases hStates with

      | stable hStable =>

          rename_i
            sourceBefore
            sourceAfter
            selectedMessage
            selectedServer
            targetBefore

          have hDetailedStates :
              ConcreteDetailedStateCorresponds
                messageServers
                (.stable _)
                (.stable _) :=

            DetailedStateCorresponds.stable
              hStable

          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          have hCompatible :
              StoreForwardDispatchCompatible
                _
                _
                _ :=

            storeForwardDispatchCompatible_of_priorityRuntimeInvariant
              hSourceDispatch
              hStable
              hTargetStable

          rcases
              concreteDetailed_dispatch_forward_of_compatible
                hSourceDispatch
                hDetailedStates
                hCompatible
            with
              ⟨selectedAction,
               selectedReaction,
               targetAfter,
               hTargetDispatch,
               hWitness⟩

          have hTargetSameTime :
              targetBefore.currentTag.time =
                targetAfter.currentTag.time := by

            calc
              targetBefore.currentTag.time =
                  _ :=
                hWitness.beforeState.currentTime

              _ =
                  _ :=
                hSourceSameTime

              _ =
                  targetAfter.currentTag.time :=
                hWitness.afterState.currentTime.symm

          have hTargetAfterMicrostepZero :
              targetAfter.currentTag.microstep =
                0 :=

            targetMultiStoreMachineStep_preserves_currentMicrostepZero
              (LF.MultiStoreMachineStep.dispatch
                (declaredVariables :=
                  declaredVariables)
                (logicalActions :=
                  Translation.compileLogicalActions
                    messageServers)
                hTargetDispatch)
              hTargetStable.currentMicrostepZero
              hTargetStable.pendingMicrostepsZero

          have hTargetSameMicrostep :
              targetBefore.currentTag.microstep =
                targetAfter.currentTag.microstep := by

            rw [
              hTargetStable.currentMicrostepZero,
              hTargetAfterMicrostepZero
            ]

          have hTargetDetailedStep :
              LF.DetailedMultiStoreStep
                declaredVariables
                (Translation.compileLogicalActions
                  messageServers)
                (Translation.compileMessageReactions
                  messageServers)
                (.stable targetBefore)
                (.consume
                  selectedAction
                  selectedReaction)
                (.stable targetAfter) :=

            LF.DetailedMultiStoreStep.consumeNow
              hTargetDispatch
              hTargetSameTime
              hTargetSameMicrostep

          have hFinalTargetInvariant :
              ConcreteDetailedTargetRuntimeInvariant
                messageServers
                (.stable targetAfter) :=

            concreteDetailedTargetRuntimeInvariant_preserved
              hTargetDetailedStep
              hDetailedStates
              hSourceInvariant
              hTargetInvariant

          exact
            ⟨LF.DetailedMultiStoreLabel.consume
                selectedAction
                selectedReaction,
             LF.DetailedMultiStoreState.stable
               targetAfter,
             LF.detailedConsume_is_weak
               hTargetDetailedStep,
             ConcreteDetailedLabelCorresponds.consume
               hWitness.selectedOccurrence
               hWitness.selectedHandler,
             DetailedStateCorresponds.stable
               hWitness.afterState,
             hFinalSourceInvariant,
             hFinalTargetInvariant⟩

      | sameTimeMicrostepAhead =>
          simp [
            ConcreteDetailedTargetRuntimeInvariant
          ] at hTargetInvariant

end Correctness
end Relico
