import Relico.Correctness.DetailedInvariantMatches

set_option autoImplicit false

namespace Relico
namespace Correctness

theorem concreteDetailedTargetRuntimeInvariant_preserved
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore :
      DTR.DetailedMultiStoreState
        messageServers}
    {targetBefore targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    {targetLabel :
      LF.DetailedMultiStoreLabel}
    (hTargetStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        targetLabel
        targetAfter)
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
        targetBefore) :
    ConcreteDetailedTargetRuntimeInvariant
      messageServers
      targetAfter := by

  cases hTargetStep with

  | statement hStatement =>
      cases hStates with

      | stable hStable =>
          have hSourceStable :=
            concreteDetailedSourceRuntimeInvariant_stable.mp
              hSourceInvariant

          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          apply
            concreteDetailedTargetRuntimeInvariant_stable.mpr

          exact
            targetMultiStoreMachineStep_preserves_priorityRuntimeInvariant
              (LF.MultiStoreMachineStep.statement
                (messageReactions :=
                  Translation.compileMessageReactions
                    messageServers)
                hStatement)
              hStable
              hSourceStable.2
              hTargetStable

  | timeAdvance
      hTargetDispatch
      hTargetFuture =>

      cases hStates with

      | stable hStable =>
          have hSourceStable :=
            concreteDetailedSourceRuntimeInvariant_stable.mp
              hSourceInvariant

          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          apply
            concreteDetailedTargetRuntimeInvariant_afterTime.mpr

          exact
            targetMultiStoreMachineStep_preserves_priorityRuntimeInvariant
              (LF.MultiStoreMachineStep.dispatch
                (declaredVariables :=
                  declaredVariables)
                (logicalActions :=
                  Translation.compileLogicalActions
                    messageServers)
                hTargetDispatch)
              hStable
              hSourceStable.2
              hTargetStable

  | microstepAfterTime
      hTargetDispatch
      hPositiveMicrostep =>

      have hAfterInvariant :=
        concreteDetailedTargetRuntimeInvariant_afterTime.mp
          hTargetInvariant

      have hImpossible : False := by
        have hPositive :=
          hPositiveMicrostep

        rw [
          hAfterInvariant.currentMicrostepZero
        ] at hPositive

        exact
          (Nat.lt_irrefl 0)
            hPositive

      exact
        hImpossible.elim

  | consumeAfterTimeZero
      hTargetDispatch
      hZeroMicrostep =>

      simpa [
        ConcreteDetailedTargetRuntimeInvariant
      ] using
        hTargetInvariant

  | microstepSameTime
      hTargetDispatch
      hTargetSameTime
      hLaterMicrostep =>

      cases hStates with

      | stable hStable =>
          have hSourceStable :=
            concreteDetailedSourceRuntimeInvariant_stable.mp
              hSourceInvariant

          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          have hAfterInvariant :
              LF.StoreState.PriorityRuntimeInvariant
                _ :=

            targetMultiStoreMachineStep_preserves_priorityRuntimeInvariant
              (LF.MultiStoreMachineStep.dispatch
                (declaredVariables :=
                  declaredVariables)
                (logicalActions :=
                  Translation.compileLogicalActions
                    messageServers)
                hTargetDispatch)
              hStable
              hSourceStable.2
              hTargetStable

          have hImpossible : False := by
            have hLater :=
              hLaterMicrostep

            rw [
              hTargetStable.currentMicrostepZero,
              hAfterInvariant.currentMicrostepZero
            ] at hLater

            exact
              (Nat.lt_irrefl 0)
                hLater

          exact
            hImpossible.elim

  | consumeReady hTargetDispatch =>
      simp [
        ConcreteDetailedTargetRuntimeInvariant
      ] at hTargetInvariant

  | consumeNow
      hTargetDispatch
      hTargetSameTime
      hTargetSameMicrostep =>

      cases hStates with

      | stable hStable =>
          have hSourceStable :=
            concreteDetailedSourceRuntimeInvariant_stable.mp
              hSourceInvariant

          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          apply
            concreteDetailedTargetRuntimeInvariant_stable.mpr

          exact
            targetMultiStoreMachineStep_preserves_priorityRuntimeInvariant
              (LF.MultiStoreMachineStep.dispatch
                (declaredVariables :=
                  declaredVariables)
                (logicalActions :=
                  Translation.compileLogicalActions
                    messageServers)
                hTargetDispatch)
              hStable
              hSourceStable.2
              hTargetStable

theorem concreteDetailedSourceRuntimeInvariant_tauSteps
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers}
    (hSteps :
      DTR.DetailedTauSteps
        declaredVariables
        messageServers
        sourceBefore
        sourceAfter)
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
            messageServer.body)
    (hBefore :
      ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceBefore) :
    ConcreteDetailedSourceRuntimeInvariant
      declaredVariables
      messageServers
      sourceAfter := by

  induction hSteps with

  | refl state =>
      exact hBefore

  | cons
      hHeadStep
      hHeadTau
      hRemainingSteps
      hInduction =>

      apply hInduction

      exact
        concreteDetailedSourceRuntimeInvariant_preserved
          hHeadStep
          hMessageBodiesWellFormed
          hMessageBodiesTiming
          hBefore

theorem concreteDetailedSourceRuntimeInvariant_weakStep
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers}
    {sourceLabel :
      DTR.DetailedMultiStoreLabel}
    (hWeakStep :
      DTR.DetailedWeakStep
        declaredVariables
        messageServers
        sourceBefore
        sourceLabel
        sourceAfter)
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
            messageServer.body)
    (hBefore :
      ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceBefore) :
    ConcreteDetailedSourceRuntimeInvariant
      declaredVariables
      messageServers
      sourceAfter := by

  cases hWeakStep with

  | tau hTau hSteps =>
      exact
        concreteDetailedSourceRuntimeInvariant_tauSteps
          hSteps
          hMessageBodiesWellFormed
          hMessageBodiesTiming
          hBefore

  | visible
      hVisible
      hPrefix
      hVisibleStep
      hSuffix =>

      have hBeforeVisible :
          ConcreteDetailedSourceRuntimeInvariant
            declaredVariables
            messageServers
            _ :=

        concreteDetailedSourceRuntimeInvariant_tauSteps
          hPrefix
          hMessageBodiesWellFormed
          hMessageBodiesTiming
          hBefore

      have hAfterVisible :
          ConcreteDetailedSourceRuntimeInvariant
            declaredVariables
            messageServers
            _ :=

        concreteDetailedSourceRuntimeInvariant_preserved
          hVisibleStep
          hMessageBodiesWellFormed
          hMessageBodiesTiming
          hBeforeVisible

      exact
        concreteDetailedSourceRuntimeInvariant_tauSteps
          hSuffix
          hMessageBodiesWellFormed
          hMessageBodiesTiming
          hAfterVisible

def ConcreteDetailedBackwardInvariantMatch
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (targetLabel : LF.DetailedMultiStoreLabel)
    (targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers))
    (sourceBefore :
      DTR.DetailedMultiStoreState
        messageServers) :
    Prop :=

  ∃ sourceLabel : DTR.DetailedMultiStoreLabel,
    ∃ sourceAfter :
        DTR.DetailedMultiStoreState
          messageServers,

      DTR.DetailedWeakStep
          declaredVariables
          messageServers
          sourceBefore
          sourceLabel
          sourceAfter ∧

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

theorem concreteDetailedBackwardInvariantMatch
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore :
      DTR.DetailedMultiStoreState
        messageServers}
    {targetBefore targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    {targetLabel :
      LF.DetailedMultiStoreLabel}
    (hTargetStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        targetLabel
        targetAfter)
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
    ConcreteDetailedBackwardInvariantMatch
      declaredVariables
      messageServers
      targetLabel
      targetAfter
      sourceBefore := by

  rcases
      concreteDetailedBackwardMatch_of_runtimeInvariants
        hTargetStep
        hStates
        hSourceInvariant
        hTargetInvariant
    with
      ⟨sourceLabel,
       sourceAfter,
       hSourceWeakStep,
       hLabels,
       hFinalStates⟩

  have hFinalSourceInvariant :
      ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceAfter :=

    concreteDetailedSourceRuntimeInvariant_weakStep
      hSourceWeakStep
      hMessageBodiesWellFormed
      hMessageBodiesTiming
      hSourceInvariant

  have hFinalTargetInvariant :
      ConcreteDetailedTargetRuntimeInvariant
        messageServers
        targetAfter :=

    concreteDetailedTargetRuntimeInvariant_preserved
      hTargetStep
      hStates
      hSourceInvariant
      hTargetInvariant

  exact
    ⟨sourceLabel,
     sourceAfter,
     hSourceWeakStep,
     hLabels,
     hFinalStates,
     hFinalSourceInvariant,
     hFinalTargetInvariant⟩

end Correctness
end Relico
