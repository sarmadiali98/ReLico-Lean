import Relico.Correctness.DetailedRuntimeInvariants

set_option autoImplicit false

namespace Relico
namespace Correctness

theorem concreteDetailedForwardPhaseCompatible_of_runtimeInvariants
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
    (hTargetInvariant :
      ConcreteDetailedTargetRuntimeInvariant
        messageServers
        targetBefore) :
    ConcreteDetailedForwardPhaseCompatible
      sourceBefore
      sourceLabel
      sourceAfter
      targetBefore := by

  cases hSourceStep with

  | statement hStatement =>
      cases hStates with

      | stable hStable =>
          simp [
            ConcreteDetailedForwardPhaseCompatible
          ]

      | sameTimeMicrostepAhead =>
          simp [
            ConcreteDetailedTargetRuntimeInvariant
          ] at hTargetInvariant

  | timeAdvance hSourceDispatch hFuture =>
      cases hStates with

      | stable hStable =>
          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          simpa [
            ConcreteDetailedForwardPhaseCompatible
          ] using
            storeForwardDispatchCompatible_of_priorityRuntimeInvariant
              hSourceDispatch
              hStable
              hTargetStable

      | sameTimeMicrostepAhead =>
          simp [
            ConcreteDetailedTargetRuntimeInvariant
          ] at hTargetInvariant

  | consumeReady hSourceDispatch =>
      cases hStates with

      | futureAfterTime =>
          simp [
            ConcreteDetailedForwardPhaseCompatible
          ]

      | futureReady =>
          simp [
            ConcreteDetailedTargetRuntimeInvariant
          ] at hTargetInvariant

  | consumeNow hSourceDispatch hSameTime =>
      cases hStates with

      | stable hStable =>
          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          simpa [
            ConcreteDetailedForwardPhaseCompatible
          ] using
            storeForwardDispatchCompatible_of_priorityRuntimeInvariant
              hSourceDispatch
              hStable
              hTargetStable

      | sameTimeMicrostepAhead =>
          simp [
            ConcreteDetailedTargetRuntimeInvariant
          ] at hTargetInvariant

theorem concreteDetailedBackwardPhaseCompatible_of_runtimeInvariants
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
    ConcreteDetailedBackwardPhaseCompatible
      (declaredVariables :=
        declaredVariables)
      sourceBefore
      targetBefore
      targetLabel
      targetAfter := by

  cases hTargetStep with

  | statement hTargetStatement =>
      cases hStates with

      | stable hStable =>
          have hSourceStable :=
            concreteDetailedSourceRuntimeInvariant_stable.mp
              hSourceInvariant

          simpa [
            ConcreteDetailedBackwardPhaseCompatible
          ] using
            hSourceStable.1.activeBody

  | timeAdvance hTargetDispatch hTargetFuture =>
      cases hStates with

      | stable hStable =>
          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          simpa [
            ConcreteDetailedBackwardPhaseCompatible
          ] using
            hTargetStable.pendingMicrostepsZero

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

      cases hStates with

      | futureAfterTime =>
          simp [
            ConcreteDetailedBackwardPhaseCompatible
          ]

  | microstepSameTime
      hTargetDispatch
      hSameTime
      hLaterMicrostep =>

      have hBeforeInvariant :=
        concreteDetailedTargetRuntimeInvariant_stable.mp
          hTargetInvariant

      have hAfterZero :
          _ =
            0 :=

        targetMultiStoreMachineStep_preserves_currentMicrostepZero
          (LF.MultiStoreMachineStep.dispatch
            (declaredVariables :=
              declaredVariables)
            (logicalActions :=
              Translation.compileLogicalActions
                messageServers)
            hTargetDispatch)
          hBeforeInvariant.currentMicrostepZero
          hBeforeInvariant.pendingMicrostepsZero

      have hImpossible : False := by
        have hLater :=
          hLaterMicrostep

        rw [
          hBeforeInvariant.currentMicrostepZero,
          hAfterZero
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
      hSameTime
      hSameMicrostep =>

      cases hStates with

      | stable hStable =>
          have hTargetStable :=
            concreteDetailedTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          simpa [
            ConcreteDetailedBackwardPhaseCompatible
          ] using
            hTargetStable.pendingMicrostepsZero

theorem concreteDetailedForwardMatch_of_runtimeInvariants
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
    (hTargetInvariant :
      ConcreteDetailedTargetRuntimeInvariant
        messageServers
        targetBefore) :
    ConcreteDetailedForwardMatch
      declaredVariables
      messageServers
      sourceLabel
      sourceAfter
      targetBefore := by

  exact
    ConcreteDetailedPhaseWeakBisimulation.forwardStep
      (concreteDetailed_phaseWeakBisimulation
        declaredVariables
        messageServers)
      hSourceStep
      hStates
      (concreteDetailedForwardPhaseCompatible_of_runtimeInvariants
        hSourceStep
        hStates
        hTargetInvariant)

theorem concreteDetailedBackwardMatch_of_runtimeInvariants
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
    ConcreteDetailedBackwardMatch
      declaredVariables
      messageServers
      targetLabel
      targetAfter
      sourceBefore := by

  exact
    ConcreteDetailedPhaseWeakBisimulation.backwardStep
      (concreteDetailed_phaseWeakBisimulation
        declaredVariables
        messageServers)
      hTargetStep
      hStates
      (concreteDetailedBackwardPhaseCompatible_of_runtimeInvariants
        hTargetStep
        hStates
        hSourceInvariant
        hTargetInvariant)

end Correctness
end Relico
