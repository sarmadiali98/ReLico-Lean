import Relico.Correctness.DetailedInvariantCarryingFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedInvariantCarryingFiniteWeakExecution

theorem forward_chosen_finite_execution_interface
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers}
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    (hSourceSteps :
      DTR.DetailedMultiStoreSteps
        declaredVariables
        messageServers
        sourceBefore
        sourceLabels
        sourceAfter)
    (hStates :
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hSourceInvariant :
      Correctness.ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceBefore)
    (hTargetInvariant :
      Correctness.ConcreteDetailedTargetRuntimeInvariant
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
    ∃ targetLabels targetAfter,
      LF.DetailedWeakSteps
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          targetLabels
          targetAfter ∧
        Correctness.ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        Correctness.ConcreteDetailedStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧
        Correctness.ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) ∧
        Correctness.ConcreteDetailedSourceRuntimeInvariant
          declaredVariables
          messageServers
          sourceAfter ∧
        Correctness.ConcreteDetailedTargetRuntimeInvariant
          messageServers
          targetAfter := by

  exact
    Correctness.concreteDetailedSteps_forward_chosen
      hSourceSteps
      hStates
      hSourceInvariant
      hTargetInvariant
      hMessageBodiesWellFormed
      hMessageBodiesTiming

theorem backward_chosen_finite_execution_interface
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore :
      DTR.DetailedMultiStoreState
        messageServers}
    {targetBefore targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    (hTargetSteps :
      LF.DetailedMultiStoreSteps
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        targetLabels
        targetAfter)
    (hStates :
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hSourceInvariant :
      Correctness.ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceBefore)
    (hTargetInvariant :
      Correctness.ConcreteDetailedTargetRuntimeInvariant
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
    ∃ sourceLabels sourceAfter,
      DTR.DetailedWeakSteps
          declaredVariables
          messageServers
          sourceBefore
          sourceLabels
          sourceAfter ∧
        Correctness.ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        Correctness.ConcreteDetailedStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧
        Correctness.ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) ∧
        Correctness.ConcreteDetailedSourceRuntimeInvariant
          declaredVariables
          messageServers
          sourceAfter ∧
        Correctness.ConcreteDetailedTargetRuntimeInvariant
          messageServers
          targetAfter := by

  exact
    Correctness.concreteDetailedSteps_backward_chosen
      hTargetSteps
      hStates
      hSourceInvariant
      hTargetInvariant
      hMessageBodiesWellFormed
      hMessageBodiesTiming

end DetailedInvariantCarryingFiniteWeakExecution
end Tests
end Relico
