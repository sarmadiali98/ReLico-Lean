import Relico.Correctness.DetailedInvariantCarryingBackwardMatch

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedInvariantCarryingBackwardMatch

theorem target_invariant_preservation_regression
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
        targetBefore) :
    Correctness.ConcreteDetailedTargetRuntimeInvariant
      messageServers
      targetAfter := by

  exact
    Correctness.concreteDetailedTargetRuntimeInvariant_preserved
      hTargetStep
      hStates
      hSourceInvariant
      hTargetInvariant

theorem source_weak_invariant_preservation_regression
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
      Correctness.ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceBefore) :
    Correctness.ConcreteDetailedSourceRuntimeInvariant
      declaredVariables
      messageServers
      sourceAfter := by

  exact
    Correctness.concreteDetailedSourceRuntimeInvariant_weakStep
      hWeakStep
      hMessageBodiesWellFormed
      hMessageBodiesTiming
      hBefore

theorem backward_invariant_match_regression
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
    Correctness.ConcreteDetailedBackwardInvariantMatch
      declaredVariables
      messageServers
      targetLabel
      targetAfter
      sourceBefore := by

  exact
    Correctness.concreteDetailedBackwardInvariantMatch
      hTargetStep
      hStates
      hSourceInvariant
      hTargetInvariant
      hMessageBodiesWellFormed
      hMessageBodiesTiming

end DetailedInvariantCarryingBackwardMatch
end Tests
end Relico
