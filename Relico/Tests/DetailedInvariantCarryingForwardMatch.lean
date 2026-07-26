import Relico.Correctness.DetailedInvariantCarryingForwardMatch

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedInvariantCarryingForwardMatch

theorem forward_invariant_match_regression
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
    Correctness.ConcreteDetailedForwardInvariantMatch
      declaredVariables
      messageServers
      sourceLabel
      sourceAfter
      targetBefore := by

  exact
    Correctness.concreteDetailedForwardInvariantMatch
      hSourceStep
      hStates
      hSourceInvariant
      hTargetInvariant
      hMessageBodiesWellFormed
      hMessageBodiesTiming

theorem forward_invariant_match_has_corresponding_destination
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
    ∃ targetLabel targetAfter,
      LF.DetailedWeakStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          targetLabel
          targetAfter ∧
        Correctness.ConcreteDetailedLabelCorresponds
          sourceLabel
          targetLabel ∧
        Correctness.ConcreteDetailedStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧
        Correctness.ConcreteDetailedSourceRuntimeInvariant
          declaredVariables
          messageServers
          sourceAfter ∧
        Correctness.ConcreteDetailedTargetRuntimeInvariant
          messageServers
          targetAfter := by

  exact
    Correctness.concreteDetailedForwardInvariantMatch
      hSourceStep
      hStates
      hSourceInvariant
      hTargetInvariant
      hMessageBodiesWellFormed
      hMessageBodiesTiming

end DetailedInvariantCarryingForwardMatch
end Tests
end Relico
