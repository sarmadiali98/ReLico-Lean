import Relico.Correctness.DetailedInvariantMatches

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedInvariantMatches

theorem forward_runtime_match_regression
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
    (hTargetInvariant :
      Correctness.ConcreteDetailedTargetRuntimeInvariant
        messageServers
        targetBefore) :
    Correctness.ConcreteDetailedForwardMatch
      declaredVariables
      messageServers
      sourceLabel
      sourceAfter
      targetBefore := by

  exact
    Correctness.concreteDetailedForwardMatch_of_runtimeInvariants
      hSourceStep
      hStates
      hTargetInvariant

theorem backward_runtime_match_regression
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
    Correctness.ConcreteDetailedBackwardMatch
      declaredVariables
      messageServers
      targetLabel
      targetAfter
      sourceBefore := by

  exact
    Correctness.concreteDetailedBackwardMatch_of_runtimeInvariants
      hTargetStep
      hStates
      hSourceInvariant
      hTargetInvariant

end DetailedInvariantMatches
end Tests
end Relico
