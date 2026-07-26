import Relico.Correctness.DetailedPhaseWeakBisimulation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedPhaseWeakBisimulation

theorem interface_exists
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer) :
    Correctness.ConcreteDetailedPhaseWeakBisimulation
      declaredVariables
      messageServers := by

  exact
    Correctness.concreteDetailed_phaseWeakBisimulation
      declaredVariables
      messageServers

theorem forward_statement_projection
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {sourceLabel : DTR.Label}
    {targetBefore : LF.StoreState}
    (hSourceStep :
      DTR.MultiStoreStep
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    Correctness.ConcreteDetailedForwardMatch
      declaredVariables
      messageServers
      DTR.DetailedMultiStoreLabel.tau
      (.stable sourceAfter)
      (.stable targetBefore) := by

  exact
    (Correctness.concreteDetailed_phaseWeakBisimulation
      declaredVariables
      messageServers).forwardStatementMatch
        sourceBefore
        sourceAfter
        sourceLabel
        targetBefore
        hSourceStep
        hStates

theorem backward_statement_projection
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {targetLabel : LF.Label}
    (hTargetStep :
      LF.MultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hSourceBodyWellFormed :
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceBefore.activeBody) :
    Correctness.ConcreteDetailedBackwardMatch
      declaredVariables
      messageServers
      LF.DetailedMultiStoreLabel.tau
      (.stable targetAfter)
      (.stable sourceBefore) := by

  exact
    (Correctness.concreteDetailed_phaseWeakBisimulation
      declaredVariables
      messageServers).backwardStatementMatch
        sourceBefore
        targetBefore
        targetAfter
        targetLabel
        hTargetStep
        hStates
        hSourceBodyWellFormed

end DetailedPhaseWeakBisimulation
end Tests
end Relico
