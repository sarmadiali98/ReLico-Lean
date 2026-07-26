import Relico.Correctness.DetailedBackwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBackwardWeakSimulation

theorem statement_case
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
    Correctness.concreteDetailed_statement_backward_weak
      hTargetStep
      hStates
      hSourceBodyWellFormed

theorem future_time_case
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hTargetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time)
    (hStates :
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hTargetMicrostepsZero :
      LF.StoreState.PendingMicrostepsZero
        targetBefore) :
    Correctness.ConcreteDetailedBackwardMatch
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
      (.stable sourceBefore) := by

  exact
    Correctness.concreteDetailed_timeAdvance_backward_weak
      hTargetDispatch
      hTargetFuture
      hStates
      hTargetMicrostepsZero

theorem backward_match_preserves_relation
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {targetLabel : LF.DetailedMultiStoreLabel}
    {targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    {sourceBefore :
      DTR.DetailedMultiStoreState
        messageServers}
    (hMatch :
      Correctness.ConcreteDetailedBackwardMatch
        declaredVariables
        messageServers
        targetLabel
        targetAfter
        sourceBefore) :
    ∃ sourceAfter :
        DTR.DetailedMultiStoreState
          messageServers,
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        sourceAfter
        targetAfter := by

  exact
    Correctness.ConcreteDetailedBackwardMatch.source_corresponds
      hMatch

end DetailedBackwardWeakSimulation
end Tests
end Relico
