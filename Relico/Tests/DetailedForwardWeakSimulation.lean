import Relico.Correctness.DetailedForwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedForwardWeakSimulation

theorem statement_case
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
    Correctness.concreteDetailed_statement_forward_weak
      hSourceStep
      hStates

theorem future_time_case
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {targetBefore : LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hStates :
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hCompatible :
      Correctness.StoreForwardDispatchCompatible
        selectedMessage
        sourceAfter.pendingMessages
        targetBefore) :
    Correctness.ConcreteDetailedForwardMatch
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
        hSourceDispatch)
      (.stable targetBefore) := by

  exact
    Correctness.concreteDetailed_timeAdvance_forward_weak
      hSourceDispatch
      hFuture
      hStates
      hCompatible

theorem forward_match_preserves_relation
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceLabel : DTR.DetailedMultiStoreLabel}
    {sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers}
    {targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    (hMatch :
      Correctness.ConcreteDetailedForwardMatch
        declaredVariables
        messageServers
        sourceLabel
        sourceAfter
        targetBefore) :
    ∃ targetAfter :
        LF.DetailedMultiStoreState
          (Translation.compileMessageReactions
            messageServers),
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        sourceAfter
        targetAfter := by

  exact
    Correctness.ConcreteDetailedForwardMatch.target_corresponds
      hMatch

end DetailedForwardWeakSimulation
end Tests
end Relico
