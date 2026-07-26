import Relico.Correctness.ConcreteDetailedStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace ConcreteDetailedStateCorrespondence

theorem stable_relation_is_store_relation
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState : LF.StoreState}
    (hStates :
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        (.stable sourceState)
        (.stable targetState)) :
    Correctness.StoreStateCorresponds
      sourceState
      targetState := by

  exact
    Correctness.concreteDetailed_stable_iff.mp
      hStates

theorem statement_forward_preserves_concrete_relation
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
    ∃ targetLabel targetAfter,
      LF.MultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          targetBefore
          targetLabel
          targetAfter ∧
        Correctness.LabelCorresponds
          sourceLabel
          targetLabel ∧
        LF.DetailedMultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          (.stable targetBefore)
          .tau
          (.stable targetAfter) ∧
        Correctness.ConcreteDetailedStateCorresponds
          messageServers
          (.stable sourceAfter)
          (.stable targetAfter) := by

  exact
    Correctness.concreteDetailed_statement_forward
      hSourceStep
      hStates

theorem dispatch_forward_produces_concrete_witness
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
    ∃ selectedAction selectedReaction targetAfter,
      LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter ∧
        Correctness.ConcreteDetailedDispatchWitnessCorresponds
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          selectedReaction
          targetAfter := by

  exact
    Correctness.concreteDetailed_dispatch_forward_of_compatible
      hSourceDispatch
      hStates
      hCompatible

theorem future_microstep_preservation
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {dtrBefore dtrAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {dtrDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter}
    {lfBefore lfAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    {lfDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        lfBefore
        selectedAction
        selectedReaction
        lfAfter}
    (hDtrFuture :
      dtrBefore.currentTime <
        dtrAfter.currentTime)
    (hLfFuture :
      lfBefore.currentTag.time <
        lfAfter.currentTag.time)
    (hPositiveMicrostep :
      0 <
        lfAfter.currentTag.microstep)
    (hWitness :
      Correctness.ConcreteDetailedDispatchWitnessCorresponds
        dtrBefore
        selectedMessage
        selectedServer
        dtrAfter
        lfBefore
        selectedAction
        selectedReaction
        lfAfter) :
    Correctness.ConcreteDetailedStateCorresponds
        messageServers
        (.dispatchReady
          dtrBefore
          selectedMessage
          selectedServer
          dtrAfter
          dtrDispatch)
        (.dispatchReady
          lfBefore
          selectedAction
          selectedReaction
          lfAfter
          lfDispatch) := by

  exact
    (Correctness.concreteDetailed_future_microstep_preserves
      (declaredVariables := declaredVariables)
      hDtrFuture
      hLfFuture
      hPositiveMicrostep
      hWitness).2.2

end ConcreteDetailedStateCorrespondence
end Tests
end Relico
