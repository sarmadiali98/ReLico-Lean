import Relico.Correctness.DetailedRuntimeInvariants

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedRuntimeInvariants

theorem source_detailed_invariant_preservation_regression
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers}
    {sourceLabel :
      DTR.DetailedMultiStoreLabel}
    (hSourceStep :
      DTR.DetailedMultiStoreStep
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
    Correctness.concreteDetailedSourceRuntimeInvariant_preserved
      hSourceStep
      hMessageBodiesWellFormed
      hMessageBodiesTiming
      hBefore

theorem dispatch_ready_is_not_target_canonical
    {messageServers : List DTR.MessageServer}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter} :
    ¬ Correctness.ConcreteDetailedTargetRuntimeInvariant
        messageServers
        (.dispatchReady
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch) := by

  exact
    Correctness.concreteDetailedTargetRuntimeInvariant_dispatchReady

end DetailedRuntimeInvariants
end Tests
end Relico
