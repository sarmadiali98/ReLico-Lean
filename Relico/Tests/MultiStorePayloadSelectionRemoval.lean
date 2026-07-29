import Relico.Correctness.MultiStorePayloadDispatchSelection

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadSelectionRemoval

theorem base_source_removal_preserves
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hCompatible :
      Correctness.MultiStorePayloadBaseSelectionCompatible
        messageServers
        sourceQueue
        targetQueue)
    (hRemove :
      Occurrence.RemovesOne
        selectedMessage
        sourceQueue
        sourceRemaining) :
    ∃ selectedAction targetRemaining,
      Occurrence.RemovesOne
          selectedAction
          targetQueue
          targetRemaining ∧
        Correctness.PendingCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.MultiStorePayloadBaseSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=

  Correctness.MultiStorePayloadBaseSelectionCompatible.remove_source
    hCompatible
    hRemove

theorem base_target_removal_preserves
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hCompatible :
      Correctness.MultiStorePayloadBaseSelectionCompatible
        messageServers
        sourceQueue
        targetQueue)
    (hRemove :
      Occurrence.RemovesOne
        selectedAction
        targetQueue
        targetRemaining) :
    ∃ selectedMessage sourceRemaining,
      Occurrence.RemovesOne
          selectedMessage
          sourceQueue
          sourceRemaining ∧
        Correctness.PendingCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.MultiStorePayloadBaseSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=

  Correctness.MultiStorePayloadBaseSelectionCompatible.remove_target
    hCompatible
    hRemove

theorem payload_source_removal_preserves
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBag sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue)
    (hRemove :
      Occurrence.RemovesOne
        selectedMessage
        sourceBag
        sourceRemaining) :
    ∃ selectedAction targetRemaining,
      Occurrence.RemovesOne
          selectedAction
          targetQueue
          targetRemaining ∧
        Correctness.PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.MultiStorePayloadSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=

  Correctness.MultiStorePayloadSelectionCompatible.remove_source
    hCompatible
    hRemove

theorem payload_target_removal_preserves
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBag :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue)
    (hRemove :
      Occurrence.RemovesOne
        selectedAction
        targetQueue
        targetRemaining) :
    ∃ selectedMessage sourceRemaining,
      Occurrence.RemovesOne
          selectedMessage
          sourceBag
          sourceRemaining ∧
        Correctness.PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.MultiStorePayloadSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=

  Correctness.MultiStorePayloadSelectionCompatible.remove_target
    hCompatible
    hRemove

theorem source_selection_packages_removal_and_eligibility
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBag sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceSelected :
      DTR.PendingMessage}
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue)
    (hRemoved :
      Occurrence.RemovesOne
        sourceSelected
        sourceBag
        sourceRemaining)
    (hEligible :
      DTR.MultiStorePayloadIsPriorityEligible
        messageServers
        sourceSelected
        sourceBag) :
    ∃ targetSelected targetRemaining,
      Occurrence.RemovesOne
          targetSelected
          targetQueue
          targetRemaining ∧
        Correctness.PendingPayloadCorresponds
          sourceSelected
          targetSelected ∧
        LF.MultiStorePayloadIsReactionPriorityEligible
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetSelected
          targetQueue ∧
        Correctness.MultiStorePayloadSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=

  Correctness.multiStorePayload_sourceDispatchSelection
    hCompatible
    hRemoved
    hEligible

theorem target_selection_packages_removal_and_eligibility
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBag :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {targetSelected :
      LF.PendingAction}
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue)
    (hRemoved :
      Occurrence.RemovesOne
        targetSelected
        targetQueue
        targetRemaining)
    (hEligible :
      LF.MultiStorePayloadIsReactionPriorityEligible
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetSelected
        targetQueue) :
    ∃ sourceSelected sourceRemaining,
      Occurrence.RemovesOne
          sourceSelected
          sourceBag
          sourceRemaining ∧
        Correctness.PendingPayloadCorresponds
          sourceSelected
          targetSelected ∧
        DTR.MultiStorePayloadIsPriorityEligible
          messageServers
          sourceSelected
          sourceBag ∧
        Correctness.MultiStorePayloadSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=

  Correctness.multiStorePayload_targetDispatchSelection
    hCompatible
    hRemoved
    hEligible

theorem duplicate_source_removal_leaves_one_occurrence
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    {sourceMessage :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        [sourceMessage, sourceMessage]
        [targetAction, targetAction]) :
    ∃ selectedAction targetRemaining,
      Occurrence.RemovesOne
          selectedAction
          [targetAction, targetAction]
          targetRemaining ∧
        Correctness.PendingPayloadCorresponds
          sourceMessage
          selectedAction ∧
        Correctness.MultiStorePayloadSelectionCompatible
          messageServers
          [sourceMessage]
          targetRemaining := by

  exact
    Correctness.MultiStorePayloadSelectionCompatible.remove_source
      hCompatible
      (Occurrence.RemovesOne.head
        [sourceMessage])

theorem duplicate_target_removal_leaves_one_occurrence
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    {sourceMessage :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hCompatible :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        [sourceMessage, sourceMessage]
        [targetAction, targetAction]) :
    ∃ selectedMessage sourceRemaining,
      Occurrence.RemovesOne
          selectedMessage
          [sourceMessage, sourceMessage]
          sourceRemaining ∧
        Correctness.PendingPayloadCorresponds
          selectedMessage
          targetAction ∧
        Correctness.MultiStorePayloadSelectionCompatible
          messageServers
          sourceRemaining
          [targetAction] := by

  exact
    Correctness.MultiStorePayloadSelectionCompatible.remove_target
      hCompatible
      (Occurrence.RemovesOne.head
        [targetAction])

end MultiStorePayloadSelectionRemoval
end Tests
end Relico
