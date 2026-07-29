import Relico.Correctness.DirectLFPayloadSelectionRemoval

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFPayloadSelectionRemoval

#check Correctness.directLFPayloadAlignedRemoval_of_source
#check Correctness.directLFPayloadAlignedRemoval_of_target
#check Correctness.DirectLFPayloadOrderedSelectionCompatible.remove_source
#check Correctness.DirectLFPayloadOrderedSelectionCompatible.remove_target
#check Correctness.DirectLFPayloadSelectionCompatible.remove_source
#check Correctness.DirectLFPayloadSelectionCompatible.remove_target

example
    {messageServers : List DTR.MessageServer}
    {sourceBag sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {selectedMessage : DTR.PendingMessage}
    (hCompatible :
      Correctness.DirectLFPayloadSelectionCompatible
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
        Correctness.DirectLFPayloadSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  exact
    Correctness.DirectLFPayloadSelectionCompatible.remove_source
      hCompatible
      hRemove

example
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hCompatible :
      Correctness.DirectLFPayloadSelectionCompatible
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
        Correctness.DirectLFPayloadSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  exact
    Correctness.DirectLFPayloadSelectionCompatible.remove_target
      hCompatible
      hRemove

end DirectLFPayloadSelectionRemoval
end Tests
end Relico
