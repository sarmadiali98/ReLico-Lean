import Relico.Correctness.MultiStorePayloadRuntimeDispatchSupport

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadRuntimeDispatchSupport

universe u

theorem duplicate_same_value_removals_are_permutations
    {α : Type u}
    (selected other : α) :
    [other, selected].Perm
      [selected, other] := by

  exact
    Correctness.removesOne_same_selected_remaining_perm
      (Occurrence.RemovesOne.head
        [other, selected])
      (Occurrence.RemovesOne.tail
        selected
        (Occurrence.RemovesOne.tail
          other
          (Occurrence.RemovesOne.head [])))

theorem same_target_determines_source_value
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hLeft :
      Correctness.PendingPayloadCorresponds
        sourceLeft
        targetAction)
    (hRight :
      Correctness.PendingPayloadCorresponds
        sourceRight
        targetAction) :
    sourceLeft =
      sourceRight :=

  Correctness.pendingPayloadCorresponds_source_eq_of_sameTarget
    hLeft
    hRight

theorem same_source_and_tag_determine_target_value
    {sourceMessage :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hLeft :
      Correctness.PendingPayloadCorresponds
        sourceMessage
        targetLeft)
    (hRight :
      Correctness.PendingPayloadCorresponds
        sourceMessage
        targetRight)
    (hTag :
      targetLeft.tag =
        targetRight.tag) :
    targetLeft =
      targetRight :=

  Correctness.pendingPayloadCorresponds_target_eq_of_sameSource_and_tag
    hLeft
    hRight
    hTag

theorem forward_residual_selection_transport
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceRemaining :
      DTR.MessageBag}
    {targetQueue selectionRemaining positionalRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hSelectionRemoved :
      Occurrence.RemovesOne
        selectedAction
        targetQueue
        selectionRemaining)
    (hPositionalRemoved :
      Occurrence.RemovesOne
        selectedAction
        targetQueue
        positionalRemaining)
    (hSelectionRemaining :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        sourceRemaining
        selectionRemaining) :
    Correctness.MultiStorePayloadSelectionCompatible
      messageServers
      sourceRemaining
      positionalRemaining :=

  Correctness.multiStorePayload_forwardResidualSelectionMerge
    hSelectionRemoved
    hPositionalRemoved
    hSelectionRemaining

theorem backward_residual_selection_transport
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue selectionRemaining positionalRemaining :
      DTR.MessageBag}
    {targetRemaining :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hSelectionRemoved :
      Occurrence.RemovesOne
        selectedMessage
        sourceQueue
        selectionRemaining)
    (hPositionalRemoved :
      Occurrence.RemovesOne
        selectedMessage
        sourceQueue
        positionalRemaining)
    (hSelectionRemaining :
      Correctness.MultiStorePayloadSelectionCompatible
        messageServers
        selectionRemaining
        targetRemaining) :
    Correctness.MultiStorePayloadSelectionCompatible
      messageServers
      positionalRemaining
      targetRemaining :=

  Correctness.multiStorePayload_backwardResidualSelectionMerge
    hSelectionRemoved
    hPositionalRemoved
    hSelectionRemaining

end MultiStorePayloadRuntimeDispatchSupport
end Tests
end Relico
