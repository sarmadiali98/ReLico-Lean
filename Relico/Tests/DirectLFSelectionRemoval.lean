import Relico.Correctness.DirectLFSelectionRemoval

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFSelectionRemoval

/--
Source removal preserves the approved direct-LF selection compatibility
condition and removes one corresponding target occurrence.
-/
theorem source_removal_preserves
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hCompatible :
      Correctness.DirectLFSelectionCompatible
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
        Correctness.DirectLFSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=
  Correctness.DirectLFSelectionCompatible.remove_source
    hCompatible
    hRemove

/--
Target removal preserves the approved direct-LF selection compatibility
condition and removes one corresponding source occurrence.
-/
theorem target_removal_preserves
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hCompatible :
      Correctness.DirectLFSelectionCompatible
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
        Correctness.DirectLFSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining :=
  Correctness.DirectLFSelectionCompatible.remove_target
    hCompatible
    hRemove

/--
Selection compatibility is independent of the concrete source-list order.
-/
theorem source_permutation_preserves
    {messageServers :
      List DTR.MessageServer}
    {sourceLeft sourceRight :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    (hPermutation :
      sourceLeft.Perm sourceRight)
    (hCompatible :
      Correctness.DirectLFSelectionCompatible
        messageServers
        sourceRight
        targetQueue) :
    Correctness.DirectLFSelectionCompatible
      messageServers
      sourceLeft
      targetQueue :=
  Correctness.DirectLFSelectionCompatible.perm_source
    hPermutation
    hCompatible

/--
Selection compatibility is independent of the concrete target-list order.
-/
theorem target_permutation_preserves
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetLeft targetRight :
      LF.ActionQueue}
    (hPermutation :
      targetLeft.Perm targetRight)
    (hCompatible :
      Correctness.DirectLFSelectionCompatible
        messageServers
        sourceQueue
        targetRight) :
    Correctness.DirectLFSelectionCompatible
      messageServers
      sourceQueue
      targetLeft :=
  Correctness.DirectLFSelectionCompatible.perm_target
    hPermutation
    hCompatible

#check Correctness.DirectLFSelectionCompatible.perm_source
#check Correctness.DirectLFSelectionCompatible.perm_target

#check Correctness.directLFAlignedRemoval_of_source
#check Correctness.directLFAlignedRemoval_of_target

#check Correctness.DirectLFOrderedSelectionCompatible.remove_source
#check Correctness.DirectLFOrderedSelectionCompatible.remove_target

#check Correctness.DirectLFSelectionCompatible.remove_source
#check Correctness.DirectLFSelectionCompatible.remove_target

#check source_removal_preserves
#check target_removal_preserves
#check source_permutation_preserves
#check target_permutation_preserves

end DirectLFSelectionRemoval
end Tests
end Relico
