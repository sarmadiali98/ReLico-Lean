import Relico.Correctness.DirectLFBagQueueCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFBagQueueCorrespondence

/--
The source and target collections may use different list orders while
representing the same occurrence correspondence.
-/
theorem reordered_pair
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hLeft :
      Correctness.PendingCorresponds
        sourceLeft
        targetLeft)
    (hRight :
      Correctness.PendingCorresponds
        sourceRight
        targetRight) :
    Correctness.DirectLFBagQueueCorresponds
      [sourceLeft, sourceRight]
      [targetRight, targetLeft] := by

  refine
    ⟨[sourceLeft, sourceRight],
     [targetLeft, targetRight],
     List.Perm.refl
       [sourceLeft, sourceRight],
     ?_,
     ?_⟩

  · exact
      List.Perm.swap
        targetLeft
        targetRight
        []

  · exact
      Correctness.QueueCorresponds.cons
        hLeft
        (Correctness.QueueCorresponds.cons
          hRight
          Correctness.QueueCorresponds.nil)

/--
Removing one occurrence from two equal source values removes exactly one
corresponding target occurrence and leaves the other occurrence represented.
-/
theorem duplicate_occurrence_remove_source
    {sourceMessage :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hPending :
      Correctness.PendingCorresponds
        sourceMessage
        targetAction) :
    ∃ selectedAction targetRemaining,
      Occurrence.RemovesOne
          selectedAction
          [targetAction, targetAction]
          targetRemaining ∧
        Correctness.PendingCorresponds
          sourceMessage
          selectedAction ∧
        Correctness.DirectLFBagQueueCorresponds
          [sourceMessage]
          targetRemaining := by

  have hQueues :
      Correctness.DirectLFBagQueueCorresponds
        [sourceMessage, sourceMessage]
        [targetAction, targetAction] :=
    Correctness.directLFBagQueueCorresponds_of_queueCorresponds
      (Correctness.QueueCorresponds.cons
        hPending
        (Correctness.QueueCorresponds.cons
          hPending
          Correctness.QueueCorresponds.nil))

  exact
    Correctness.DirectLFBagQueueCorresponds.remove_source
      hQueues
      (Occurrence.RemovesOne.head
        [sourceMessage])

/--
The symmetric target-removal theorem also preserves one duplicate occurrence.
-/
theorem duplicate_occurrence_remove_target
    {sourceMessage :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hPending :
      Correctness.PendingCorresponds
        sourceMessage
        targetAction) :
    ∃ selectedMessage sourceRemaining,
      Occurrence.RemovesOne
          selectedMessage
          [sourceMessage, sourceMessage]
          sourceRemaining ∧
        Correctness.PendingCorresponds
          selectedMessage
          targetAction ∧
        Correctness.DirectLFBagQueueCorresponds
          sourceRemaining
          [targetAction] := by

  have hQueues :
      Correctness.DirectLFBagQueueCorresponds
        [sourceMessage, sourceMessage]
        [targetAction, targetAction] :=
    Correctness.directLFBagQueueCorresponds_of_queueCorresponds
      (Correctness.QueueCorresponds.cons
        hPending
        (Correctness.QueueCorresponds.cons
          hPending
          Correctness.QueueCorresponds.nil))

  exact
    Correctness.DirectLFBagQueueCorresponds.remove_target
      hQueues
      (Occurrence.RemovesOne.head
        [targetAction])

#check Correctness.DirectLFBagQueueCorresponds
#check Correctness.directLFBagQueueCorresponds_nil
#check Correctness.DirectLFBagQueueCorresponds.append_one
#check Correctness.DirectLFBagQueueCorresponds.source_mem
#check Correctness.DirectLFBagQueueCorresponds.target_mem
#check Correctness.DirectLFBagQueueCorresponds.remove_source
#check Correctness.DirectLFBagQueueCorresponds.remove_target

#check reordered_pair
#check duplicate_occurrence_remove_source
#check duplicate_occurrence_remove_target

end DirectLFBagQueueCorrespondence
end Tests
end Relico
