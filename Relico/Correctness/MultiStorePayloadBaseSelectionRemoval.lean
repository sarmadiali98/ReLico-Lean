/-
Copyright (c) 2026.

Preservation of direct DTR-to-LF selection compatibility under
single-occurrence dispatch removal.

The proofs operate on ordinary DTR pending-message bags and LF action queues.
They distinguish repeated equal values through occurrence derivations and do
not introduce source-side microsteps or operational annotations.
-/

import Relico.Correctness.MultiStorePayloadBaseSelectionCompatibility

set_option autoImplicit false

namespace Relico
namespace Correctness
/--
Changing only the concrete source-list representation preserves selection
compatibility.
-/
theorem MultiStorePayloadBaseSelectionCompatible.perm_source
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    (hSourcePermutation :
      sourceLeft.Perm sourceRight)
    (hCompatible :
      MultiStorePayloadBaseSelectionCompatible
        messageServers
        sourceRight
        targetQueue) :
    MultiStorePayloadBaseSelectionCompatible
      messageServers
      sourceLeft
      targetQueue := by

  rcases hCompatible with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourceRepresentative,
     hTargetRepresentative,
     hOrdered⟩

  exact
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation.trans
       hSourceRepresentative,
     hTargetRepresentative,
     hOrdered⟩

/--
Changing only the concrete target-list representation preserves selection
compatibility.
-/
theorem MultiStorePayloadBaseSelectionCompatible.perm_target
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetLeft targetRight :
      LF.ActionQueue}
    (hTargetPermutation :
      targetLeft.Perm targetRight)
    (hCompatible :
      MultiStorePayloadBaseSelectionCompatible
        messageServers
        sourceQueue
        targetRight) :
    MultiStorePayloadBaseSelectionCompatible
      messageServers
      sourceQueue
      targetLeft := by

  rcases hCompatible with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourceRepresentative,
     hTargetRepresentative,
     hOrdered⟩

  exact
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourceRepresentative,
     hTargetPermutation.trans
       hTargetRepresentative,
     hOrdered⟩

/--
Simultaneously remove the target occurrence aligned with one selected source
occurrence in an ordered corresponding pair.

Every alignment remaining after removal embeds into the original alignment.
This embedding is what preserves the pairwise compatibility property in the
presence of duplicate values.
-/
theorem multiStorePayloadBaseAlignedRemoval_of_source
    {sourceQueue sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hQueues :
      QueueCorresponds
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
        PendingCorresponds
          selectedMessage
          selectedAction ∧
        QueueCorresponds
          sourceRemaining
          targetRemaining ∧
        (
          ∀
            {sourceMessage :
              DTR.PendingMessage}
            {targetAction :
              LF.PendingAction},
            MultiStorePayloadBaseAlignedOccurrence
                sourceMessage
                targetAction
                sourceRemaining
                targetRemaining →
              MultiStorePayloadBaseAlignedOccurrence
                sourceMessage
                targetAction
                sourceQueue
                targetQueue
        ) := by

  induction hRemove generalizing targetQueue with

  | head remaining =>
      cases hQueues with

      | cons hSelectedCorresponds hRemainingQueues =>
          refine
            ⟨_,
             _,
             Occurrence.RemovesOne.head _,
             hSelectedCorresponds,
             hRemainingQueues,
             ?_⟩

          intro
            sourceMessage
            targetAction
            hAligned

          exact
            MultiStorePayloadBaseAlignedOccurrence.tail
              hSelectedCorresponds
              hAligned

  | tail sourceHead hTailRemove inductionHypothesis =>
      cases hQueues with

      | cons hHeadCorresponds hTailQueues =>
          obtain
            ⟨selectedAction,
             targetTailRemaining,
             hTargetTailRemove,
             hSelectedCorresponds,
             hRemainingQueues,
             hEmbedding⟩ :=
              inductionHypothesis
                hTailQueues

          refine
            ⟨selectedAction,
             _ :: targetTailRemaining,
             Occurrence.RemovesOne.tail
               _
               hTargetTailRemove,
             hSelectedCorresponds,
             QueueCorresponds.cons
               hHeadCorresponds
               hRemainingQueues,
             ?_⟩

          intro
            sourceMessage
            targetAction
            hAligned

          cases hAligned with

          | head _hResidualHead =>
              exact
                MultiStorePayloadBaseAlignedOccurrence.head
                  hHeadCorresponds

          | tail _hResidualHead hAlignedTail =>
              exact
                MultiStorePayloadBaseAlignedOccurrence.tail
                  hHeadCorresponds
                  (hEmbedding
                    hAlignedTail)

/--
Symmetric ordered removal starting from one selected target occurrence.
-/
theorem multiStorePayloadBaseAlignedRemoval_of_target
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hQueues :
      QueueCorresponds
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
        PendingCorresponds
          selectedMessage
          selectedAction ∧
        QueueCorresponds
          sourceRemaining
          targetRemaining ∧
        (
          ∀
            {sourceMessage :
              DTR.PendingMessage}
            {targetAction :
              LF.PendingAction},
            MultiStorePayloadBaseAlignedOccurrence
                sourceMessage
                targetAction
                sourceRemaining
                targetRemaining →
              MultiStorePayloadBaseAlignedOccurrence
                sourceMessage
                targetAction
                sourceQueue
                targetQueue
        ) := by

  induction hRemove generalizing sourceQueue with

  | head remaining =>
      cases hQueues with

      | cons hSelectedCorresponds hRemainingQueues =>
          refine
            ⟨_,
             _,
             Occurrence.RemovesOne.head _,
             hSelectedCorresponds,
             hRemainingQueues,
             ?_⟩

          intro
            sourceMessage
            targetAction
            hAligned

          exact
            MultiStorePayloadBaseAlignedOccurrence.tail
              hSelectedCorresponds
              hAligned

  | tail targetHead hTailRemove inductionHypothesis =>
      cases hQueues with

      | cons hHeadCorresponds hTailQueues =>
          obtain
            ⟨selectedMessage,
             sourceTailRemaining,
             hSourceTailRemove,
             hSelectedCorresponds,
             hRemainingQueues,
             hEmbedding⟩ :=
              inductionHypothesis
                hTailQueues

          refine
            ⟨selectedMessage,
             _ :: sourceTailRemaining,
             Occurrence.RemovesOne.tail
               _
               hSourceTailRemove,
             hSelectedCorresponds,
             QueueCorresponds.cons
               hHeadCorresponds
               hRemainingQueues,
             ?_⟩

          intro
            sourceMessage
            targetAction
            hAligned

          cases hAligned with

          | head _hResidualHead =>
              exact
                MultiStorePayloadBaseAlignedOccurrence.head
                  hHeadCorresponds

          | tail _hResidualHead hAlignedTail =>
              exact
                MultiStorePayloadBaseAlignedOccurrence.tail
                  hHeadCorresponds
                  (hEmbedding
                    hAlignedTail)

/--
Removing one aligned source occurrence preserves ordered selection
compatibility.
-/
theorem MultiStorePayloadBaseOrderedSelectionCompatible.remove_source
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hCompatible :
      MultiStorePayloadBaseOrderedSelectionCompatible
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
        PendingCorresponds
          selectedMessage
          selectedAction ∧
        MultiStorePayloadBaseOrderedSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  obtain
    ⟨selectedAction,
     targetRemaining,
     hTargetRemove,
     hSelectedCorresponds,
     hRemainingQueues,
     hEmbedding⟩ :=
      multiStorePayloadBaseAlignedRemoval_of_source
        hCompatible.queues
        hRemove

  refine
    ⟨selectedAction,
     targetRemaining,
     hTargetRemove,
     hSelectedCorresponds,
     ?_⟩

  refine
    {
      queues :=
        hRemainingQueues
      pairwise := ?_
    }

  intro
    sourceLeft
    sourceRight
    targetLeft
    targetRight
    hLeft
    hRight

  exact
    hCompatible.pairwise
      (hEmbedding hLeft)
      (hEmbedding hRight)

/--
Removing one aligned target occurrence preserves ordered selection
compatibility.
-/
theorem MultiStorePayloadBaseOrderedSelectionCompatible.remove_target
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hCompatible :
      MultiStorePayloadBaseOrderedSelectionCompatible
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
        PendingCorresponds
          selectedMessage
          selectedAction ∧
        MultiStorePayloadBaseOrderedSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  obtain
    ⟨selectedMessage,
     sourceRemaining,
     hSourceRemove,
     hSelectedCorresponds,
     hRemainingQueues,
     hEmbedding⟩ :=
      multiStorePayloadBaseAlignedRemoval_of_target
        hCompatible.queues
        hRemove

  refine
    ⟨selectedMessage,
     sourceRemaining,
     hSourceRemove,
     hSelectedCorresponds,
     ?_⟩

  refine
    {
      queues :=
        hRemainingQueues
      pairwise := ?_
    }

  intro
    sourceLeft
    sourceRight
    targetLeft
    targetRight
    hLeft
    hRight

  exact
    hCompatible.pairwise
      (hEmbedding hLeft)
      (hEmbedding hRight)

/--
Removing one source occurrence from arbitrary concrete list representations
removes exactly one aligned target occurrence and preserves the approved
selection-compatibility invariant.
-/
theorem MultiStorePayloadBaseSelectionCompatible.remove_source
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hCompatible :
      MultiStorePayloadBaseSelectionCompatible
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
        PendingCorresponds
          selectedMessage
          selectedAction ∧
        MultiStorePayloadBaseSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  rcases hCompatible with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered⟩

  obtain
    ⟨sourceRepresentativeAfter,
     hSourceRepresentativeRemove,
     hSourceAfterPermutation⟩ :=
      directLF_transport_removesOne
        hSourcePermutation
        hRemove

  obtain
    ⟨selectedAction,
     targetRepresentativeAfter,
     hTargetRepresentativeRemove,
     hSelectedCorresponds,
     hOrderedAfter⟩ :=
      MultiStorePayloadBaseOrderedSelectionCompatible.remove_source
        hOrdered
        hSourceRepresentativeRemove

  obtain
    ⟨targetAfter,
     hTargetRemove,
     hTargetRepresentativeAfterPermutation⟩ :=
      directLF_transport_removesOne
        (List.Perm.symm
          hTargetPermutation)
        hTargetRepresentativeRemove

  refine
    ⟨selectedAction,
     targetAfter,
     hTargetRemove,
     hSelectedCorresponds,
     ?_⟩

  exact
    ⟨sourceRepresentativeAfter,
     targetRepresentativeAfter,
     hSourceAfterPermutation,
     List.Perm.symm
       hTargetRepresentativeAfterPermutation,
     hOrderedAfter⟩

/--
Symmetric one-occurrence target removal for arbitrary concrete list
representations.
-/
theorem MultiStorePayloadBaseSelectionCompatible.remove_target
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hCompatible :
      MultiStorePayloadBaseSelectionCompatible
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
        PendingCorresponds
          selectedMessage
          selectedAction ∧
        MultiStorePayloadBaseSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  rcases hCompatible with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered⟩

  obtain
    ⟨targetRepresentativeAfter,
     hTargetRepresentativeRemove,
     hTargetAfterPermutation⟩ :=
      directLF_transport_removesOne
        hTargetPermutation
        hRemove

  obtain
    ⟨selectedMessage,
     sourceRepresentativeAfter,
     hSourceRepresentativeRemove,
     hSelectedCorresponds,
     hOrderedAfter⟩ :=
      MultiStorePayloadBaseOrderedSelectionCompatible.remove_target
        hOrdered
        hTargetRepresentativeRemove

  obtain
    ⟨sourceAfter,
     hSourceRemove,
     hSourceRepresentativeAfterPermutation⟩ :=
      directLF_transport_removesOne
        (List.Perm.symm
          hSourcePermutation)
        hSourceRepresentativeRemove

  refine
    ⟨selectedMessage,
     sourceAfter,
     hSourceRemove,
     hSelectedCorresponds,
     ?_⟩

  exact
    ⟨sourceRepresentativeAfter,
     targetRepresentativeAfter,
     List.Perm.symm
       hSourceRepresentativeAfterPermutation,
     hTargetAfterPermutation,
     hOrderedAfter⟩

end Correctness
end Relico
