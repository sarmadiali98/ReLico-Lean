/-
Copyright (c) 2026.

Preservation of direct DTR-to-LF selection compatibility under
single-occurrence dispatch removal.

The proofs operate on ordinary DTR pending-message bags and LF action queues.
They distinguish repeated equal values through occurrence derivations and do
not introduce source-side microsteps or operational annotations.
-/

import Relico.Correctness.DirectLFSelectionCompatibility

set_option autoImplicit false

namespace Relico
namespace Correctness
/--
Changing only the concrete source-list representation preserves selection
compatibility.
-/
theorem DirectLFSelectionCompatible.perm_source
    {messageServers :
      List DTR.MessageServer}
    {sourceLeft sourceRight :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    (hSourcePermutation :
      sourceLeft.Perm sourceRight)
    (hCompatible :
      DirectLFSelectionCompatible
        messageServers
        sourceRight
        targetQueue) :
    DirectLFSelectionCompatible
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
theorem DirectLFSelectionCompatible.perm_target
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetLeft targetRight :
      LF.ActionQueue}
    (hTargetPermutation :
      targetLeft.Perm targetRight)
    (hCompatible :
      DirectLFSelectionCompatible
        messageServers
        sourceQueue
        targetRight) :
    DirectLFSelectionCompatible
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
theorem directLFAlignedRemoval_of_source
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
            DirectLFAlignedOccurrence
                sourceMessage
                targetAction
                sourceRemaining
                targetRemaining →
              DirectLFAlignedOccurrence
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
            DirectLFAlignedOccurrence.tail
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
                DirectLFAlignedOccurrence.head
                  hHeadCorresponds

          | tail _hResidualHead hAlignedTail =>
              exact
                DirectLFAlignedOccurrence.tail
                  hHeadCorresponds
                  (hEmbedding
                    hAlignedTail)

/--
Symmetric ordered removal starting from one selected target occurrence.
-/
theorem directLFAlignedRemoval_of_target
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
            DirectLFAlignedOccurrence
                sourceMessage
                targetAction
                sourceRemaining
                targetRemaining →
              DirectLFAlignedOccurrence
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
            DirectLFAlignedOccurrence.tail
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
                DirectLFAlignedOccurrence.head
                  hHeadCorresponds

          | tail _hResidualHead hAlignedTail =>
              exact
                DirectLFAlignedOccurrence.tail
                  hHeadCorresponds
                  (hEmbedding
                    hAlignedTail)

/--
Removing one aligned source occurrence preserves ordered selection
compatibility.
-/
theorem DirectLFOrderedSelectionCompatible.remove_source
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hCompatible :
      DirectLFOrderedSelectionCompatible
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
        DirectLFOrderedSelectionCompatible
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
      directLFAlignedRemoval_of_source
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
theorem DirectLFOrderedSelectionCompatible.remove_target
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hCompatible :
      DirectLFOrderedSelectionCompatible
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
        DirectLFOrderedSelectionCompatible
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
      directLFAlignedRemoval_of_target
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
theorem DirectLFSelectionCompatible.remove_source
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {selectedMessage :
      DTR.PendingMessage}
    (hCompatible :
      DirectLFSelectionCompatible
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
        DirectLFSelectionCompatible
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
      DirectLFOrderedSelectionCompatible.remove_source
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
theorem DirectLFSelectionCompatible.remove_target
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {selectedAction :
      LF.PendingAction}
    (hCompatible :
      DirectLFSelectionCompatible
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
        DirectLFSelectionCompatible
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
      DirectLFOrderedSelectionCompatible.remove_target
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
