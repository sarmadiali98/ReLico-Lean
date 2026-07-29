/-
Copyright (c) 2026.

Preservation of payload-aware DirectLF selection compatibility under
single-occurrence dispatch removal.

The selected source and target occurrences are removed at one shared
representative-list position. This prevents equal-name/equal-time occurrences
with different payloads from being paired inconsistently.
-/

import Relico.Correctness.DirectLFPayloadSelectionCompatibility
import Relico.Correctness.DirectLFSelectionRemoval

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Remove the target occurrence at the same ordered position as one selected
source occurrence.

The residual payload correspondence and the embedding of every residual
alignment into the original representative pair are produced by the same
induction.
-/
theorem directLFPayloadAlignedRemoval_of_source
    {sourceBag sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {selectedMessage : DTR.PendingMessage}
    (hPayloads :
      PayloadQueueCorresponds
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
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        PayloadQueueCorresponds
          sourceRemaining
          targetRemaining ∧
        (
          ∀
            {sourceMessage : DTR.PendingMessage}
            {targetAction : LF.PendingAction},
            DirectLFAlignedOccurrence
                sourceMessage
                targetAction
                sourceRemaining
                targetRemaining →
              DirectLFAlignedOccurrence
                sourceMessage
                targetAction
                sourceBag
                targetQueue
        ) := by

  induction hRemove generalizing targetQueue with

  | head remaining =>

      cases hPayloads with

      | cons hSelectedPayload hRemainingPayloads =>

          refine
            ⟨_,
             _,
             Occurrence.RemovesOne.head _,
             hSelectedPayload,
             hRemainingPayloads,
             ?_⟩

          intro
            sourceMessage
            targetAction
            hAligned

          exact
            DirectLFAlignedOccurrence.tail
              hSelectedPayload.occurrence
              hAligned

  | tail sourceHead hTailRemove inductionHypothesis =>

      cases hPayloads with

      | cons hHeadPayload hTailPayloads =>

          obtain
            ⟨selectedAction,
             targetTailRemaining,
             hTargetTailRemove,
             hSelectedPayload,
             hRemainingPayloads,
             hEmbedding⟩ :=
              inductionHypothesis
                hTailPayloads

          refine
            ⟨selectedAction,
             _ :: targetTailRemaining,
             Occurrence.RemovesOne.tail
               _
               hTargetTailRemove,
             hSelectedPayload,
             PayloadQueueCorresponds.cons
               hHeadPayload
               hRemainingPayloads,
             ?_⟩

          intro
            sourceMessage
            targetAction
            hAligned

          cases hAligned with

          | head _hResidualHead =>

              exact
                DirectLFAlignedOccurrence.head
                  hHeadPayload.occurrence

          | tail _hResidualHead hAlignedTail =>

              exact
                DirectLFAlignedOccurrence.tail
                  hHeadPayload.occurrence
                  (hEmbedding hAlignedTail)

/--
Symmetric shared-position removal beginning with a selected target
occurrence.
-/
theorem directLFPayloadAlignedRemoval_of_target
    {sourceBag : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hPayloads :
      PayloadQueueCorresponds
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
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        PayloadQueueCorresponds
          sourceRemaining
          targetRemaining ∧
        (
          ∀
            {sourceMessage : DTR.PendingMessage}
            {targetAction : LF.PendingAction},
            DirectLFAlignedOccurrence
                sourceMessage
                targetAction
                sourceRemaining
                targetRemaining →
              DirectLFAlignedOccurrence
                sourceMessage
                targetAction
                sourceBag
                targetQueue
        ) := by

  induction hRemove generalizing sourceBag with

  | head remaining =>

      cases hPayloads with

      | cons hSelectedPayload hRemainingPayloads =>

          refine
            ⟨_,
             _,
             Occurrence.RemovesOne.head _,
             hSelectedPayload,
             hRemainingPayloads,
             ?_⟩

          intro
            sourceMessage
            targetAction
            hAligned

          exact
            DirectLFAlignedOccurrence.tail
              hSelectedPayload.occurrence
              hAligned

  | tail targetHead hTailRemove inductionHypothesis =>

      cases hPayloads with

      | cons hHeadPayload hTailPayloads =>

          obtain
            ⟨selectedMessage,
             sourceTailRemaining,
             hSourceTailRemove,
             hSelectedPayload,
             hRemainingPayloads,
             hEmbedding⟩ :=
              inductionHypothesis
                hTailPayloads

          refine
            ⟨selectedMessage,
             _ :: sourceTailRemaining,
             Occurrence.RemovesOne.tail
               _
               hSourceTailRemove,
             hSelectedPayload,
             PayloadQueueCorresponds.cons
               hHeadPayload
               hRemainingPayloads,
             ?_⟩

          intro
            sourceMessage
            targetAction
            hAligned

          cases hAligned with

          | head _hResidualHead =>

              exact
                DirectLFAlignedOccurrence.head
                  hHeadPayload.occurrence

          | tail _hResidualHead hAlignedTail =>

              exact
                DirectLFAlignedOccurrence.tail
                  hHeadPayload.occurrence
                  (hEmbedding hAlignedTail)

/--
Removing one source occurrence from an ordered payload-aware representative
pair preserves both selection compatibility and exact payload alignment.
-/
theorem DirectLFPayloadOrderedSelectionCompatible.remove_source
    {messageServers : List DTR.MessageServer}
    {sourceBag sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {selectedMessage : DTR.PendingMessage}
    (hCompatible :
      DirectLFPayloadOrderedSelectionCompatible
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
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        DirectLFPayloadOrderedSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  obtain
    ⟨selectedAction,
     targetRemaining,
     hTargetRemove,
     hSelectedPayload,
     hRemainingPayloads,
     hEmbedding⟩ :=
      directLFPayloadAlignedRemoval_of_source
        hCompatible.payloads
        hRemove

  refine
    ⟨selectedAction,
     targetRemaining,
     hTargetRemove,
     hSelectedPayload,
     ?_⟩

  refine
    {
      selection := ?_
      payloads := hRemainingPayloads
    }

  refine
    {
      queues :=
        hRemainingPayloads.toQueueCorresponds
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
    hCompatible.selection.pairwise
      (hEmbedding hLeft)
      (hEmbedding hRight)

/--
Removing one target occurrence from an ordered payload-aware representative
pair preserves both selection compatibility and exact payload alignment.
-/
theorem DirectLFPayloadOrderedSelectionCompatible.remove_target
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hCompatible :
      DirectLFPayloadOrderedSelectionCompatible
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
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        DirectLFPayloadOrderedSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  obtain
    ⟨selectedMessage,
     sourceRemaining,
     hSourceRemove,
     hSelectedPayload,
     hRemainingPayloads,
     hEmbedding⟩ :=
      directLFPayloadAlignedRemoval_of_target
        hCompatible.payloads
        hRemove

  refine
    ⟨selectedMessage,
     sourceRemaining,
     hSourceRemove,
     hSelectedPayload,
     ?_⟩

  refine
    {
      selection := ?_
      payloads := hRemainingPayloads
    }

  refine
    {
      queues :=
        hRemainingPayloads.toQueueCorresponds
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
    hCompatible.selection.pairwise
      (hEmbedding hLeft)
      (hEmbedding hRight)

/--
Remove one source occurrence from arbitrary concrete list representations.

The selected LF occurrence is the payload-corresponding occurrence at the same
position in the shared ordered representatives.
-/
theorem DirectLFPayloadSelectionCompatible.remove_source
    {messageServers : List DTR.MessageServer}
    {sourceBag sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {selectedMessage : DTR.PendingMessage}
    (hCompatible :
      DirectLFPayloadSelectionCompatible
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
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        DirectLFPayloadSelectionCompatible
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
     hSelectedPayload,
     hOrderedAfter⟩ :=
      DirectLFPayloadOrderedSelectionCompatible.remove_source
        hOrdered
        hSourceRepresentativeRemove

  obtain
    ⟨targetAfter,
     hTargetRemove,
     hTargetRepresentativeAfterPermutation⟩ :=
      directLF_transport_removesOne
        (List.Perm.symm hTargetPermutation)
        hTargetRepresentativeRemove

  refine
    ⟨selectedAction,
     targetAfter,
     hTargetRemove,
     hSelectedPayload,
     ?_⟩

  exact
    ⟨sourceRepresentativeAfter,
     targetRepresentativeAfter,
     hSourceAfterPermutation,
     List.Perm.symm
       hTargetRepresentativeAfterPermutation,
     hOrderedAfter⟩

/--
Symmetric payload-preserving removal from arbitrary concrete target-list
representations.
-/
theorem DirectLFPayloadSelectionCompatible.remove_target
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hCompatible :
      DirectLFPayloadSelectionCompatible
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
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        DirectLFPayloadSelectionCompatible
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
     hSelectedPayload,
     hOrderedAfter⟩ :=
      DirectLFPayloadOrderedSelectionCompatible.remove_target
        hOrdered
        hTargetRepresentativeRemove

  obtain
    ⟨sourceAfter,
     hSourceRemove,
     hSourceRepresentativeAfterPermutation⟩ :=
      directLF_transport_removesOne
        (List.Perm.symm hSourcePermutation)
        hSourceRepresentativeRemove

  refine
    ⟨selectedMessage,
     sourceAfter,
     hSourceRemove,
     hSelectedPayload,
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
