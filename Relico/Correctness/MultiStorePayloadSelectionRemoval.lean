/-
Copyright (c) 2026.

Preservation of payload-aware MultiStorePayloadBase selection compatibility under
single-occurrence dispatch removal.

The selected source and target occurrences are removed at one shared
representative-list position. This prevents equal-name/equal-time occurrences
with different payloads from being paired inconsistently.
-/

import Relico.Correctness.MultiStorePayloadSelectionCompatibility
import Relico.Correctness.MultiStorePayloadBaseSelectionRemoval

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
theorem multiStorePayloadAlignedRemoval_of_source
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
            MultiStorePayloadBaseAlignedOccurrence
                sourceMessage
                targetAction
                sourceRemaining
                targetRemaining →
              MultiStorePayloadBaseAlignedOccurrence
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
            MultiStorePayloadBaseAlignedOccurrence.tail
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
                MultiStorePayloadBaseAlignedOccurrence.head
                  hHeadPayload.occurrence

          | tail _hResidualHead hAlignedTail =>

              exact
                MultiStorePayloadBaseAlignedOccurrence.tail
                  hHeadPayload.occurrence
                  (hEmbedding hAlignedTail)

/--
Symmetric shared-position removal beginning with a selected target
occurrence.
-/
theorem multiStorePayloadAlignedRemoval_of_target
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
            MultiStorePayloadBaseAlignedOccurrence
                sourceMessage
                targetAction
                sourceRemaining
                targetRemaining →
              MultiStorePayloadBaseAlignedOccurrence
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
            MultiStorePayloadBaseAlignedOccurrence.tail
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
                MultiStorePayloadBaseAlignedOccurrence.head
                  hHeadPayload.occurrence

          | tail _hResidualHead hAlignedTail =>

              exact
                MultiStorePayloadBaseAlignedOccurrence.tail
                  hHeadPayload.occurrence
                  (hEmbedding hAlignedTail)

/--
Removing one source occurrence from an ordered payload-aware representative
pair preserves both selection compatibility and exact payload alignment.
-/
theorem MultiStorePayloadOrderedSelectionCompatible.remove_source
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceBag sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {selectedMessage : DTR.PendingMessage}
    (hCompatible :
      MultiStorePayloadOrderedSelectionCompatible
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
        MultiStorePayloadOrderedSelectionCompatible
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
      multiStorePayloadAlignedRemoval_of_source
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
theorem MultiStorePayloadOrderedSelectionCompatible.remove_target
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hCompatible :
      MultiStorePayloadOrderedSelectionCompatible
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
        MultiStorePayloadOrderedSelectionCompatible
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
      multiStorePayloadAlignedRemoval_of_target
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
theorem MultiStorePayloadSelectionCompatible.remove_source
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceBag sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {selectedMessage : DTR.PendingMessage}
    (hCompatible :
      MultiStorePayloadSelectionCompatible
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
        MultiStorePayloadSelectionCompatible
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
      MultiStorePayloadOrderedSelectionCompatible.remove_source
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
theorem MultiStorePayloadSelectionCompatible.remove_target
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hCompatible :
      MultiStorePayloadSelectionCompatible
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
        MultiStorePayloadSelectionCompatible
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
      MultiStorePayloadOrderedSelectionCompatible.remove_target
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
