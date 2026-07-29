/-
Copyright (c) 2026.

Payload-preserving occurrence alignment for the direct DTR-to-LF
selection-compatible runtime relation.

This layer is additive. It does not alter DTR semantics, LF semantics, the
existing DirectLF relation, or the approved selection-compatibility condition.
-/

import Relico.Correctness.DirectLFSelectionCompatibility
import Relico.Correctness.PayloadDispatchQueue

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Permutation-invariant payload-preserving correspondence between a DTR pending
message bag and an LF action queue.

The source and target lists may use different concrete orders. Their ordered
representatives preserve generated action naming, logical occurrence time, and
the complete ordered payload of every occurrence.
-/
def DirectLFPayloadBagQueueCorresponds
    (sourceBag : DTR.MessageBag)
    (targetQueue : LF.ActionQueue) :
    Prop :=
  ∃ sourceRepresentative : DTR.MessageBag,
    ∃ targetRepresentative : LF.ActionQueue,
      sourceBag.Perm sourceRepresentative ∧
        targetQueue.Perm targetRepresentative ∧
        PayloadQueueCorresponds
          sourceRepresentative
          targetRepresentative

/--
Payload-aware occurrence correspondence projects to the established
permutation-invariant DirectLF bag/action-queue relation.
-/
theorem DirectLFPayloadBagQueueCorresponds.toBagQueueCorresponds
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      DirectLFPayloadBagQueueCorresponds
        sourceBag
        targetQueue) :
    DirectLFBagQueueCorresponds
      sourceBag
      targetQueue := by

  rcases hPayload with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hRepresentatives⟩

  exact
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hRepresentatives.toQueueCorresponds⟩

/--
Changing the concrete source-list representation preserves payload-aware
bag/action-queue correspondence.
-/
theorem DirectLFPayloadBagQueueCorresponds.perm_source
    {sourceLeft sourceRight : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hSourcePermutation :
      sourceLeft.Perm sourceRight)
    (hPayload :
      DirectLFPayloadBagQueueCorresponds
        sourceRight
        targetQueue) :
    DirectLFPayloadBagQueueCorresponds
      sourceLeft
      targetQueue := by

  rcases hPayload with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourceRepresentative,
     hTargetRepresentative,
     hRepresentatives⟩

  exact
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation.trans
       hSourceRepresentative,
     hTargetRepresentative,
     hRepresentatives⟩

/--
Changing the concrete target-list representation preserves payload-aware
bag/action-queue correspondence.
-/
theorem DirectLFPayloadBagQueueCorresponds.perm_target
    {sourceBag : DTR.MessageBag}
    {targetLeft targetRight : LF.ActionQueue}
    (hTargetPermutation :
      targetLeft.Perm targetRight)
    (hPayload :
      DirectLFPayloadBagQueueCorresponds
        sourceBag
        targetRight) :
    DirectLFPayloadBagQueueCorresponds
      sourceBag
      targetLeft := by

  rcases hPayload with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourceRepresentative,
     hTargetRepresentative,
     hRepresentatives⟩

  exact
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourceRepresentative,
     hTargetPermutation.trans
       hTargetRepresentative,
     hRepresentatives⟩

/--
Appending one payload-corresponding occurrence preserves ordered
payload-aware correspondence.
-/
theorem PayloadQueueCorresponds.append_one
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      PayloadQueueCorresponds
        sourceBag
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hPending :
      PendingPayloadCorresponds
        sourceMessage
        targetAction) :
    PayloadQueueCorresponds
      (sourceBag ++ [sourceMessage])
      (targetQueue ++ [targetAction]) := by

  induction hQueues with

  | nil =>
      exact
        PayloadQueueCorresponds.cons
          hPending
          PayloadQueueCorresponds.nil

  | cons head tail inductionHypothesis =>
      exact
        PayloadQueueCorresponds.cons
          head
          inductionHypothesis

/--
Appending one payload-corresponding source occurrence and generated LF
occurrence preserves the permutation-invariant payload relation.
-/
theorem DirectLFPayloadBagQueueCorresponds.append_one
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      DirectLFPayloadBagQueueCorresponds
        sourceBag
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hPending :
      PendingPayloadCorresponds
        sourceMessage
        targetAction) :
    DirectLFPayloadBagQueueCorresponds
      (sourceBag ++ [sourceMessage])
      (targetQueue ++ [targetAction]) := by

  rcases hQueues with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hRepresentatives⟩

  refine
    ⟨sourceRepresentative ++ [sourceMessage],
     targetRepresentative ++ [targetAction],
     ?_,
     ?_,
     hRepresentatives.append_one
       hPending⟩

  · exact
      List.Perm.append
        hSourcePermutation
        (List.Perm.refl
          [sourceMessage])

  · exact
      List.Perm.append
        hTargetPermutation
        (List.Perm.refl
          [targetAction])

/--
An occurrence aligned by the existing DirectLF positional relation preserves
its complete payload whenever the representative lists satisfy
`PayloadQueueCorresponds`.

This theorem is the key shared-alignment result: payload equality is recovered
for the same positional occurrence used by selection compatibility.
-/
theorem PayloadQueueCorresponds.pendingPayloadCorresponds_of_aligned
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      PayloadQueueCorresponds
        sourceBag
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hAligned :
      DirectLFAlignedOccurrence
        sourceMessage
        targetAction
        sourceBag
        targetQueue) :
    PendingPayloadCorresponds
      sourceMessage
      targetAction := by

  induction hQueues with

  | nil =>
      cases hAligned

  | cons head tail inductionHypothesis =>

      cases hAligned with

      | head _hPending =>
          exact head

      | tail _hHead hTail =>
          exact
            inductionHypothesis
              hTail

/--
Payload-aware selection compatibility for one ordered representative pair.

The established selection proof and the payload proof refer to exactly the
same source and target representative lists. Consequently, the positional
occurrence alignment used by the selection proof is also payload-preserving.
-/
structure DirectLFPayloadOrderedSelectionCompatible
    (messageServers : List DTR.MessageServer)
    (sourceRepresentative : DTR.MessageBag)
    (targetRepresentative : LF.ActionQueue) :
    Prop where

  selection :
    DirectLFOrderedSelectionCompatible
      messageServers
      sourceRepresentative
      targetRepresentative

  payloads :
    PayloadQueueCorresponds
      sourceRepresentative
      targetRepresentative

/--
Payload-aware ordered selection compatibility projects to the established
ordered selection-compatible relation.
-/
theorem DirectLFPayloadOrderedSelectionCompatible.toOrderedSelectionCompatible
    {messageServers : List DTR.MessageServer}
    {sourceRepresentative : DTR.MessageBag}
    {targetRepresentative : LF.ActionQueue}
    (hPayload :
      DirectLFPayloadOrderedSelectionCompatible
        messageServers
        sourceRepresentative
        targetRepresentative) :
    DirectLFOrderedSelectionCompatible
      messageServers
      sourceRepresentative
      targetRepresentative :=

  hPayload.selection

/--
Any occurrence aligned by a payload-aware ordered representative pair
preserves generated action naming, logical occurrence time, and exact payload.
-/
theorem DirectLFPayloadOrderedSelectionCompatible.alignedPayload
    {messageServers : List DTR.MessageServer}
    {sourceRepresentative : DTR.MessageBag}
    {targetRepresentative : LF.ActionQueue}
    (hPayload :
      DirectLFPayloadOrderedSelectionCompatible
        messageServers
        sourceRepresentative
        targetRepresentative)
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hAligned :
      DirectLFAlignedOccurrence
        sourceMessage
        targetAction
        sourceRepresentative
        targetRepresentative) :
    PendingPayloadCorresponds
      sourceMessage
      targetAction := by

  exact
    PayloadQueueCorresponds.pendingPayloadCorresponds_of_aligned
      hPayload.payloads
      hAligned

/--
Permutation-invariant payload-preserving DirectLF selection compatibility.

The selected representatives simultaneously carry:

* the approved DirectLF non-overtaking and priority compatibility proof; and
* exact payload correspondence at every aligned occurrence.

This proposition contains proof data only and does not alter either runtime
state.
-/
def DirectLFPayloadSelectionCompatible
    (messageServers : List DTR.MessageServer)
    (sourceBag : DTR.MessageBag)
    (targetQueue : LF.ActionQueue) :
    Prop :=
  ∃ sourceRepresentative : DTR.MessageBag,
    ∃ targetRepresentative : LF.ActionQueue,
      sourceBag.Perm sourceRepresentative ∧
        targetQueue.Perm targetRepresentative ∧
        DirectLFPayloadOrderedSelectionCompatible
          messageServers
          sourceRepresentative
          targetRepresentative

/--
Forgetting payload equality yields the existing approved DirectLF
selection-compatible relation.
-/
theorem DirectLFPayloadSelectionCompatible.toSelectionCompatible
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      DirectLFPayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    DirectLFSelectionCompatible
      messageServers
      sourceBag
      targetQueue := by

  rcases hPayload with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered⟩

  exact
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered.selection⟩

/--
Payload-aware selection compatibility contains the permutation-invariant
payload-preserving bag/action-queue relation.
-/
theorem DirectLFPayloadSelectionCompatible.toPayloadBagQueueCorresponds
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      DirectLFPayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    DirectLFPayloadBagQueueCorresponds
      sourceBag
      targetQueue := by

  rcases hPayload with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered⟩

  exact
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered.payloads⟩

/--
Payload-aware selection compatibility also contains the established
permutation-invariant name-and-time occurrence relation.
-/
theorem DirectLFPayloadSelectionCompatible.toBagQueueCorresponds
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      DirectLFPayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    DirectLFBagQueueCorresponds
      sourceBag
      targetQueue := by

  exact
    DirectLFSelectionCompatible.toBagQueueCorresponds
      hPayload.toSelectionCompatible

/--
Changing the concrete source-list representation preserves payload-aware
selection compatibility.
-/
theorem DirectLFPayloadSelectionCompatible.perm_source
    {messageServers : List DTR.MessageServer}
    {sourceLeft sourceRight : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hSourcePermutation :
      sourceLeft.Perm sourceRight)
    (hPayload :
      DirectLFPayloadSelectionCompatible
        messageServers
        sourceRight
        targetQueue) :
    DirectLFPayloadSelectionCompatible
      messageServers
      sourceLeft
      targetQueue := by

  rcases hPayload with
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
Changing the concrete target-list representation preserves payload-aware
selection compatibility.
-/
theorem DirectLFPayloadSelectionCompatible.perm_target
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetLeft targetRight : LF.ActionQueue}
    (hTargetPermutation :
      targetLeft.Perm targetRight)
    (hPayload :
      DirectLFPayloadSelectionCompatible
        messageServers
        sourceBag
        targetRight) :
    DirectLFPayloadSelectionCompatible
      messageServers
      sourceBag
      targetLeft := by

  rcases hPayload with
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
The empty source bag and empty LF action queue satisfy payload-aware DirectLF
selection compatibility.
-/
theorem directLFPayloadSelectionCompatible_nil
    (messageServers : List DTR.MessageServer) :
    DirectLFPayloadSelectionCompatible
      messageServers
      []
      [] := by

  refine
    ⟨[],
     [],
     List.Perm.refl [],
     List.Perm.refl [],
     ?_⟩

  refine {
    selection := ?_
    payloads :=
      PayloadQueueCorresponds.nil
  }

  refine {
    queues :=
      QueueCorresponds.nil
    pairwise := ?_
  }

  intro
    sourceLeft
    sourceRight
    targetLeft
    targetRight
    hLeft
    _hRight

  cases hLeft

end Correctness
end Relico
