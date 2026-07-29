/-
Copyright (c) 2026.

Payload-preserving occurrence alignment for the direct DTR-to-LF
selection-compatible runtime relation.

This layer is additive. It does not alter DTR semantics, LF semantics, the
existing MultiStorePayloadBase relation, or the approved selection-compatibility condition.
-/

import Relico.Correctness.MultiStorePayloadBaseSelectionCompatibility
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
def MultiStorePayloadBagQueueCorresponds
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
permutation-invariant MultiStorePayloadBase bag/action-queue relation.
-/
theorem MultiStorePayloadBagQueueCorresponds.toBagQueueCorresponds
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      MultiStorePayloadBagQueueCorresponds
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
theorem MultiStorePayloadBagQueueCorresponds.perm_source
    {sourceLeft sourceRight : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hSourcePermutation :
      sourceLeft.Perm sourceRight)
    (hPayload :
      MultiStorePayloadBagQueueCorresponds
        sourceRight
        targetQueue) :
    MultiStorePayloadBagQueueCorresponds
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
theorem MultiStorePayloadBagQueueCorresponds.perm_target
    {sourceBag : DTR.MessageBag}
    {targetLeft targetRight : LF.ActionQueue}
    (hTargetPermutation :
      targetLeft.Perm targetRight)
    (hPayload :
      MultiStorePayloadBagQueueCorresponds
        sourceBag
        targetRight) :
    MultiStorePayloadBagQueueCorresponds
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
theorem PayloadQueueCorresponds.multiStorePayload_append_one
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
theorem MultiStorePayloadBagQueueCorresponds.append_one
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      MultiStorePayloadBagQueueCorresponds
        sourceBag
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hPending :
      PendingPayloadCorresponds
        sourceMessage
        targetAction) :
    MultiStorePayloadBagQueueCorresponds
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
     hRepresentatives.multiStorePayload_append_one
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
An occurrence aligned by the existing MultiStorePayloadBase positional relation preserves
its complete payload whenever the representative lists satisfy
`PayloadQueueCorresponds`.

This theorem is the key shared-alignment result: payload equality is recovered
for the same positional occurrence used by selection compatibility.
-/
theorem PayloadQueueCorresponds.pendingPayloadCorresponds_of_multiStorePayloadAligned
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      PayloadQueueCorresponds
        sourceBag
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hAligned :
      MultiStorePayloadBaseAlignedOccurrence
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
structure MultiStorePayloadOrderedSelectionCompatible
    (messageServers : List DTR.MultiStorePayloadMessageServer)
    (sourceRepresentative : DTR.MessageBag)
    (targetRepresentative : LF.ActionQueue) :
    Prop where

  selection :
    MultiStorePayloadBaseOrderedSelectionCompatible
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
theorem MultiStorePayloadOrderedSelectionCompatible.toOrderedSelectionCompatible
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceRepresentative : DTR.MessageBag}
    {targetRepresentative : LF.ActionQueue}
    (hPayload :
      MultiStorePayloadOrderedSelectionCompatible
        messageServers
        sourceRepresentative
        targetRepresentative) :
    MultiStorePayloadBaseOrderedSelectionCompatible
      messageServers
      sourceRepresentative
      targetRepresentative :=

  hPayload.selection

/--
Any occurrence aligned by a payload-aware ordered representative pair
preserves generated action naming, logical occurrence time, and exact payload.
-/
theorem MultiStorePayloadOrderedSelectionCompatible.alignedPayload
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceRepresentative : DTR.MessageBag}
    {targetRepresentative : LF.ActionQueue}
    (hPayload :
      MultiStorePayloadOrderedSelectionCompatible
        messageServers
        sourceRepresentative
        targetRepresentative)
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hAligned :
      MultiStorePayloadBaseAlignedOccurrence
        sourceMessage
        targetAction
        sourceRepresentative
        targetRepresentative) :
    PendingPayloadCorresponds
      sourceMessage
      targetAction := by

  exact
    PayloadQueueCorresponds.pendingPayloadCorresponds_of_multiStorePayloadAligned
      hPayload.payloads
      hAligned

/--
Permutation-invariant payload-preserving MultiStorePayloadBase selection compatibility.

The selected representatives simultaneously carry:

* the approved MultiStorePayloadBase non-overtaking and priority compatibility proof; and
* exact payload correspondence at every aligned occurrence.

This proposition contains proof data only and does not alter either runtime
state.
-/
def MultiStorePayloadSelectionCompatible
    (messageServers : List DTR.MultiStorePayloadMessageServer)
    (sourceBag : DTR.MessageBag)
    (targetQueue : LF.ActionQueue) :
    Prop :=
  ∃ sourceRepresentative : DTR.MessageBag,
    ∃ targetRepresentative : LF.ActionQueue,
      sourceBag.Perm sourceRepresentative ∧
        targetQueue.Perm targetRepresentative ∧
        MultiStorePayloadOrderedSelectionCompatible
          messageServers
          sourceRepresentative
          targetRepresentative

/--
Forgetting payload equality yields the existing approved MultiStorePayloadBase
selection-compatible relation.
-/
theorem MultiStorePayloadSelectionCompatible.toSelectionCompatible
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    MultiStorePayloadBaseSelectionCompatible
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
theorem MultiStorePayloadSelectionCompatible.toPayloadBagQueueCorresponds
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    MultiStorePayloadBagQueueCorresponds
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
theorem MultiStorePayloadSelectionCompatible.toBagQueueCorresponds
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hPayload :
      MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue) :
    DirectLFBagQueueCorresponds
      sourceBag
      targetQueue := by

  exact
    MultiStorePayloadBaseSelectionCompatible.toBagQueueCorresponds
      hPayload.toSelectionCompatible

/--
Changing the concrete source-list representation preserves payload-aware
selection compatibility.
-/
theorem MultiStorePayloadSelectionCompatible.perm_source
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hSourcePermutation :
      sourceLeft.Perm sourceRight)
    (hPayload :
      MultiStorePayloadSelectionCompatible
        messageServers
        sourceRight
        targetQueue) :
    MultiStorePayloadSelectionCompatible
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
theorem MultiStorePayloadSelectionCompatible.perm_target
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceBag : DTR.MessageBag}
    {targetLeft targetRight : LF.ActionQueue}
    (hTargetPermutation :
      targetLeft.Perm targetRight)
    (hPayload :
      MultiStorePayloadSelectionCompatible
        messageServers
        sourceBag
        targetRight) :
    MultiStorePayloadSelectionCompatible
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
The empty source bag and empty LF action queue satisfy payload-aware MultiStorePayloadBase
selection compatibility.
-/
theorem multiStorePayloadSelectionCompatible_nil
    (messageServers : List DTR.MultiStorePayloadMessageServer) :
    MultiStorePayloadSelectionCompatible
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
