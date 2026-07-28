/-
Copyright (c) 2026.

Permutation-invariant correspondence between the ordinary DTR
pending-message bag and the generated LF pending-action collection.

This module deliberately keeps LF microsteps on the LF side. The source
relation uses ordinary `DTR.PendingMessage` occurrences and interprets their
list representation modulo `List.Perm`.
-/

import Relico.Correctness.Dispatch
import Relico.Correctness.DispatchForward

set_option autoImplicit false

namespace Relico
namespace Correctness
/--
Permutation-invariant correspondence between an ordinary DTR pending-message
bag and the generated LF pending-action collection.

The actual source and target lists may use different representations and
different list orders. Each is permutation-equivalent to an ordered
representative pair related by the established occurrence-preserving
`QueueCorresponds` relation.

No LF microstep is stored in the DTR state.
-/
def DirectLFBagQueueCorresponds
    (sourceQueue : DTR.MessageBag)
    (targetQueue : LF.ActionQueue) :
    Prop :=
  ∃ sourceRepresentative : DTR.MessageBag,
    ∃ targetRepresentative : LF.ActionQueue,
      sourceQueue.Perm sourceRepresentative ∧
      targetQueue.Perm targetRepresentative ∧
      Correctness.QueueCorresponds
        sourceRepresentative
        targetRepresentative

/--
Membership supplies a witness that removes exactly one occurrence.

This is independent of decidable equality. The selected occurrence is
identified by the derivation rather than by `List.erase`.
-/
theorem directLF_exists_removesOne_of_mem
    {α : Type}
    {selected : α}
    {before : List α}
    (hMembership :
      selected ∈ before) :
    ∃ after,
      Occurrence.RemovesOne
        selected
        before
        after := by

  induction before with

  | nil =>
      simp at hMembership

  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hMembership

      rcases hMembership with
        hSelectedHead |
        hSelectedTail

      · subst head

        exact
          ⟨tail,
           Occurrence.RemovesOne.head
             tail⟩

      · obtain
          ⟨after,
           hRemove⟩ :=
            inductionHypothesis
              hSelectedTail

        exact
          ⟨head :: after,
           Occurrence.RemovesOne.tail
             head
             hRemove⟩

/--
Removing one occurrence is equivalent, modulo permutation, to exposing that
occurrence at the head of the original list.
-/
theorem directLF_removesOne_perm_cons
    {α : Type}
    {selected : α}
    {before after : List α}
    (hRemove :
      Occurrence.RemovesOne
        selected
        before
        after) :
    before.Perm
      (selected :: after) := by

  induction hRemove with

  | head remaining =>
      exact
        List.Perm.refl
          (selected :: remaining)

  | tail headValue hTail inductionHypothesis =>
      exact
        (List.Perm.cons
            headValue
            inductionHypothesis).trans
          (List.Perm.swap
            selected
            headValue
            _)

/--
Transport a one-occurrence removal through a permutation of the original
collection.

The residual collections remain permutation-equivalent, including when equal
values occur more than once.
-/
theorem directLF_transport_removesOne
    {α : Type}
    {selected : α}
    {before after representative : List α}
    (hPermutation :
      before.Perm representative)
    (hRemove :
      Occurrence.RemovesOne
        selected
        before
        after) :
    ∃ representativeAfter,
      Occurrence.RemovesOne
          selected
          representative
          representativeAfter ∧
        after.Perm representativeAfter := by

  have hRepresentativeMembership :
      selected ∈ representative :=
    (List.Perm.mem_iff
      hPermutation).mp
      hRemove.selected_mem

  obtain
    ⟨representativeAfter,
     hRepresentativeRemove⟩ :=
      directLF_exists_removesOne_of_mem
        hRepresentativeMembership

  have hAfterConsToRepresentative :
      (selected :: after).Perm
        representative :=
    (directLF_removesOne_perm_cons
      hRemove).symm.trans
      hPermutation

  have hConsPermutation :
      (selected :: after).Perm
        (selected :: representativeAfter) :=
    hAfterConsToRepresentative.trans
      (directLF_removesOne_perm_cons
        hRepresentativeRemove)

  have hAfterPermutation :
      after.Perm representativeAfter :=
    List.Perm.cons_inv
      hConsPermutation

  exact
    ⟨representativeAfter,
     hRepresentativeRemove,
     hAfterPermutation⟩

/--
The established ordered queue relation induces the new bag relation.
-/
theorem directLFBagQueueCorresponds_of_queueCorresponds
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      Correctness.QueueCorresponds
        sourceQueue
        targetQueue) :
    DirectLFBagQueueCorresponds
      sourceQueue
      targetQueue := by

  exact
    ⟨sourceQueue,
     targetQueue,
     List.Perm.refl sourceQueue,
     List.Perm.refl targetQueue,
     hQueues⟩

/--
The two empty collections correspond.
-/
theorem directLFBagQueueCorresponds_nil :
    DirectLFBagQueueCorresponds
      []
      [] := by

  exact
    directLFBagQueueCorresponds_of_queueCorresponds
      Correctness.QueueCorresponds.nil

/--
Changing only the source list representation preserves bag correspondence.
-/
theorem DirectLFBagQueueCorresponds.perm_source
    {sourceLeft sourceRight : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hSourcePermutation :
      sourceLeft.Perm sourceRight)
    (hQueues :
      DirectLFBagQueueCorresponds
        sourceRight
        targetQueue) :
    DirectLFBagQueueCorresponds
      sourceLeft
      targetQueue := by

  rcases hQueues with
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
Changing only the target list representation preserves bag correspondence.
-/
theorem DirectLFBagQueueCorresponds.perm_target
    {sourceQueue : DTR.MessageBag}
    {targetLeft targetRight : LF.ActionQueue}
    (hTargetPermutation :
      targetLeft.Perm targetRight)
    (hQueues :
      DirectLFBagQueueCorresponds
        sourceQueue
        targetRight) :
    DirectLFBagQueueCorresponds
      sourceQueue
      targetLeft := by

  rcases hQueues with
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
Appending one corresponding source/target occurrence preserves correspondence.
The actual collections need not previously use the representative ordering.
-/
theorem DirectLFBagQueueCorresponds.append_one
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      DirectLFBagQueueCorresponds
        sourceQueue
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hPending :
      Correctness.PendingCorresponds
        sourceMessage
        targetAction) :
    DirectLFBagQueueCorresponds
      (sourceQueue ++ [sourceMessage])
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
     Correctness.QueueCorresponds.append_one
       hRepresentatives
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
Target membership in an ordered representative identifies its corresponding
source occurrence.

The established project has `QueueCorresponds.source_mem`; this is the
symmetric ordered helper needed by the bag relation.
-/
theorem directLF_queueCorresponds_target_mem
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      Correctness.QueueCorresponds
        sourceQueue
        targetQueue)
    {targetAction : LF.PendingAction}
    (hMembership :
      targetAction ∈ targetQueue) :
    ∃ sourceMessage,
      sourceMessage ∈ sourceQueue ∧
      Correctness.PendingCorresponds
        sourceMessage
        targetAction := by

  obtain
    ⟨targetRemaining,
     hTargetRemove⟩ :=
      directLF_exists_removesOne_of_mem
        hMembership

  obtain
    ⟨sourceMessage,
     _sourceRemaining,
     hSourceRemove,
     hPending,
     _hRemainingQueues⟩ :=
      Correctness.QueueCorresponds.remove_target
        hQueues
        hTargetRemove

  exact
    ⟨sourceMessage,
     hSourceRemove.selected_mem,
     hPending⟩

/--
Every source occurrence has a corresponding target occurrence.
-/
theorem DirectLFBagQueueCorresponds.source_mem
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      DirectLFBagQueueCorresponds
        sourceQueue
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    (hMembership :
      sourceMessage ∈ sourceQueue) :
    ∃ targetAction,
      targetAction ∈ targetQueue ∧
      Correctness.PendingCorresponds
        sourceMessage
        targetAction := by

  rcases hQueues with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hRepresentatives⟩

  have hSourceRepresentativeMembership :
      sourceMessage ∈ sourceRepresentative :=
    (List.Perm.mem_iff
      hSourcePermutation).mp
      hMembership

  obtain
    ⟨targetAction,
     hTargetRepresentativeMembership,
     hPending⟩ :=
      Correctness.QueueCorresponds.source_mem
        hRepresentatives
        hSourceRepresentativeMembership

  have hTargetMembership :
      targetAction ∈ targetQueue :=
    (List.Perm.mem_iff
      hTargetPermutation).mpr
      hTargetRepresentativeMembership

  exact
    ⟨targetAction,
     hTargetMembership,
     hPending⟩

/--
Every target occurrence has a corresponding source occurrence.
-/
theorem DirectLFBagQueueCorresponds.target_mem
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      DirectLFBagQueueCorresponds
        sourceQueue
        targetQueue)
    {targetAction : LF.PendingAction}
    (hMembership :
      targetAction ∈ targetQueue) :
    ∃ sourceMessage,
      sourceMessage ∈ sourceQueue ∧
      Correctness.PendingCorresponds
        sourceMessage
        targetAction := by

  rcases hQueues with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hRepresentatives⟩

  have hTargetRepresentativeMembership :
      targetAction ∈ targetRepresentative :=
    (List.Perm.mem_iff
      hTargetPermutation).mp
      hMembership

  obtain
    ⟨sourceMessage,
     hSourceRepresentativeMembership,
     hPending⟩ :=
      directLF_queueCorresponds_target_mem
        hRepresentatives
        hTargetRepresentativeMembership

  have hSourceMembership :
      sourceMessage ∈ sourceQueue :=
    (List.Perm.mem_iff
      hSourcePermutation).mpr
      hSourceRepresentativeMembership

  exact
    ⟨sourceMessage,
     hSourceMembership,
     hPending⟩

/--
Removing one source occurrence identifies and removes exactly one
corresponding target occurrence.

The residual collections continue to correspond modulo permutation.
-/
theorem DirectLFBagQueueCorresponds.remove_source
    {sourceQueue sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {selectedMessage : DTR.PendingMessage}
    (hQueues :
      DirectLFBagQueueCorresponds
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
        DirectLFBagQueueCorresponds
          sourceRemaining
          targetRemaining := by

  rcases hQueues with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hRepresentatives⟩

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
     hRepresentativesAfter⟩ :=
      Correctness.QueueCorresponds.remove_source
        hRepresentatives
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
     hRepresentativesAfter⟩

/--
Removing one target occurrence identifies and removes exactly one
corresponding source occurrence.

The residual collections continue to correspond modulo permutation.
-/
theorem DirectLFBagQueueCorresponds.remove_target
    {sourceQueue : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hQueues :
      DirectLFBagQueueCorresponds
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
        DirectLFBagQueueCorresponds
          sourceRemaining
          targetRemaining := by

  rcases hQueues with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hRepresentatives⟩

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
     hRepresentativesAfter⟩ :=
      Correctness.QueueCorresponds.remove_target
        hRepresentatives
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
     hRepresentativesAfter⟩

end Correctness
end Relico
