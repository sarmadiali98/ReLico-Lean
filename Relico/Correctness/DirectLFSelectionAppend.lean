/-
Copyright (c) 2026.

Preservation of direct DTR-to-LF selection compatibility when one
corresponding occurrence is scheduled.

The append premise requires the new occurrence to be pair-compatible with
every retained aligned occurrence. This is the operational preservation form
of the approved selection-compatibility condition.

The proofs use ordinary DTR pending-message bags and LF action queues. They do
not add source-side microsteps or operational annotations.
-/

import Relico.Correctness.DirectLFSelectionRemoval

set_option autoImplicit false

namespace Relico
namespace Correctness
/--
Moving one appended value to the front preserves the list as a collection of
occurrences.

This lemma uses only `List.Perm`; no equality or decidable-equality assumption
on the element type is required.
-/
theorem directLF_append_singleton_perm_cons
    {α : Type}
    (value : α)
    (values : List α) :
    (values ++ [value]).Perm
      (value :: values) := by

  induction values with

  | nil =>
      simp

  | cons head tail inductionHypothesis =>
      exact
        (List.Perm.cons
            head
            inductionHypothesis).trans
          (List.Perm.swap
            value
            head
            tail)

/--
Classify an aligned occurrence after adding one corresponding occurrence at
the front.

The occurrence is either the new head occurrence or an aligned occurrence
from the previous representative pair.
-/
theorem directLFAlignedOccurrence_cons_cases
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceMessage :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hAligned :
      DirectLFAlignedOccurrence
        sourceMessage
        targetAction
        (sourceNew :: sourceQueue)
        (targetNew :: targetQueue)) :
    (
      sourceMessage = sourceNew ∧
      targetAction = targetNew
    ) ∨
    DirectLFAlignedOccurrence
      sourceMessage
      targetAction
      sourceQueue
      targetQueue := by

  cases hAligned with

  | head _hPending =>
      exact
        Or.inl
          ⟨rfl, rfl⟩

  | tail _hHead hTail =>
      exact
        Or.inr
          hTail

/--
Step-local append compatibility.

The existential representative pair is the same kind of proof-only alignment
used by `DirectLFSelectionCompatible`.

In addition to the existing ordered compatibility, the newly scheduled
source/LF occurrence must:

* correspond structurally; and
* be pair-compatible with every existing aligned occurrence.

The reverse orientation is obtained from symmetry of
`DirectLFPairSelectionCompatible`.
-/
def DirectLFSelectionAppendCompatible
    (messageServers :
      List DTR.MessageServer)
    (sourceQueue :
      DTR.MessageBag)
    (targetQueue :
      LF.ActionQueue)
    (sourceNew :
      DTR.PendingMessage)
    (targetNew :
      LF.PendingAction) :
    Prop :=
  ∃ sourceRepresentative :
      DTR.MessageBag,
    ∃ targetRepresentative :
        LF.ActionQueue,
      sourceQueue.Perm
          sourceRepresentative ∧
        targetQueue.Perm
          targetRepresentative ∧
        DirectLFOrderedSelectionCompatible
          messageServers
          sourceRepresentative
          targetRepresentative ∧
        PendingCorresponds
          sourceNew
          targetNew ∧
        ∀
          {sourceExisting :
            DTR.PendingMessage}
          {targetExisting :
            LF.PendingAction},
          DirectLFAlignedOccurrence
              sourceExisting
              targetExisting
              sourceRepresentative
              targetRepresentative →
            DirectLFPairSelectionCompatible
              messageServers
              sourceNew
              sourceExisting
              targetNew
              targetExisting

/--
The append premise contains the previous selection-compatibility invariant.
-/
theorem
    DirectLFSelectionAppendCompatible.toSelectionCompatible
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    (hAppend :
      DirectLFSelectionAppendCompatible
        messageServers
        sourceQueue
        targetQueue
        sourceNew
        targetNew) :
    DirectLFSelectionCompatible
      messageServers
      sourceQueue
      targetQueue := by

  rcases hAppend with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered,
     _hNewCorresponds,
     _hNewWithExisting⟩

  exact
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered⟩

/--
Adding one corresponding occurrence at the front preserves ordered selection
compatibility when the new occurrence is pair-compatible with every existing
aligned occurrence.
-/
theorem directLFOrderedSelectionCompatible_cons
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    (hCompatible :
      DirectLFOrderedSelectionCompatible
        messageServers
        sourceQueue
        targetQueue)
    (hNewCorresponds :
      PendingCorresponds
        sourceNew
        targetNew)
    (hNewWithExisting :
      ∀
        {sourceExisting :
          DTR.PendingMessage}
        {targetExisting :
          LF.PendingAction},
        DirectLFAlignedOccurrence
            sourceExisting
            targetExisting
            sourceQueue
            targetQueue →
          DirectLFPairSelectionCompatible
            messageServers
            sourceNew
            sourceExisting
            targetNew
            targetExisting) :
    DirectLFOrderedSelectionCompatible
      messageServers
      (sourceNew :: sourceQueue)
      (targetNew :: targetQueue) := by

  refine
    {
      queues :=
        QueueCorresponds.cons
          hNewCorresponds
          hCompatible.queues
      pairwise := ?_
    }

  intro
    sourceLeft
    sourceRight
    targetLeft
    targetRight
    hLeft
    hRight

  rcases
    directLFAlignedOccurrence_cons_cases
      hLeft
    with
    hLeftNew |
    hLeftExisting

  · rcases hLeftNew with
      ⟨rfl, rfl⟩

    rcases
      directLFAlignedOccurrence_cons_cases
        hRight
      with
      hRightNew |
      hRightExisting

    · rcases hRightNew with
        ⟨rfl, rfl⟩

      exact
        directLFPairSelectionCompatible_of_sameMicrostep
          hNewCorresponds
          hNewCorresponds
          rfl

    · exact
        hNewWithExisting
          hRightExisting

  · rcases
      directLFAlignedOccurrence_cons_cases
        hRight
      with
      hRightNew |
      hRightExisting

    · rcases hRightNew with
        ⟨rfl, rfl⟩

      exact
        (hNewWithExisting
          hLeftExisting).symm

    · exact
        hCompatible.pairwise
          hLeftExisting
          hRightExisting

/--
The empty representative pair admits any structurally corresponding new
occurrence.

There are no existing occurrences against which a pairwise obligation must be
proved.
-/
theorem directLFSelectionAppendCompatible_nil
    (messageServers :
      List DTR.MessageServer)
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    (hNewCorresponds :
      PendingCorresponds
        sourceNew
        targetNew) :
    DirectLFSelectionAppendCompatible
      messageServers
      []
      []
      sourceNew
      targetNew := by

  refine
    ⟨[],
     [],
     List.Perm.refl [],
     List.Perm.refl [],
     ?_,
     hNewCorresponds,
     ?_⟩

  · refine
      {
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

  · intro
      sourceExisting
      targetExisting
      hExisting

    cases hExisting

/--
The step-local append premise preserves selection compatibility when the new
occurrence is placed at the front of both representative collections.
-/
theorem DirectLFSelectionAppendCompatible.cons_one
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    (hAppend :
      DirectLFSelectionAppendCompatible
        messageServers
        sourceQueue
        targetQueue
        sourceNew
        targetNew) :
    DirectLFSelectionCompatible
      messageServers
      (sourceNew :: sourceQueue)
      (targetNew :: targetQueue) := by

  rcases hAppend with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered,
     hNewCorresponds,
     hNewWithExisting⟩

  exact
    ⟨sourceNew :: sourceRepresentative,
     targetNew :: targetRepresentative,
     List.Perm.cons
       sourceNew
       hSourcePermutation,
     List.Perm.cons
       targetNew
       hTargetPermutation,
     directLFOrderedSelectionCompatible_cons
       hOrdered
       hNewCorresponds
       hNewWithExisting⟩

/--
Operational append preservation.

Statements append newly scheduled work to the concrete source bag and LF
action queue. Since selection compatibility is permutation-invariant, this is
derived from front insertion by moving the final occurrence to the front.

No list position is treated as scheduler order.
-/
theorem DirectLFSelectionAppendCompatible.append_one
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceNew :
      DTR.PendingMessage}
    {targetNew :
      LF.PendingAction}
    (hAppend :
      DirectLFSelectionAppendCompatible
        messageServers
        sourceQueue
        targetQueue
        sourceNew
        targetNew) :
    DirectLFSelectionCompatible
      messageServers
      (sourceQueue ++ [sourceNew])
      (targetQueue ++ [targetNew]) := by

  have hConsCompatible :
      DirectLFSelectionCompatible
        messageServers
        (sourceNew :: sourceQueue)
        (targetNew :: targetQueue) :=
    hAppend.cons_one

  have hSourcePermutation :
      (sourceQueue ++ [sourceNew]).Perm
        (sourceNew :: sourceQueue) :=
    directLF_append_singleton_perm_cons
      sourceNew
      sourceQueue

  have hTargetPermutation :
      (targetQueue ++ [targetNew]).Perm
        (targetNew :: targetQueue) :=
    directLF_append_singleton_perm_cons
      targetNew
      targetQueue

  have hSourceAppended :
      DirectLFSelectionCompatible
        messageServers
        (sourceQueue ++ [sourceNew])
        (targetNew :: targetQueue) :=
    DirectLFSelectionCompatible.perm_source
      hSourcePermutation
      hConsCompatible

  exact
    DirectLFSelectionCompatible.perm_target
      hTargetPermutation
      hSourceAppended

/--
A corresponding singleton source bag and LF action queue satisfy selection
compatibility.
-/
theorem directLFSelectionCompatible_singleton
    (messageServers :
      List DTR.MessageServer)
    {sourceMessage :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hPending :
      PendingCorresponds
        sourceMessage
        targetAction) :
    DirectLFSelectionCompatible
      messageServers
      [sourceMessage]
      [targetAction] := by

  simpa using
    (directLFSelectionAppendCompatible_nil
      messageServers
      hPending).append_one

end Correctness
end Relico
