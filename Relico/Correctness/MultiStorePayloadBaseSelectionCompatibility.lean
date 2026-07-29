/-
Copyright (c) 2026.

Selection compatibility for the direct DTR-to-LF translation.

This module formalizes the approved supported-fragment condition that LF
complete-tag order must not contradict DTR message-server priority among
pending occurrences at the same metric time.

The condition is proof-only. It does not add microsteps, annotations, or
other fields to DTR messages or DTR operational states.
-/

import Relico.Correctness.DirectLFBagQueueCorrespondence
import Relico.Correctness.MultiStorePayloadPriorityOrder
import Relico.DTR.MultiStorePayloadDispatch
import Relico.LF.MultiStorePayloadDispatch

set_option autoImplicit false

namespace Relico
namespace Correctness
/--
Strict precedence induced directly by the existing DTR scheduling relation.

This is not a new source scheduler. It is the asymmetric part of
`DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual`.
-/
def MultiStorePayloadBaseStrictPriorityPrecedes
    (messageServers : List DTR.MultiStorePayloadMessageServer)
    (left right : MsgName) :
    Prop :=
  DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
      left
      right
      messageServers ∧
    ¬DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
      right
      left
      messageServers

theorem MultiStorePayloadBaseStrictPriorityPrecedes.precedes
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {left right : MsgName}
    (hStrict :
      MultiStorePayloadBaseStrictPriorityPrecedes
        messageServers
        left
        right) :
    DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
      left
      right
      messageServers :=
  hStrict.1

theorem MultiStorePayloadBaseStrictPriorityPrecedes.not_reverse
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {left right : MsgName}
    (hStrict :
      MultiStorePayloadBaseStrictPriorityPrecedes
        messageServers
        left
        right) :
    ¬DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
      right
      left
      messageServers :=
  hStrict.2

/--
Selection compatibility for two aligned source/target occurrences.

For occurrences at different metric times, complete-tag order is already
determined by the time component.

For occurrences at the same metric time:

* equal LF microsteps defer ordering to generated reaction order;
* an earlier LF microstep must correspond to a strictly higher-priority DTR
  message server.

No LF microstep is added to either DTR message.
-/
def MultiStorePayloadBasePairSelectionCompatible
    (messageServers : List DTR.MultiStorePayloadMessageServer)
    (sourceLeft sourceRight : DTR.PendingMessage)
    (targetLeft targetRight : LF.PendingAction) :
    Prop :=
  Correctness.PendingCorresponds
      sourceLeft
      targetLeft ∧
    Correctness.PendingCorresponds
      sourceRight
      targetRight ∧
    (
      sourceLeft.arrivalTime ≠
        sourceRight.arrivalTime
      ∨
      targetLeft.tag.microstep =
        targetRight.tag.microstep
      ∨
      (
        targetLeft.tag.microstep <
          targetRight.tag.microstep ∧
        MultiStorePayloadBaseStrictPriorityPrecedes
          messageServers
          sourceLeft.name
          sourceRight.name
      )
      ∨
      (
        targetRight.tag.microstep <
          targetLeft.tag.microstep ∧
        MultiStorePayloadBaseStrictPriorityPrecedes
          messageServers
          sourceRight.name
          sourceLeft.name
      )
    )

theorem MultiStorePayloadBasePairSelectionCompatible.leftCorresponds
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight : DTR.PendingMessage}
    {targetLeft targetRight : LF.PendingAction}
    (hCompatible :
      MultiStorePayloadBasePairSelectionCompatible
        messageServers
        sourceLeft
        sourceRight
        targetLeft
        targetRight) :
    Correctness.PendingCorresponds
      sourceLeft
      targetLeft :=
  hCompatible.1

theorem MultiStorePayloadBasePairSelectionCompatible.rightCorresponds
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight : DTR.PendingMessage}
    {targetLeft targetRight : LF.PendingAction}
    (hCompatible :
      MultiStorePayloadBasePairSelectionCompatible
        messageServers
        sourceLeft
        sourceRight
        targetLeft
        targetRight) :
    Correctness.PendingCorresponds
      sourceRight
      targetRight :=
  hCompatible.2.1

theorem MultiStorePayloadBasePairSelectionCompatible.symm
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight : DTR.PendingMessage}
    {targetLeft targetRight : LF.PendingAction}
    (hCompatible :
      MultiStorePayloadBasePairSelectionCompatible
        messageServers
        sourceLeft
        sourceRight
        targetLeft
        targetRight) :
    MultiStorePayloadBasePairSelectionCompatible
      messageServers
      sourceRight
      sourceLeft
      targetRight
      targetLeft := by

  rcases hCompatible with
    ⟨hLeft,
     hRight,
     hOrder⟩

  refine
    ⟨hRight,
     hLeft,
     ?_⟩

  rcases hOrder with
    hDifferentTime |
    hSameMicrostep |
    hLeftEarlier |
    hRightEarlier

  · exact
      Or.inl
        (Ne.symm hDifferentTime)

  · exact
      Or.inr
        (Or.inl hSameMicrostep.symm)

  · exact
      Or.inr
        (Or.inr
          (Or.inr hLeftEarlier))

  · exact
      Or.inr
        (Or.inr
          (Or.inl hRightEarlier))

theorem multiStorePayloadBasePairSelectionCompatible_of_differentTime
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight : DTR.PendingMessage}
    {targetLeft targetRight : LF.PendingAction}
    (hLeft :
      Correctness.PendingCorresponds
        sourceLeft
        targetLeft)
    (hRight :
      Correctness.PendingCorresponds
        sourceRight
        targetRight)
    (hDifferentTime :
      sourceLeft.arrivalTime ≠
        sourceRight.arrivalTime) :
    MultiStorePayloadBasePairSelectionCompatible
      messageServers
      sourceLeft
      sourceRight
      targetLeft
      targetRight := by

  exact
    ⟨hLeft,
     hRight,
     Or.inl hDifferentTime⟩

theorem multiStorePayloadBasePairSelectionCompatible_of_sameMicrostep
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight : DTR.PendingMessage}
    {targetLeft targetRight : LF.PendingAction}
    (hLeft :
      Correctness.PendingCorresponds
        sourceLeft
        targetLeft)
    (hRight :
      Correctness.PendingCorresponds
        sourceRight
        targetRight)
    (hSameMicrostep :
      targetLeft.tag.microstep =
        targetRight.tag.microstep) :
    MultiStorePayloadBasePairSelectionCompatible
      messageServers
      sourceLeft
      sourceRight
      targetLeft
      targetRight := by

  exact
    ⟨hLeft,
     hRight,
     Or.inr
       (Or.inl hSameMicrostep)⟩

theorem multiStorePayloadBasePairSelectionCompatible_of_leftEarlier
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight : DTR.PendingMessage}
    {targetLeft targetRight : LF.PendingAction}
    (hLeft :
      Correctness.PendingCorresponds
        sourceLeft
        targetLeft)
    (hRight :
      Correctness.PendingCorresponds
        sourceRight
        targetRight)
    (hMicrostep :
      targetLeft.tag.microstep <
        targetRight.tag.microstep)
    (hPriority :
      MultiStorePayloadBaseStrictPriorityPrecedes
        messageServers
        sourceLeft.name
        sourceRight.name) :
    MultiStorePayloadBasePairSelectionCompatible
      messageServers
      sourceLeft
      sourceRight
      targetLeft
      targetRight := by

  exact
    ⟨hLeft,
     hRight,
     Or.inr
       (Or.inr
         (Or.inl
           ⟨hMicrostep,
            hPriority⟩))⟩

theorem MultiStorePayloadBasePairSelectionCompatible.strictPriority_of_leftEarlier
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight : DTR.PendingMessage}
    {targetLeft targetRight : LF.PendingAction}
    (hCompatible :
      MultiStorePayloadBasePairSelectionCompatible
        messageServers
        sourceLeft
        sourceRight
        targetLeft
        targetRight)
    (hSameTime :
      sourceLeft.arrivalTime =
        sourceRight.arrivalTime)
    (hMicrostep :
      targetLeft.tag.microstep <
        targetRight.tag.microstep) :
    MultiStorePayloadBaseStrictPriorityPrecedes
      messageServers
      sourceLeft.name
      sourceRight.name := by

  rcases hCompatible with
    ⟨_hLeft,
     _hRight,
     hOrder⟩

  rcases hOrder with
    hDifferentTime |
    hEqualMicrostep |
    hLeftEarlier |
    hRightEarlier

  · exact
      False.elim
        (hDifferentTime hSameTime)

  · exact
      False.elim
        ((Nat.ne_of_lt hMicrostep)
          hEqualMicrostep)

  · exact
      hLeftEarlier.2

  · exact
      False.elim
        ((Nat.lt_asymm hMicrostep)
          hRightEarlier.1)

theorem MultiStorePayloadBasePairSelectionCompatible.strictPriority_of_rightEarlier
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceLeft sourceRight : DTR.PendingMessage}
    {targetLeft targetRight : LF.PendingAction}
    (hCompatible :
      MultiStorePayloadBasePairSelectionCompatible
        messageServers
        sourceLeft
        sourceRight
        targetLeft
        targetRight)
    (hSameTime :
      sourceLeft.arrivalTime =
        sourceRight.arrivalTime)
    (hMicrostep :
      targetRight.tag.microstep <
        targetLeft.tag.microstep) :
    MultiStorePayloadBaseStrictPriorityPrecedes
      messageServers
      sourceRight.name
      sourceLeft.name := by

  exact
    hCompatible.symm.strictPriority_of_leftEarlier
      hSameTime.symm
      hMicrostep

/--
An aligned occurrence identifies one corresponding position in an ordered
source/target representative pair.

This relation distinguishes duplicate occurrences through its derivation.
-/
inductive MultiStorePayloadBaseAlignedOccurrence
    (sourceMessage : DTR.PendingMessage)
    (targetAction : LF.PendingAction) :
    DTR.MessageBag →
    LF.ActionQueue →
    Prop

  | head
      {sourceRemaining : DTR.MessageBag}
      {targetRemaining : LF.ActionQueue}
      (hPending :
        Correctness.PendingCorresponds
          sourceMessage
          targetAction) :
      MultiStorePayloadBaseAlignedOccurrence
        sourceMessage
        targetAction
        (sourceMessage :: sourceRemaining)
        (targetAction :: targetRemaining)

  | tail
      {sourceHead : DTR.PendingMessage}
      {targetHead : LF.PendingAction}
      {sourceRemaining : DTR.MessageBag}
      {targetRemaining : LF.ActionQueue}
      (hHead :
        Correctness.PendingCorresponds
          sourceHead
          targetHead)
      (hTail :
        MultiStorePayloadBaseAlignedOccurrence
          sourceMessage
          targetAction
          sourceRemaining
          targetRemaining) :
      MultiStorePayloadBaseAlignedOccurrence
        sourceMessage
        targetAction
        (sourceHead :: sourceRemaining)
        (targetHead :: targetRemaining)

theorem MultiStorePayloadBaseAlignedOccurrence.pendingCorresponds
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hAligned :
      MultiStorePayloadBaseAlignedOccurrence
        sourceMessage
        targetAction
        sourceQueue
        targetQueue) :
    Correctness.PendingCorresponds
      sourceMessage
      targetAction := by

  induction hAligned with

  | head hPending =>
      exact hPending

  | tail _hHead _hTail inductionHypothesis =>
      exact inductionHypothesis

theorem MultiStorePayloadBaseAlignedOccurrence.source_mem
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hAligned :
      MultiStorePayloadBaseAlignedOccurrence
        sourceMessage
        targetAction
        sourceQueue
        targetQueue) :
    sourceMessage ∈ sourceQueue := by

  induction hAligned with

  | head _hPending =>
      simp

  | tail _hHead _hTail inductionHypothesis =>
      exact
        List.mem_cons_of_mem
          _
          inductionHypothesis

theorem MultiStorePayloadBaseAlignedOccurrence.target_mem
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hAligned :
      MultiStorePayloadBaseAlignedOccurrence
        sourceMessage
        targetAction
        sourceQueue
        targetQueue) :
    targetAction ∈ targetQueue := by

  induction hAligned with

  | head _hPending =>
      simp

  | tail _hHead _hTail inductionHypothesis =>
      exact
        List.mem_cons_of_mem
          _
          inductionHypothesis

/--
Selection compatibility for one ordered representative pair.

`pairwise` quantifies over aligned occurrences, not raw list membership, so
duplicate values remain distinct occurrences.
-/
structure MultiStorePayloadBaseOrderedSelectionCompatible
    (messageServers : List DTR.MultiStorePayloadMessageServer)
    (sourceRepresentative : DTR.MessageBag)
    (targetRepresentative : LF.ActionQueue) :
    Prop where

  queues :
    Correctness.QueueCorresponds
      sourceRepresentative
      targetRepresentative

  pairwise :
    ∀
      {sourceLeft sourceRight : DTR.PendingMessage}
      {targetLeft targetRight : LF.PendingAction},
      MultiStorePayloadBaseAlignedOccurrence
        sourceLeft
        targetLeft
        sourceRepresentative
        targetRepresentative →
      MultiStorePayloadBaseAlignedOccurrence
        sourceRight
        targetRight
        sourceRepresentative
        targetRepresentative →
      MultiStorePayloadBasePairSelectionCompatible
        messageServers
        sourceLeft
        sourceRight
        targetLeft
        targetRight

/--
Permutation-invariant supported-fragment assumption.

The source and target lists may use arbitrary concrete list orders. The
existential representative pair provides the occurrence alignment used by the
selection-compatibility proof.

This is a proposition rather than a data structure: the representatives are
proof witnesses and do not extend either operational state.
-/
def MultiStorePayloadBaseSelectionCompatible
    (messageServers : List DTR.MultiStorePayloadMessageServer)
    (sourceQueue : DTR.MessageBag)
    (targetQueue : LF.ActionQueue) :
    Prop :=
  ∃ sourceRepresentative : DTR.MessageBag,
    ∃ targetRepresentative : LF.ActionQueue,
      sourceQueue.Perm
          sourceRepresentative ∧
        targetQueue.Perm
          targetRepresentative ∧
        MultiStorePayloadBaseOrderedSelectionCompatible
          messageServers
          sourceRepresentative
          targetRepresentative

/--
Selection compatibility includes the previously established bag/event
correspondence.
-/
theorem MultiStorePayloadBaseSelectionCompatible.toBagQueueCorresponds
    {messageServers : List DTR.MultiStorePayloadMessageServer}
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hCompatible :
      MultiStorePayloadBaseSelectionCompatible
        messageServers
        sourceQueue
        targetQueue) :
    Correctness.DirectLFBagQueueCorresponds
      sourceQueue
      targetQueue := by

  rcases hCompatible with
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
     hOrdered.queues⟩

/--
The empty source and target collections satisfy selection compatibility.
-/
theorem multiStorePayloadBaseSelectionCompatible_nil
    (messageServers : List DTR.MultiStorePayloadMessageServer) :
    MultiStorePayloadBaseSelectionCompatible
      messageServers
      []
      [] := by

  refine
    ⟨[],
     [],
     List.Perm.refl [],
     List.Perm.refl [],
     ?_⟩

  refine
    {
      queues :=
        Correctness.QueueCorresponds.nil
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


/-!
Occurrence-alignment helpers.
-/

/--
A source occurrence in an ordered corresponding pair has an aligned target
occurrence.

The witness is an occurrence derivation, not merely a value-level membership
fact.
-/
theorem multiStorePayloadBaseAlignedOccurrence_of_source_mem
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      Correctness.QueueCorresponds
        sourceQueue
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    (hMembership :
      sourceMessage ∈ sourceQueue) :
    ∃ targetAction,
      MultiStorePayloadBaseAlignedOccurrence
        sourceMessage
        targetAction
        sourceQueue
        targetQueue := by

  induction hQueues with

  | nil =>
      simp at hMembership

  | cons headCorresponds
      tailCorresponds
      inductionHypothesis =>

      simp only [List.mem_cons] at hMembership

      rcases hMembership with
        hAtHead |
        hInTail

      · subst sourceMessage

        exact
          ⟨_,
           MultiStorePayloadBaseAlignedOccurrence.head
             headCorresponds⟩

      · obtain
          ⟨targetAction,
           hAligned⟩ :=
            inductionHypothesis
              hInTail

        exact
          ⟨targetAction,
           MultiStorePayloadBaseAlignedOccurrence.tail
             headCorresponds
             hAligned⟩

/--
A target occurrence in an ordered corresponding pair has an aligned source
occurrence.
-/
theorem multiStorePayloadBaseAlignedOccurrence_of_target_mem
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
      MultiStorePayloadBaseAlignedOccurrence
        sourceMessage
        targetAction
        sourceQueue
        targetQueue := by

  induction hQueues with

  | nil =>
      simp at hMembership

  | cons headCorresponds
      tailCorresponds
      inductionHypothesis =>

      simp only [List.mem_cons] at hMembership

      rcases hMembership with
        hAtHead |
        hInTail

      · subst targetAction

        exact
          ⟨_,
           MultiStorePayloadBaseAlignedOccurrence.head
             headCorresponds⟩

      · obtain
          ⟨sourceMessage,
           hAligned⟩ :=
            inductionHypothesis
              hInTail

        exact
          ⟨sourceMessage,
           MultiStorePayloadBaseAlignedOccurrence.tail
             headCorresponds
             hAligned⟩

/-!
Eligibility transport.
-/

/--
A source-priority-eligible occurrence has an aligned generated-LF occurrence
that is reaction-priority eligible.

The target occurrence is existential because value-level correspondence does
not uniquely identify an occurrence when equal values are repeated.
-/
theorem
    multiStorePayloadBase_sourcePriorityEligible_implies_exists_targetReactionPriorityEligible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceSelected :
      DTR.PendingMessage}
    (hCompatible :
      MultiStorePayloadBaseSelectionCompatible
        messageServers
        sourceQueue
        targetQueue)
    (hSourceSelected :
      sourceSelected ∈ sourceQueue)
    (hSourceEligible :
      DTR.MultiStorePayloadIsPriorityEligible
        messageServers
        sourceSelected
        sourceQueue) :
    ∃ targetSelected,
      targetSelected ∈ targetQueue ∧
        Correctness.PendingCorresponds
          sourceSelected
          targetSelected ∧
        LF.MultiStorePayloadIsReactionPriorityEligible
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetSelected
          targetQueue := by

  rcases hCompatible with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered⟩

  have hSourceSelectedRepresentative :
      sourceSelected ∈ sourceRepresentative :=
    (List.Perm.mem_iff
      hSourcePermutation).mp
      hSourceSelected

  obtain
    ⟨targetSelected,
     hSelectedAligned⟩ :=
      multiStorePayloadBaseAlignedOccurrence_of_source_mem
        hOrdered.queues
        hSourceSelectedRepresentative

  have hTargetSelectedRepresentative :
      targetSelected ∈ targetRepresentative :=
    hSelectedAligned.target_mem

  have hTargetSelected :
      targetSelected ∈ targetQueue :=
    (List.Perm.mem_iff
      hTargetPermutation).mpr
      hTargetSelectedRepresentative

  have hSelectedCorresponds :
      Correctness.PendingCorresponds
        sourceSelected
        targetSelected :=
    hSelectedAligned.pendingCorresponds

  refine
    ⟨targetSelected,
     hTargetSelected,
     hSelectedCorresponds,
     ?_⟩

  refine
    ⟨?_,
     ?_⟩

  · intro targetCandidate
    intro hTargetCandidate

    have hTargetCandidateRepresentative :
        targetCandidate ∈ targetRepresentative :=
      (List.Perm.mem_iff
        hTargetPermutation).mp
        hTargetCandidate

    obtain
      ⟨sourceCandidate,
       hCandidateAligned⟩ :=
        multiStorePayloadBaseAlignedOccurrence_of_target_mem
          hOrdered.queues
          hTargetCandidateRepresentative

    have hSourceCandidateRepresentative :
        sourceCandidate ∈ sourceRepresentative :=
      hCandidateAligned.source_mem

    have hSourceCandidate :
        sourceCandidate ∈ sourceQueue :=
      (List.Perm.mem_iff
        hSourcePermutation).mpr
        hSourceCandidateRepresentative

    have hCandidateCorresponds :
        Correctness.PendingCorresponds
          sourceCandidate
          targetCandidate :=
      hCandidateAligned.pendingCorresponds

    have hSourceTimeLe :
        sourceSelected.arrivalTime ≤
          sourceCandidate.arrivalTime :=
      hSourceEligible.isEarliest
        sourceCandidate
        hSourceCandidate

    by_cases hSameSourceTime :
        sourceSelected.arrivalTime =
          sourceCandidate.arrivalTime

    · have hSameTargetTime :
          targetSelected.tag.time =
            targetCandidate.tag.time := by

        calc
          targetSelected.tag.time =
              sourceSelected.arrivalTime :=
            hSelectedCorresponds.logicalTime

          _ = sourceCandidate.arrivalTime :=
            hSameSourceTime

          _ = targetCandidate.tag.time :=
            hCandidateCorresponds.logicalTime.symm

      rcases
        Nat.lt_trichotomy
          targetSelected.tag.microstep
          targetCandidate.tag.microstep
        with
        hSelectedEarlier |
        hSameMicrostep |
        hCandidateEarlier

      · exact
          LF.Tag.precedesOrEqual_same_time
            hSameTargetTime
            (Nat.le_of_lt
              hSelectedEarlier)

      · have hMicrostepLe :
            targetSelected.tag.microstep ≤
              targetCandidate.tag.microstep := by

          simpa [hSameMicrostep]

        exact
          LF.Tag.precedesOrEqual_same_time
            hSameTargetTime
            hMicrostepLe

      · have hPairCompatible :
            MultiStorePayloadBasePairSelectionCompatible
              messageServers
              sourceSelected
              sourceCandidate
              targetSelected
              targetCandidate :=
          hOrdered.pairwise
            hSelectedAligned
            hCandidateAligned

        have hCandidateStrictlyPrecedes :
            MultiStorePayloadBaseStrictPriorityPrecedes
              messageServers
              sourceCandidate.name
              sourceSelected.name :=
          hPairCompatible.strictPriority_of_rightEarlier
            hSameSourceTime
            hCandidateEarlier

        have hSelectedPrecedesCandidate :
            DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
              sourceSelected.name
              sourceCandidate.name
              messageServers :=
          hSourceEligible.precedes_same_time
            hSourceCandidate
            hSameSourceTime.symm

        exact
          False.elim
            (hCandidateStrictlyPrecedes.not_reverse
              hSelectedPrecedesCandidate)

    · rcases
        Nat.lt_trichotomy
          sourceSelected.arrivalTime
          sourceCandidate.arrivalTime
        with
        hSelectedEarlier |
        hEqual |
        hCandidateEarlier

      · have hTargetTimeEarlier :
            targetSelected.tag.time <
              targetCandidate.tag.time := by

          calc
            targetSelected.tag.time =
                sourceSelected.arrivalTime :=
              hSelectedCorresponds.logicalTime

            _ < sourceCandidate.arrivalTime :=
              hSelectedEarlier

            _ = targetCandidate.tag.time :=
              hCandidateCorresponds.logicalTime.symm

        exact
          Or.inl
            hTargetTimeEarlier

      · exact
          False.elim
            (hSameSourceTime hEqual)

      · exact
          False.elim
            ((Nat.not_lt.mpr
                hSourceTimeLe)
              hCandidateEarlier)

  · intro targetCandidate
    intro hTargetCandidate
    intro hSameTag

    have hTargetCandidateRepresentative :
        targetCandidate ∈ targetRepresentative :=
      (List.Perm.mem_iff
        hTargetPermutation).mp
        hTargetCandidate

    obtain
      ⟨sourceCandidate,
       hCandidateAligned⟩ :=
        multiStorePayloadBaseAlignedOccurrence_of_target_mem
          hOrdered.queues
          hTargetCandidateRepresentative

    have hSourceCandidate :
        sourceCandidate ∈ sourceQueue :=
      (List.Perm.mem_iff
        hSourcePermutation).mpr
        hCandidateAligned.source_mem

    have hCandidateCorresponds :
        Correctness.PendingCorresponds
          sourceCandidate
          targetCandidate :=
      hCandidateAligned.pendingCorresponds

    have hSameSourceTime :
        sourceCandidate.arrivalTime =
          sourceSelected.arrivalTime := by

      calc
        sourceCandidate.arrivalTime =
            targetCandidate.tag.time :=
          hCandidateCorresponds.logicalTime.symm

        _ = targetSelected.tag.time :=
          congrArg LF.Tag.time
            hSameTag

        _ = sourceSelected.arrivalTime :=
          hSelectedCorresponds.logicalTime

    have hSourceOrder :
        DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
          sourceSelected.name
          sourceCandidate.name
          messageServers :=
      hSourceEligible.precedes_same_time
        hSourceCandidate
        hSameSourceTime

    have hReactionOrder :
        LF.MultiStorePayloadReactionActionPrecedesOrEqual
          (Translation.actionNameFor
            sourceSelected.name)
          (Translation.actionNameFor
            sourceCandidate.name)
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers) :=
      Correctness.multiStorePayloadPriorityServerOrder_implies_reactionOrder
        hSourceOrder

    rw [
      hSelectedCorresponds.actionName,
      hCandidateCorresponds.actionName
    ]

    exact hReactionOrder

/--
A reaction-priority-eligible generated-LF occurrence has an aligned source
occurrence that is source-priority eligible.
-/
theorem
    multiStorePayloadBase_targetReactionPriorityEligible_implies_exists_sourcePriorityEligible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {targetSelected :
      LF.PendingAction}
    (hCompatible :
      MultiStorePayloadBaseSelectionCompatible
        messageServers
        sourceQueue
        targetQueue)
    (hTargetSelected :
      targetSelected ∈ targetQueue)
    (hTargetEligible :
      LF.MultiStorePayloadIsReactionPriorityEligible
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetSelected
        targetQueue) :
    ∃ sourceSelected,
      sourceSelected ∈ sourceQueue ∧
        Correctness.PendingCorresponds
          sourceSelected
          targetSelected ∧
        DTR.MultiStorePayloadIsPriorityEligible
          messageServers
          sourceSelected
          sourceQueue := by

  rcases hCompatible with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered⟩

  have hTargetSelectedRepresentative :
      targetSelected ∈ targetRepresentative :=
    (List.Perm.mem_iff
      hTargetPermutation).mp
      hTargetSelected

  obtain
    ⟨sourceSelected,
     hSelectedAligned⟩ :=
      multiStorePayloadBaseAlignedOccurrence_of_target_mem
        hOrdered.queues
        hTargetSelectedRepresentative

  have hSourceSelectedRepresentative :
      sourceSelected ∈ sourceRepresentative :=
    hSelectedAligned.source_mem

  have hSourceSelected :
      sourceSelected ∈ sourceQueue :=
    (List.Perm.mem_iff
      hSourcePermutation).mpr
      hSourceSelectedRepresentative

  have hSelectedCorresponds :
      Correctness.PendingCorresponds
        sourceSelected
        targetSelected :=
    hSelectedAligned.pendingCorresponds

  refine
    ⟨sourceSelected,
     hSourceSelected,
     hSelectedCorresponds,
     ?_⟩

  refine
    ⟨?_,
     ?_⟩

  · intro sourceCandidate
    intro hSourceCandidate

    have hSourceCandidateRepresentative :
        sourceCandidate ∈ sourceRepresentative :=
      (List.Perm.mem_iff
        hSourcePermutation).mp
        hSourceCandidate

    obtain
      ⟨targetCandidate,
       hCandidateAligned⟩ :=
        multiStorePayloadBaseAlignedOccurrence_of_source_mem
          hOrdered.queues
          hSourceCandidateRepresentative

    have hTargetCandidate :
        targetCandidate ∈ targetQueue :=
      (List.Perm.mem_iff
        hTargetPermutation).mpr
        hCandidateAligned.target_mem

    have hCandidateCorresponds :
        Correctness.PendingCorresponds
          sourceCandidate
          targetCandidate :=
      hCandidateAligned.pendingCorresponds

    have hTargetTagOrder :
        targetSelected.tag.PrecedesOrEqual
          targetCandidate.tag :=
      hTargetEligible.isEarliest
        targetCandidate
        hTargetCandidate

    have hTargetTimeLe :
        targetSelected.tag.time ≤
          targetCandidate.tag.time :=
      LF.Tag.time_le_of_precedesOrEqual
        hTargetTagOrder

    calc
      sourceSelected.arrivalTime =
          targetSelected.tag.time :=
        hSelectedCorresponds.logicalTime.symm

      _ ≤ targetCandidate.tag.time :=
        hTargetTimeLe

      _ = sourceCandidate.arrivalTime :=
        hCandidateCorresponds.logicalTime

  · intro sourceCandidate
    intro hSourceCandidate
    intro hSameSourceTime

    have hSourceCandidateRepresentative :
        sourceCandidate ∈ sourceRepresentative :=
      (List.Perm.mem_iff
        hSourcePermutation).mp
        hSourceCandidate

    obtain
      ⟨targetCandidate,
       hCandidateAligned⟩ :=
        multiStorePayloadBaseAlignedOccurrence_of_source_mem
          hOrdered.queues
          hSourceCandidateRepresentative

    have hTargetCandidate :
        targetCandidate ∈ targetQueue :=
      (List.Perm.mem_iff
        hTargetPermutation).mpr
        hCandidateAligned.target_mem

    have hCandidateCorresponds :
        Correctness.PendingCorresponds
          sourceCandidate
          targetCandidate :=
      hCandidateAligned.pendingCorresponds

    have hSameTargetTime :
        targetCandidate.tag.time =
          targetSelected.tag.time := by

      calc
        targetCandidate.tag.time =
            sourceCandidate.arrivalTime :=
          hCandidateCorresponds.logicalTime

        _ = sourceSelected.arrivalTime :=
          hSameSourceTime

        _ = targetSelected.tag.time :=
          hSelectedCorresponds.logicalTime.symm

    rcases
      Nat.lt_trichotomy
        targetSelected.tag.microstep
        targetCandidate.tag.microstep
      with
      hSelectedEarlier |
      hSameMicrostep |
      hCandidateEarlier

    · have hPairCompatible :
          MultiStorePayloadBasePairSelectionCompatible
            messageServers
            sourceSelected
            sourceCandidate
            targetSelected
            targetCandidate :=
        hOrdered.pairwise
          hSelectedAligned
          hCandidateAligned

      have hSelectedStrictlyPrecedes :
          MultiStorePayloadBaseStrictPriorityPrecedes
            messageServers
            sourceSelected.name
            sourceCandidate.name :=
        hPairCompatible.strictPriority_of_leftEarlier
          hSameSourceTime.symm
          hSelectedEarlier

      exact
        hSelectedStrictlyPrecedes.precedes

    · have hSameTargetTag :
          targetCandidate.tag =
            targetSelected.tag :=
        LF.Tag.eq_of_time_eq_of_microstep
          hSameTargetTime
          hSameMicrostep.symm

      have hReactionOrder :
          LF.MultiStorePayloadReactionActionPrecedesOrEqual
            targetSelected.name
            targetCandidate.name
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers) :=
        hTargetEligible.precedes_same_tag
          hTargetCandidate
          hSameTargetTag

      rw [
        hSelectedCorresponds.actionName,
        hCandidateCorresponds.actionName
      ] at hReactionOrder

      exact
        Correctness.multiStorePayloadReactionOrder_implies_priorityServerOrder
          hReactionOrder

    · have hSelectedPrecedesCandidate :
          targetSelected.tag.PrecedesOrEqual
            targetCandidate.tag :=
        hTargetEligible.isEarliest
          targetCandidate
          hTargetCandidate

      exact
        False.elim
          ((LF.Tag.not_precedesOrEqual_same_time_of_microstep_lt
              hSameTargetTime
              hCandidateEarlier)
            hSelectedPrecedesCandidate)

end Correctness
end Relico
