import Relico.Correctness.Dispatch
import Relico.Correctness.PriorityOrder
import Relico.Correctness.PriorityTiming
import Relico.DTR.MultiStorePriorityScheduling
import Relico.LF.MultiStoreReactionScheduling

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Every target occurrence in corresponding queues has a source
occurrence at the same list position.
-/
theorem QueueCorresponds.target_mem
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      QueueCorresponds
        sourceQueue
        targetQueue)
    {targetAction : LF.PendingAction}
    (hMembership :
      targetAction ∈
        targetQueue) :
    ∃ sourceMessage,
      sourceMessage ∈
          sourceQueue ∧
        PendingCorresponds
          sourceMessage
          targetAction := by

  induction hQueues with

  | nil =>
      simp at hMembership

  | cons
      headCorresponds
      tailCorresponds
      inductionHypothesis =>

      simp only [
        List.mem_cons
      ] at hMembership

      rcases hMembership with
        hHead | hTail

      · subst targetAction

        exact
          ⟨_,
           by simp,
           headCorresponds⟩

      · rcases
            inductionHypothesis
              hTail
          with
            ⟨sourceMessage,
             hSourceMembership,
             hCorresponds⟩

        exact
          ⟨sourceMessage,
           by
             simp only [
               List.mem_cons
             ]

             exact
               Or.inr
                 hSourceMembership,
           hCorresponds⟩

/--
Under the queue-wide zero-microstep invariant, source earliest-time
eligibility implies target earliest-tag eligibility.
-/
theorem sourceEarliest_implies_targetEarliest_of_allMicrostepsZero
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {sourceSelected : DTR.PendingMessage}
    {targetSelected : LF.PendingAction}
    (hQueues :
      QueueCorresponds
        sourceQueue
        targetQueue)
    (hSelected :
      PendingCorresponds
        sourceSelected
        targetSelected)
    (hTargetSelected :
      targetSelected ∈
        targetQueue)
    (hSourceEarliest :
      DTR.IsEarliest
        sourceSelected
        sourceQueue)
    (hAllMicrostepsZero :
      LF.ActionQueue.AllMicrostepsZero
        targetQueue) :
    LF.IsEarliest
      targetSelected
      targetQueue := by

  intro targetCandidate
  intro hTargetCandidate

  rcases
      QueueCorresponds.target_mem
        hQueues
        hTargetCandidate
    with
      ⟨sourceCandidate,
       hSourceCandidate,
       hCandidateCorresponds⟩

  have hTargetTimeOrder :
      targetSelected.tag.time ≤
        targetCandidate.tag.time := by

    calc
      targetSelected.tag.time
          =
        sourceSelected.arrivalTime :=
          hSelected.logicalTime

      _ ≤
        sourceCandidate.arrivalTime :=
          hSourceEarliest
            sourceCandidate
            hSourceCandidate

      _ =
        targetCandidate.tag.time :=
          hCandidateCorresponds.logicalTime.symm

  rcases
      Nat.lt_or_eq_of_le
        hTargetTimeOrder
    with
      hEarlier | hSameTime

  · exact
      Or.inl
        hEarlier

  · have hSelectedZero :
        targetSelected.tag.microstep =
          0 :=

      hAllMicrostepsZero
        targetSelected
        hTargetSelected

    have hCandidateZero :
        targetCandidate.tag.microstep =
          0 :=

      hAllMicrostepsZero
        targetCandidate
        hTargetCandidate

    apply
      LF.Tag.precedesOrEqual_same_time
        hSameTime

    calc
      targetSelected.tag.microstep
          =
        0 :=
          hSelectedZero

      _ ≤
        0 :=
          Nat.le_refl 0

      _ =
        targetCandidate.tag.microstep :=
          hCandidateZero.symm

/--
Source priority eligibility transports to generated-LF reaction
priority eligibility.

The target earliest-tag premise remains explicit. This preserves the
existing conditional forward-dispatch interface while adding the
priority-order obligation.
-/
theorem sourcePriorityEligible_implies_targetReactionPriorityEligible
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {sourceSelected : DTR.PendingMessage}
    {targetSelected : LF.PendingAction}
    (hQueues :
      QueueCorresponds
        sourceQueue
        targetQueue)
    (hSelected :
      PendingCorresponds
        sourceSelected
        targetSelected)
    (hTargetEarliest :
      LF.IsEarliest
        targetSelected
        targetQueue)
    (hSourceEligible :
      DTR.IsPriorityEligible
        messageServers
        sourceSelected
        sourceQueue) :
    LF.IsReactionPriorityEligible
      (Translation.compileMessageReactions
        messageServers)
      targetSelected
      targetQueue := by

  refine
    ⟨hTargetEarliest,
     ?_⟩

  intro targetCandidate
  intro hTargetCandidate
  intro hSameTag

  rcases
      QueueCorresponds.target_mem
        hQueues
        hTargetCandidate
    with
      ⟨sourceCandidate,
       hSourceCandidate,
       hCandidateCorresponds⟩

  have hSameTime :
      sourceCandidate.arrivalTime =
        sourceSelected.arrivalTime := by

    calc
      sourceCandidate.arrivalTime
          =
        targetCandidate.tag.time :=
          hCandidateCorresponds.logicalTime.symm

      _ =
        targetSelected.tag.time :=
          congrArg
            (fun tag : LF.Tag =>
              tag.time)
            hSameTag

      _ =
        sourceSelected.arrivalTime :=
          hSelected.logicalTime

  have hSourceOrder :
      DTR.PriorityServerNamePrecedesOrEqual
        sourceSelected.name
        sourceCandidate.name
        messageServers :=

    hSourceEligible.precedes_same_time
      hSourceCandidate
      hSameTime

  have hTargetOrder :
      LF.ReactionActionPrecedesOrEqual
        (Translation.actionNameFor
          sourceSelected.name)
        (Translation.actionNameFor
          sourceCandidate.name)
        (Translation.compileMessageReactions
          messageServers) :=

    priorityServerOrder_implies_reactionOrder
      hSourceOrder

  rw [
    hSelected.actionName,
    hCandidateCorresponds.actionName
  ]

  exact
    hTargetOrder

/--
Generated-LF reaction-priority eligibility transports back to source
priority eligibility when every pending target occurrence has
microstep zero.

The zero-microstep premise is essential: equal source logical times do
not otherwise imply equal complete LF tags.
-/
theorem targetReactionPriorityEligible_implies_sourcePriorityEligible
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {sourceSelected : DTR.PendingMessage}
    {targetSelected : LF.PendingAction}
    (hQueues :
      QueueCorresponds
        sourceQueue
        targetQueue)
    (hSelected :
      PendingCorresponds
        sourceSelected
        targetSelected)
    (hTargetSelected :
      targetSelected ∈
        targetQueue)
    (hTargetEligible :
      LF.IsReactionPriorityEligible
        (Translation.compileMessageReactions
          messageServers)
        targetSelected
        targetQueue)
    (hAllMicrostepsZero :
      LF.ActionQueue.AllMicrostepsZero
        targetQueue) :
    DTR.IsPriorityEligible
      messageServers
      sourceSelected
      sourceQueue := by

  refine
    ⟨targetEarliest_implies_sourceEarliest
        hQueues
        hSelected
        hTargetEligible.isEarliest,
     ?_⟩

  intro sourceCandidate
  intro hSourceCandidate
  intro hSameTime

  rcases
      QueueCorresponds.source_mem
        hQueues
        hSourceCandidate
    with
      ⟨targetCandidate,
       hTargetCandidate,
       hCandidateCorresponds⟩

  have hSelectedZero :
      targetSelected.tag.microstep =
        0 :=

    hAllMicrostepsZero
      targetSelected
      hTargetSelected

  have hCandidateZero :
      targetCandidate.tag.microstep =
        0 :=

    hAllMicrostepsZero
      targetCandidate
      hTargetCandidate

  have hSelectedTagEqualsCandidate :
      targetSelected.tag =
        targetCandidate.tag :=

    Correctness.PendingCorresponds.targetTag_eq_of_sameTime_and_zero
      hSelected
      hCandidateCorresponds
      hSameTime.symm
      hSelectedZero
      hCandidateZero

  have hTargetOrder :
      LF.ReactionActionPrecedesOrEqual
        targetSelected.name
        targetCandidate.name
        (Translation.compileMessageReactions
          messageServers) :=

    hTargetEligible.precedes_same_tag
      hTargetCandidate
      hSelectedTagEqualsCandidate.symm

  rw [
    hSelected.actionName,
    hCandidateCorresponds.actionName
  ] at hTargetOrder

  exact
    reactionOrder_implies_priorityServerOrder
      hTargetOrder

end Correctness
end Relico
