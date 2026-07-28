/-
Copyright (c) 2026.

Combined occurrence-sensitive dispatch-selection transport for the direct
DTR-to-LF translation.

The forward theorem synchronizes one concrete DTR message occurrence removal
with one corresponding LF action occurrence that is reaction-priority
eligible.

The backward theorem synchronizes one concrete LF action occurrence removal
with one corresponding DTR message occurrence that is source-priority
eligible.

Repeated equal values remain distinct occurrences. Eligibility transfer uses
only the scheduling fields observed by the schedulers: message/action name,
logical time, and LF tag. Payload equality is not required.

No source-side microstep, ghost state, restricted source semantics, or
positive-delay-only assumption is introduced.
-/

import Relico.Correctness.DirectLFSelectionRemoval

set_option autoImplicit false

namespace Relico
namespace Correctness
/--
Two source pending-message values corresponding to the same target action
have the same source message-server name.

Payload equality is intentionally not claimed.
-/
theorem pendingCorresponds_sourceName_eq_of_sameTarget
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hLeft :
      PendingCorresponds
        sourceLeft
        targetAction)
    (hRight :
      PendingCorresponds
        sourceRight
        targetAction) :
    sourceLeft.name =
      sourceRight.name := by

  apply
    Translation.actionNameFor_injective

  calc
    Translation.actionNameFor
        sourceLeft.name =
      targetAction.name :=
        hLeft.actionName.symm

    _ =
      Translation.actionNameFor
        sourceRight.name :=
          hRight.actionName

/--
Two source pending-message values corresponding to the same target action
have the same logical arrival time.

Payload equality is intentionally not claimed.
-/
theorem pendingCorresponds_sourceTime_eq_of_sameTarget
    {sourceLeft sourceRight :
      DTR.PendingMessage}
    {targetAction :
      LF.PendingAction}
    (hLeft :
      PendingCorresponds
        sourceLeft
        targetAction)
    (hRight :
      PendingCorresponds
        sourceRight
        targetAction) :
    sourceLeft.arrivalTime =
      sourceRight.arrivalTime := by

  calc
    sourceLeft.arrivalTime =
        targetAction.tag.time :=
      hLeft.logicalTime.symm

    _ =
        sourceRight.arrivalTime :=
      hRight.logicalTime

/--
Two target pending-action values corresponding to the same source message
have the same generated action name.

Payload equality is intentionally not claimed.
-/
theorem pendingCorresponds_targetName_eq_of_sameSource
    {sourceMessage :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hLeft :
      PendingCorresponds
        sourceMessage
        targetLeft)
    (hRight :
      PendingCorresponds
        sourceMessage
        targetRight) :
    targetLeft.name =
      targetRight.name := by

  calc
    targetLeft.name =
        Translation.actionNameFor
          sourceMessage.name :=
      hLeft.actionName

    _ =
        targetRight.name :=
      hRight.actionName.symm

/--
Two target pending-action values corresponding to the same source message
have the same metric-time component.

Their microsteps require the selection-compatibility argument below.
-/
theorem pendingCorresponds_targetTime_eq_of_sameSource
    {sourceMessage :
      DTR.PendingMessage}
    {targetLeft targetRight :
      LF.PendingAction}
    (hLeft :
      PendingCorresponds
        sourceMessage
        targetLeft)
    (hRight :
      PendingCorresponds
        sourceMessage
        targetRight) :
    targetLeft.tag.time =
      targetRight.tag.time := by

  calc
    targetLeft.tag.time =
        sourceMessage.arrivalTime :=
      hLeft.logicalTime

    _ =
        targetRight.tag.time :=
      hRight.logicalTime.symm

/--
Synchronize source occurrence removal with generated-LF eligibility.

The target occurrence returned by removal is proved eligible even when the
previous eligibility-transport theorem initially identifies a different equal
occurrence.

Selection compatibility forces both target occurrences to have the same
complete scheduling tag. Payload equality is unnecessary because reaction
scheduling depends only on action name and tag.
-/
theorem directLF_sourceDispatchSelection
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue sourceRemaining :
      DTR.MessageBag}
    {targetQueue :
      LF.ActionQueue}
    {sourceSelected :
      DTR.PendingMessage}
    (hCompatible :
      DirectLFSelectionCompatible
        messageServers
        sourceQueue
        targetQueue)
    (hRemoved :
      Occurrence.RemovesOne
        sourceSelected
        sourceQueue
        sourceRemaining)
    (hEligible :
      DTR.IsPriorityEligible
        messageServers
        sourceSelected
        sourceQueue) :
    ∃ targetSelected targetRemaining,
      Occurrence.RemovesOne
          targetSelected
          targetQueue
          targetRemaining ∧
        PendingCorresponds
          sourceSelected
          targetSelected ∧
        LF.IsReactionPriorityEligible
          (Translation.compileMessageReactions
            messageServers)
          targetSelected
          targetQueue ∧
        DirectLFSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  have hSourceSelected :
      sourceSelected ∈
        sourceQueue :=
    Occurrence.RemovesOne.selected_mem
      hRemoved

  obtain
    ⟨targetRemoved,
     targetRemaining,
     hTargetRemoved,
     hRemovedCorresponds,
     hRemainingCompatible⟩ :=
      DirectLFSelectionCompatible.remove_source
        hCompatible
        hRemoved

  obtain
    ⟨targetEligible,
     hTargetEligibleMember,
     hEligibleCorresponds,
     hTargetEligible⟩ :=
      directLF_sourcePriorityEligible_implies_exists_targetReactionPriorityEligible
        hCompatible
        hSourceSelected
        hEligible

  have hTargetRemovedMember :
      targetRemoved ∈
        targetQueue :=
    Occurrence.RemovesOne.selected_mem
      hTargetRemoved

  have hTargetName :
      targetRemoved.name =
        targetEligible.name :=
    pendingCorresponds_targetName_eq_of_sameSource
      hRemovedCorresponds
      hEligibleCorresponds

  have hTargetTime :
      targetRemoved.tag.time =
        targetEligible.tag.time :=
    pendingCorresponds_targetTime_eq_of_sameSource
      hRemovedCorresponds
      hEligibleCorresponds

  rcases hCompatible with
    ⟨sourceRepresentative,
     targetRepresentative,
     hSourcePermutation,
     hTargetPermutation,
     hOrdered⟩

  have hTargetRemovedRepresentative :
      targetRemoved ∈
        targetRepresentative :=
    (List.Perm.mem_iff
      hTargetPermutation).mp
        hTargetRemovedMember

  have hTargetEligibleRepresentative :
      targetEligible ∈
        targetRepresentative :=
    (List.Perm.mem_iff
      hTargetPermutation).mp
        hTargetEligibleMember

  obtain
    ⟨sourceRemovedRepresentative,
     hRemovedAligned⟩ :=
      directLFAlignedOccurrence_of_target_mem
        hOrdered.queues
        hTargetRemovedRepresentative

  obtain
    ⟨sourceEligibleRepresentative,
     hEligibleAligned⟩ :=
      directLFAlignedOccurrence_of_target_mem
        hOrdered.queues
        hTargetEligibleRepresentative

  have hRemovedRepresentativeCorresponds :
      PendingCorresponds
        sourceRemovedRepresentative
        targetRemoved :=
    hRemovedAligned.pendingCorresponds

  have hEligibleRepresentativeCorresponds :
      PendingCorresponds
        sourceEligibleRepresentative
        targetEligible :=
    hEligibleAligned.pendingCorresponds

  have hRemovedSourceName :
      sourceRemovedRepresentative.name =
        sourceSelected.name :=
    pendingCorresponds_sourceName_eq_of_sameTarget
      hRemovedRepresentativeCorresponds
      hRemovedCorresponds

  have hEligibleSourceName :
      sourceEligibleRepresentative.name =
        sourceSelected.name :=
    pendingCorresponds_sourceName_eq_of_sameTarget
      hEligibleRepresentativeCorresponds
      hEligibleCorresponds

  have hRepresentativeNames :
      sourceRemovedRepresentative.name =
        sourceEligibleRepresentative.name :=
    hRemovedSourceName.trans
      hEligibleSourceName.symm

  have hRemovedSourceTime :
      sourceRemovedRepresentative.arrivalTime =
        sourceSelected.arrivalTime :=
    pendingCorresponds_sourceTime_eq_of_sameTarget
      hRemovedRepresentativeCorresponds
      hRemovedCorresponds

  have hEligibleSourceTime :
      sourceEligibleRepresentative.arrivalTime =
        sourceSelected.arrivalTime :=
    pendingCorresponds_sourceTime_eq_of_sameTarget
      hEligibleRepresentativeCorresponds
      hEligibleCorresponds

  have hRepresentativeTimes :
      sourceRemovedRepresentative.arrivalTime =
        sourceEligibleRepresentative.arrivalTime :=
    hRemovedSourceTime.trans
      hEligibleSourceTime.symm

  have hPairCompatible :
      DirectLFPairSelectionCompatible
        messageServers
        sourceRemovedRepresentative
        sourceEligibleRepresentative
        targetRemoved
        targetEligible :=
    hOrdered.pairwise
      hRemovedAligned
      hEligibleAligned

  have hTargetMicrostep :
      targetRemoved.tag.microstep =
        targetEligible.tag.microstep := by

    rcases hPairCompatible.2.2 with
      hDifferentTime |
      hSameMicrostep |
      hRemovedEarlier |
      hEligibleEarlier

    · exact
        False.elim
          (hDifferentTime
            hRepresentativeTimes)

    · exact
        hSameMicrostep

    · have hStrict :
          DirectLFStrictPriorityPrecedes
            messageServers
            sourceRemovedRepresentative.name
            sourceEligibleRepresentative.name :=
        hRemovedEarlier.2

      unfold
        DirectLFStrictPriorityPrecedes
        at hStrict

      rw [
        hRepresentativeNames
      ] at hStrict

      exact
        False.elim
          (hStrict.2
            hStrict.1)

    · have hStrict :
          DirectLFStrictPriorityPrecedes
            messageServers
            sourceEligibleRepresentative.name
            sourceRemovedRepresentative.name :=
        hEligibleEarlier.2

      unfold
        DirectLFStrictPriorityPrecedes
        at hStrict

      rw [
        hRepresentativeNames
      ] at hStrict

      exact
        False.elim
          (hStrict.2
            hStrict.1)

  have hTargetTag :
      targetRemoved.tag =
        targetEligible.tag :=
    LF.Tag.eq_of_time_eq_of_microstep
      hTargetTime
      hTargetMicrostep

  have hTargetRemovedEligible :
      LF.IsReactionPriorityEligible
        (Translation.compileMessageReactions
          messageServers)
        targetRemoved
        targetQueue := by

    refine
      ⟨?_,
       ?_⟩

    · intro targetCandidate
      intro hTargetCandidate

      have hEligibleTagOrder :
          LF.Tag.PrecedesOrEqual
            targetEligible.tag
            targetCandidate.tag :=
        hTargetEligible.1
          targetCandidate
          hTargetCandidate

      rw [
        hTargetTag
      ]

      exact hEligibleTagOrder

    · intro targetCandidate
      intro hTargetCandidate
      intro hCandidateSameRemovedTag

      have hCandidateSameEligibleTag :
          targetCandidate.tag =
            targetEligible.tag :=
        hCandidateSameRemovedTag.trans
          hTargetTag

      have hEligibleReactionOrder :
          LF.ReactionActionPrecedesOrEqual
            targetEligible.name
            targetCandidate.name
            (Translation.compileMessageReactions
              messageServers) :=
        hTargetEligible.2
          targetCandidate
          hTargetCandidate
          hCandidateSameEligibleTag

      rw [
        hTargetName
      ]

      exact hEligibleReactionOrder

  exact
    ⟨targetRemoved,
     targetRemaining,
     hTargetRemoved,
     hRemovedCorresponds,
     hTargetRemovedEligible,
     hRemainingCompatible⟩

/--
Synchronize target occurrence removal with source priority eligibility.

The source value recovered from occurrence removal and the source value
recovered from eligibility transport both correspond to the same selected LF
action. They therefore have the same source name and arrival time.

DTR priority eligibility is insensitive to payload and transfers directly.
-/
theorem directLF_targetDispatchSelection
    {messageServers :
      List DTR.MessageServer}
    {sourceQueue :
      DTR.MessageBag}
    {targetQueue targetRemaining :
      LF.ActionQueue}
    {targetSelected :
      LF.PendingAction}
    (hCompatible :
      DirectLFSelectionCompatible
        messageServers
        sourceQueue
        targetQueue)
    (hRemoved :
      Occurrence.RemovesOne
        targetSelected
        targetQueue
        targetRemaining)
    (hEligible :
      LF.IsReactionPriorityEligible
        (Translation.compileMessageReactions
          messageServers)
        targetSelected
        targetQueue) :
    ∃ sourceSelected sourceRemaining,
      Occurrence.RemovesOne
          sourceSelected
          sourceQueue
          sourceRemaining ∧
        PendingCorresponds
          sourceSelected
          targetSelected ∧
        DTR.IsPriorityEligible
          messageServers
          sourceSelected
          sourceQueue ∧
        DirectLFSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  have hTargetSelected :
      targetSelected ∈
        targetQueue :=
    Occurrence.RemovesOne.selected_mem
      hRemoved

  obtain
    ⟨sourceRemoved,
     sourceRemaining,
     hSourceRemoved,
     hRemovedCorresponds,
     hRemainingCompatible⟩ :=
      DirectLFSelectionCompatible.remove_target
        hCompatible
        hRemoved

  obtain
    ⟨sourceEligible,
     _hSourceEligibleMember,
     hEligibleCorresponds,
     hSourceEligible⟩ :=
      directLF_targetReactionPriorityEligible_implies_exists_sourcePriorityEligible
        hCompatible
        hTargetSelected
        hEligible

  have hSourceName :
      sourceRemoved.name =
        sourceEligible.name :=
    pendingCorresponds_sourceName_eq_of_sameTarget
      hRemovedCorresponds
      hEligibleCorresponds

  have hSourceTime :
      sourceRemoved.arrivalTime =
        sourceEligible.arrivalTime :=
    pendingCorresponds_sourceTime_eq_of_sameTarget
      hRemovedCorresponds
      hEligibleCorresponds

  have hSourceRemovedEligible :
      DTR.IsPriorityEligible
        messageServers
        sourceRemoved
        sourceQueue := by

    simpa [
      DTR.IsPriorityEligible,
      DTR.IsEarliest,
      hSourceName,
      hSourceTime
    ] using
      hSourceEligible

  exact
    ⟨sourceRemoved,
     sourceRemaining,
     hSourceRemoved,
     hRemovedCorresponds,
     hSourceRemovedEligible,
     hRemainingCompatible⟩

end Correctness
end Relico
