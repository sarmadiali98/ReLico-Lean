/-
Copyright (c) 2026.

Payload-aware occurrence-sensitive dispatch-selection transport for the
direct DTR-to-LF translation.

The selected source and target occurrences are paired through the same
payload-aware representative alignment used by removal. Scheduler eligibility
is then transferred without inspecting payloads.
-/

import Relico.Correctness.DirectLFPayloadSelectionRemoval
import Relico.Correctness.DirectLFDispatchSelection

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Two target actions in a selection-compatible LF action queue that both
correspond to one source message have equal complete tags.

The metric-time components follow from occurrence correspondence. Selection
compatibility rules out unequal microsteps because that would require a
strict source-priority cycle for equal source names.
-/
theorem directLF_targetTag_eq_of_sameSource
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {sourceMessage : DTR.PendingMessage}
    {targetLeft targetRight : LF.PendingAction}
    (hCompatible :
      DirectLFSelectionCompatible
        messageServers
        sourceBag
        targetQueue)
    (hLeftMember :
      targetLeft ∈ targetQueue)
    (hRightMember :
      targetRight ∈ targetQueue)
    (hLeft :
      PendingCorresponds
        sourceMessage
        targetLeft)
    (hRight :
      PendingCorresponds
        sourceMessage
        targetRight) :
    targetLeft.tag =
      targetRight.tag := by

  have hTargetTime :
      targetLeft.tag.time =
        targetRight.tag.time :=
    pendingCorresponds_targetTime_eq_of_sameSource
      hLeft
      hRight

  rcases hCompatible with
    ⟨sourceRepresentative,
     targetRepresentative,
     _hSourcePermutation,
     hTargetPermutation,
     hOrdered⟩

  have hLeftRepresentative :
      targetLeft ∈ targetRepresentative :=
    (List.Perm.mem_iff
      hTargetPermutation).mp
        hLeftMember

  have hRightRepresentative :
      targetRight ∈ targetRepresentative :=
    (List.Perm.mem_iff
      hTargetPermutation).mp
        hRightMember

  obtain
    ⟨sourceLeft,
     hLeftAligned⟩ :=
      directLFAlignedOccurrence_of_target_mem
        hOrdered.queues
        hLeftRepresentative

  obtain
    ⟨sourceRight,
     hRightAligned⟩ :=
      directLFAlignedOccurrence_of_target_mem
        hOrdered.queues
        hRightRepresentative

  have hLeftRepresentativeCorresponds :
      PendingCorresponds
        sourceLeft
        targetLeft :=
    hLeftAligned.pendingCorresponds

  have hRightRepresentativeCorresponds :
      PendingCorresponds
        sourceRight
        targetRight :=
    hRightAligned.pendingCorresponds

  have hLeftSourceName :
      sourceLeft.name =
        sourceMessage.name :=
    pendingCorresponds_sourceName_eq_of_sameTarget
      hLeftRepresentativeCorresponds
      hLeft

  have hRightSourceName :
      sourceRight.name =
        sourceMessage.name :=
    pendingCorresponds_sourceName_eq_of_sameTarget
      hRightRepresentativeCorresponds
      hRight

  have hRepresentativeNames :
      sourceLeft.name =
        sourceRight.name :=
    hLeftSourceName.trans
      hRightSourceName.symm

  have hLeftSourceTime :
      sourceLeft.arrivalTime =
        sourceMessage.arrivalTime :=
    pendingCorresponds_sourceTime_eq_of_sameTarget
      hLeftRepresentativeCorresponds
      hLeft

  have hRightSourceTime :
      sourceRight.arrivalTime =
        sourceMessage.arrivalTime :=
    pendingCorresponds_sourceTime_eq_of_sameTarget
      hRightRepresentativeCorresponds
      hRight

  have hRepresentativeTimes :
      sourceLeft.arrivalTime =
        sourceRight.arrivalTime :=
    hLeftSourceTime.trans
      hRightSourceTime.symm

  have hPairCompatible :
      DirectLFPairSelectionCompatible
        messageServers
        sourceLeft
        sourceRight
        targetLeft
        targetRight :=
    hOrdered.pairwise
      hLeftAligned
      hRightAligned

  have hTargetMicrostep :
      targetLeft.tag.microstep =
        targetRight.tag.microstep := by

    rcases hPairCompatible.2.2 with
      hDifferentTime |
      hSameMicrostep |
      hLeftEarlier |
      hRightEarlier

    · exact
        False.elim
          (hDifferentTime
            hRepresentativeTimes)

    · exact
        hSameMicrostep

    · have hStrict :
          DirectLFStrictPriorityPrecedes
            messageServers
            sourceLeft.name
            sourceRight.name :=
        hLeftEarlier.2

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
            sourceRight.name
            sourceLeft.name :=
        hRightEarlier.2

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

  exact
    LF.Tag.eq_of_time_eq_of_microstep
      hTargetTime
      hTargetMicrostep

/--
Transfer LF reaction-priority eligibility between two actions that correspond
to the same source message in one selection-compatible state.
-/
theorem directLF_reactionPriorityEligible_of_sameSource
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {sourceMessage : DTR.PendingMessage}
    {targetSelected targetEligible : LF.PendingAction}
    (hCompatible :
      DirectLFSelectionCompatible
        messageServers
        sourceBag
        targetQueue)
    (hSelectedMember :
      targetSelected ∈ targetQueue)
    (hEligibleMember :
      targetEligible ∈ targetQueue)
    (hSelectedCorresponds :
      PendingCorresponds
        sourceMessage
        targetSelected)
    (hEligibleCorresponds :
      PendingCorresponds
        sourceMessage
        targetEligible)
    (hEligible :
      LF.IsReactionPriorityEligible
        (Translation.compileMessageReactions
          messageServers)
        targetEligible
        targetQueue) :
    LF.IsReactionPriorityEligible
      (Translation.compileMessageReactions
        messageServers)
      targetSelected
      targetQueue := by

  have hTargetName :
      targetSelected.name =
        targetEligible.name :=
    pendingCorresponds_targetName_eq_of_sameSource
      hSelectedCorresponds
      hEligibleCorresponds

  have hTargetTag :
      targetSelected.tag =
        targetEligible.tag :=
    directLF_targetTag_eq_of_sameSource
      hCompatible
      hSelectedMember
      hEligibleMember
      hSelectedCorresponds
      hEligibleCorresponds

  refine
    ⟨?_,
     ?_⟩

  · intro candidate
    intro hCandidate

    have hTagOrder :
        LF.Tag.PrecedesOrEqual
          targetEligible.tag
          candidate.tag :=
      hEligible.1
        candidate
        hCandidate

    rw [
      hTargetTag
    ]

    exact hTagOrder

  · intro candidate
    intro hCandidate
    intro hCandidateSameSelectedTag

    have hCandidateSameEligibleTag :
        candidate.tag =
          targetEligible.tag :=
      hCandidateSameSelectedTag.trans
        hTargetTag

    have hReactionOrder :
        LF.ReactionActionPrecedesOrEqual
          targetEligible.name
          candidate.name
          (Translation.compileMessageReactions
            messageServers) :=
      hEligible.2
        candidate
        hCandidate
        hCandidateSameEligibleTag

    rw [
      hTargetName
    ]

    exact hReactionOrder

/--
Synchronize one source occurrence removal with exact payload correspondence,
LF reaction-priority eligibility, and payload-aware residual compatibility.
-/
theorem directLFPayload_sourceDispatchSelection
    {messageServers : List DTR.MessageServer}
    {sourceBag sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {sourceSelected : DTR.PendingMessage}
    (hCompatible :
      DirectLFPayloadSelectionCompatible
        messageServers
        sourceBag
        targetQueue)
    (hRemoved :
      Occurrence.RemovesOne
        sourceSelected
        sourceBag
        sourceRemaining)
    (hEligible :
      DTR.IsPriorityEligible
        messageServers
        sourceSelected
        sourceBag) :
    ∃ targetSelected targetRemaining,
      Occurrence.RemovesOne
          targetSelected
          targetQueue
          targetRemaining ∧
        PendingPayloadCorresponds
          sourceSelected
          targetSelected ∧
        LF.IsReactionPriorityEligible
          (Translation.compileMessageReactions
            messageServers)
          targetSelected
          targetQueue ∧
        DirectLFPayloadSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  have hBaseCompatible :
      DirectLFSelectionCompatible
        messageServers
        sourceBag
        targetQueue :=
    hCompatible.toSelectionCompatible

  have hSourceSelected :
      sourceSelected ∈ sourceBag :=
    Occurrence.RemovesOne.selected_mem
      hRemoved

  obtain
    ⟨targetSelected,
     targetRemaining,
     hTargetRemoved,
     hSelectedPayload,
     hRemainingCompatible⟩ :=
      DirectLFPayloadSelectionCompatible.remove_source
        hCompatible
        hRemoved

  obtain
    ⟨targetEligible,
     hTargetEligibleMember,
     hEligibleCorresponds,
     hTargetEligible⟩ :=
      directLF_sourcePriorityEligible_implies_exists_targetReactionPriorityEligible
        hBaseCompatible
        hSourceSelected
        hEligible

  have hTargetSelectedMember :
      targetSelected ∈ targetQueue :=
    Occurrence.RemovesOne.selected_mem
      hTargetRemoved

  have hTargetSelectedEligible :
      LF.IsReactionPriorityEligible
        (Translation.compileMessageReactions
          messageServers)
        targetSelected
        targetQueue :=
    directLF_reactionPriorityEligible_of_sameSource
      hBaseCompatible
      hTargetSelectedMember
      hTargetEligibleMember
      hSelectedPayload.occurrence
      hEligibleCorresponds
      hTargetEligible

  exact
    ⟨targetSelected,
     targetRemaining,
     hTargetRemoved,
     hSelectedPayload,
     hTargetSelectedEligible,
     hRemainingCompatible⟩

/--
Synchronize one target occurrence removal with exact payload correspondence,
DTR priority eligibility, and payload-aware residual compatibility.
-/
theorem directLFPayload_targetDispatchSelection
    {messageServers : List DTR.MessageServer}
    {sourceBag : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {targetSelected : LF.PendingAction}
    (hCompatible :
      DirectLFPayloadSelectionCompatible
        messageServers
        sourceBag
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
          sourceBag
          sourceRemaining ∧
        PendingPayloadCorresponds
          sourceSelected
          targetSelected ∧
        DTR.IsPriorityEligible
          messageServers
          sourceSelected
          sourceBag ∧
        DirectLFPayloadSelectionCompatible
          messageServers
          sourceRemaining
          targetRemaining := by

  have hBaseCompatible :
      DirectLFSelectionCompatible
        messageServers
        sourceBag
        targetQueue :=
    hCompatible.toSelectionCompatible

  have hTargetSelected :
      targetSelected ∈ targetQueue :=
    Occurrence.RemovesOne.selected_mem
      hRemoved

  obtain
    ⟨sourceSelected,
     sourceRemaining,
     hSourceRemoved,
     hSelectedPayload,
     hRemainingCompatible⟩ :=
      DirectLFPayloadSelectionCompatible.remove_target
        hCompatible
        hRemoved

  obtain
    ⟨sourceEligible,
     _hSourceEligibleMember,
     hEligibleCorresponds,
     hSourceEligible⟩ :=
      directLF_targetReactionPriorityEligible_implies_exists_sourcePriorityEligible
        hBaseCompatible
        hTargetSelected
        hEligible

  have hSourceName :
      sourceSelected.name =
        sourceEligible.name :=
    pendingCorresponds_sourceName_eq_of_sameTarget
      hSelectedPayload.occurrence
      hEligibleCorresponds

  have hSourceTime :
      sourceSelected.arrivalTime =
        sourceEligible.arrivalTime :=
    pendingCorresponds_sourceTime_eq_of_sameTarget
      hSelectedPayload.occurrence
      hEligibleCorresponds

  have hSourceSelectedEligible :
      DTR.IsPriorityEligible
        messageServers
        sourceSelected
        sourceBag := by

    simpa [
      DTR.IsPriorityEligible,
      DTR.IsEarliest,
      hSourceName,
      hSourceTime
    ] using
      hSourceEligible

  exact
    ⟨sourceSelected,
     sourceRemaining,
     hSourceRemoved,
     hSelectedPayload,
     hSourceSelectedEligible,
     hRemainingCompatible⟩

end Correctness
end Relico
