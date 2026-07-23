import Relico.Correctness.Correspondence
import Relico.DTR.DispatchSemantics
import Relico.DTR.RuntimeWellFormed
import Relico.LF.DispatchSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Removing one target occurrence from corresponding queues identifies
the source occurrence at the same list position.

The remaining source and target queues continue to correspond.
-/
theorem QueueCorresponds.remove_target
    {sourceQueue : DTR.MessageBag}
    {targetQueue targetRemaining : LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hQueues :
      QueueCorresponds
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
      PendingCorresponds
          selectedMessage
          selectedAction ∧
      QueueCorresponds
          sourceRemaining
          targetRemaining := by

  induction hRemove generalizing sourceQueue with

  | head targetRemaining =>
      cases hQueues with

      | cons headCorresponds tailCorresponds =>
          exact
            ⟨_,
             _,
             Occurrence.RemovesOne.head _,
             headCorresponds,
             tailCorresponds⟩

  | tail targetHead hTail inductionHypothesis =>
      cases hQueues with

      | cons headCorresponds tailCorresponds =>
          rcases
              inductionHypothesis
                tailCorresponds
            with
              ⟨selectedMessage,
               sourceRemaining,
               hSourceRemove,
               hSelectedCorresponds,
               hRemainingCorresponds⟩

          exact
            ⟨selectedMessage,
             _,
             Occurrence.RemovesOne.tail
               _
               hSourceRemove,
             hSelectedCorresponds,
             QueueCorresponds.cons
               headCorresponds
               hRemainingCorresponds⟩

/--
Every source occurrence in corresponding queues has a target
occurrence at the same list position.
-/
theorem QueueCorresponds.source_mem
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    (hQueues :
      QueueCorresponds
        sourceQueue
        targetQueue)
    {sourceMessage : DTR.PendingMessage}
    (hMembership :
      sourceMessage ∈ sourceQueue) :
    ∃ targetAction,
      targetAction ∈ targetQueue ∧
      PendingCorresponds
        sourceMessage
        targetAction := by

  induction hQueues with

  | nil =>
      simp at hMembership

  | cons headCorresponds tailCorresponds inductionHypothesis =>
      simp only [List.mem_cons] at hMembership

      rcases hMembership with
        hHead | hTail

      · subst sourceMessage

        exact
          ⟨_,
           by simp,
           headCorresponds⟩

      · rcases
            inductionHypothesis hTail
          with
            ⟨targetAction,
             hTargetMembership,
             hCorresponds⟩

        exact
          ⟨targetAction,
           by
             simp only [List.mem_cons]
             exact Or.inr hTargetMembership,
           hCorresponds⟩

/--
LF earliest-tag selection implies DTR earliest-logical-time selection
for the corresponding source occurrence.

The converse is intentionally not claimed because equal-time LF actions
may be ordered by different microsteps.
-/
theorem targetEarliest_implies_sourceEarliest
    {sourceQueue : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {sourceMessage : DTR.PendingMessage}
    {targetAction : LF.PendingAction}
    (hQueues :
      QueueCorresponds
        sourceQueue
        targetQueue)
    (hSelected :
      PendingCorresponds
        sourceMessage
        targetAction)
    (hTargetEarliest :
      LF.IsEarliest
        targetAction
        targetQueue) :
    DTR.IsEarliest
      sourceMessage
      sourceQueue := by

  intro candidate hCandidateMembership

  rcases
      QueueCorresponds.source_mem
        hQueues
        hCandidateMembership
    with
      ⟨targetCandidate,
       hTargetCandidateMembership,
       hCandidateCorresponds⟩

  have hTagOrder :
      LF.Tag.PrecedesOrEqual
        targetAction.tag
        targetCandidate.tag :=
    hTargetEarliest
      targetCandidate
      hTargetCandidateMembership

  have hTimeOrder :
      targetAction.tag.time ≤
        targetCandidate.tag.time :=
    LF.Tag.time_le_of_precedesOrEqual
      hTagOrder

  calc
    sourceMessage.arrivalTime
        =
      targetAction.tag.time := by
        exact hSelected.logicalTime.symm

    _ ≤
      targetCandidate.tag.time :=
        hTimeOrder

    _ =
      candidate.arrivalTime := by
        exact hCandidateCorresponds.logicalTime

/--
Backward simulation for one dispatch transition.

Every generated-LF dispatch from a corresponding state identifies a
source message occurrence that DTR may dispatch. The selected events and
resulting states correspond.
-/
theorem dispatch_backward
    {model : DTR.Model}
    {sourceState : DTR.State}
    {targetState targetStateAfter : LF.State}
    {selectedAction : LF.PendingAction}
    (hTargetDispatch :
      LF.DispatchStep
        (Translation.translateCore model)
        targetState
        selectedAction
        targetStateAfter)
    (hStates :
      StateCorresponds
        sourceState
        targetState)
    (hSourceWellFormed :
      DTR.State.WellFormed
        model
        sourceState) :
    ∃ selectedMessage sourceStateAfter,
      DTR.DispatchStep
          model
          sourceState
          selectedMessage
          sourceStateAfter ∧
      PendingCorresponds
          selectedMessage
          selectedAction ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by

  cases hTargetDispatch with

  | fire
      currentTag
      targetStateValue
      pendingActions
      remainingActions
      selectedAction
      hRemoved
      hEarliest
      hNotPast
      hTarget =>

      cases sourceState with

      | mk
          sourceTime
          sourceStateValue
          pendingMessages
          sourceBody =>

          have hCurrentTime :
              currentTag.time =
                sourceTime := by
            simpa using hStates.currentTime

          have hStateValue :
              targetStateValue =
                sourceStateValue := by
            simpa using hStates.stateValue

          have hQueues :
              QueueCorresponds
                pendingMessages
                pendingActions := by
            simpa using hStates.pendingEvents

          have hCompiledEmpty :
              Translation.compileBody
                  sourceBody =
                [] := by
            simpa using hStates.activeBody.symm

          have hSourceBodyEmpty :
              sourceBody = [] := by
            cases sourceBody with

            | nil =>
                rfl

            | cons sourceStatement sourceRemaining =>
                simp [
                  Translation.compileBody
                ] at hCompiledEmpty

          subst sourceBody

          rcases
              QueueCorresponds.remove_target
                hQueues
                hRemoved
            with
              ⟨selectedMessage,
               remainingMessages,
               hSourceRemoved,
               hSelectedCorresponds,
               hRemainingCorresponds⟩

          have hSourceEarliest :
              DTR.IsEarliest
                selectedMessage
                pendingMessages :=
            targetEarliest_implies_sourceEarliest
              hQueues
              hSelectedCorresponds
              hEarliest

          have hSelectedMembership :
              selectedMessage ∈
                pendingMessages :=
            Occurrence.RemovesOne.selected_mem
              hSourceRemoved

          have hSourceTarget :
              selectedMessage.name =
                model.reactiveClass.messageServer.name :=
            hSourceWellFormed.pendingMessagesWellFormed
              selectedMessage
              hSelectedMembership

          have hSourceNotPast :
              sourceTime ≤
                selectedMessage.arrivalTime := by

            have hTargetTimeOrder :
                currentTag.time ≤
                  selectedAction.tag.time :=
              LF.Tag.time_le_of_precedesOrEqual
                hNotPast

            calc
              sourceTime
                  =
                currentTag.time := by
                  exact hCurrentTime.symm

              _ ≤
                selectedAction.tag.time :=
                  hTargetTimeOrder

              _ =
                selectedMessage.arrivalTime := by
                  exact
                    hSelectedCorresponds.logicalTime

          refine
            ⟨selectedMessage,
             {
               currentTime :=
                 selectedMessage.arrivalTime
               stateValue :=
                 sourceStateValue
               pendingMessages :=
                 remainingMessages
               activeBody :=
                 model.reactiveClass.messageServer.body
             },
             ?_,
             hSelectedCorresponds,
             ?_⟩

          · exact
              DTR.DispatchStep.fire
                (model := model)
                (currentTime := sourceTime)
                (stateValue := sourceStateValue)
                (pendingMessages := pendingMessages)
                (remainingMessages :=
                  remainingMessages)
                (selectedMessage :=
                  selectedMessage)
                hSourceRemoved
                hSourceEarliest
                hSourceNotPast
                hSourceTarget

          · refine {
              currentTime :=
                hSelectedCorresponds.logicalTime

              stateValue :=
                hStateValue

              pendingEvents :=
                hRemainingCorresponds

              activeBody := ?_
            }

            rfl

end Correctness
end Relico
