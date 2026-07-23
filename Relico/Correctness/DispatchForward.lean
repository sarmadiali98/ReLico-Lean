import Relico.Correctness.Dispatch

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Removing one source occurrence from corresponding queues identifies the
target occurrence at the same list position.

The residual queues continue to correspond.
-/
theorem QueueCorresponds.remove_source
    {sourceQueue sourceRemaining : DTR.MessageBag}
    {targetQueue : LF.ActionQueue}
    {selectedMessage : DTR.PendingMessage}
    (hQueues :
      QueueCorresponds
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
      PendingCorresponds
          selectedMessage
          selectedAction ∧
      QueueCorresponds
          sourceRemaining
          targetRemaining := by

  induction hRemove generalizing targetQueue with

  | head sourceRemaining =>
      cases hQueues with

      | cons headCorresponds tailCorresponds =>
          exact
            ⟨_,
             _,
             Occurrence.RemovesOne.head _,
             headCorresponds,
             tailCorresponds⟩

  | tail sourceHead hTail inductionHypothesis =>
      cases hQueues with

      | cons headCorresponds tailCorresponds =>
          rcases
              inductionHypothesis
                tailCorresponds
            with
              ⟨selectedAction,
               targetRemaining,
               hTargetRemove,
               hSelectedCorresponds,
               hRemainingCorresponds⟩

          exact
            ⟨selectedAction,
             _,
             Occurrence.RemovesOne.tail
               _
               hTargetRemove,
             hSelectedCorresponds,
             QueueCorresponds.cons
               headCorresponds
               hRemainingCorresponds⟩

/--
Compatibility condition required for forward dispatch simulation.

The selected source occurrence must have an aligned target occurrence
that is eligible under the more precise LF scheduler.
-/
def ForwardDispatchCompatible
    (selectedMessage : DTR.PendingMessage)
    (sourceRemaining : DTR.MessageBag)
    (targetState : LF.State) :
    Prop :=
  ∃ selectedAction targetRemaining,
    Occurrence.RemovesOne
        selectedAction
        targetState.pendingActions
        targetRemaining ∧
    PendingCorresponds
        selectedMessage
        selectedAction ∧
    QueueCorresponds
        sourceRemaining
        targetRemaining ∧
    LF.IsEarliest
        selectedAction
        targetState.pendingActions ∧
    LF.Tag.PrecedesOrEqual
        targetState.currentTag
        selectedAction.tag

/--
Conditional forward simulation for one dispatch transition.

A DTR dispatch has a matching LF dispatch when the corresponding target
occurrence is LF-earliest and does not precede the current LF tag.

These premises are necessary because DTR exposes logical time only,
whereas LF also orders equal-time actions by microstep.
-/
theorem dispatch_forward_of_compatible
    {model : DTR.Model}
    {sourceState sourceStateAfter : DTR.State}
    {selectedMessage : DTR.PendingMessage}
    {targetState : LF.State}
    (hSourceDispatch :
      DTR.DispatchStep
        model
        sourceState
        selectedMessage
        sourceStateAfter)
    (hStates :
      StateCorresponds
        sourceState
        targetState)
    (hCompatible :
      ForwardDispatchCompatible
        selectedMessage
        sourceStateAfter.pendingMessages
        targetState) :
    ∃ selectedAction targetStateAfter,
      LF.DispatchStep
          (Translation.translateCore model)
          targetState
          selectedAction
          targetStateAfter ∧
      PendingCorresponds
          selectedMessage
          selectedAction ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by

  cases hSourceDispatch with

  | fire
      currentTime
      sourceStateValue
      pendingMessages
      remainingMessages
      selectedMessage
      hSourceRemoved
      hSourceEarliest
      hSourceNotPast
      hSourceTarget =>

      cases targetState with

      | mk
          currentTag
          targetStateValue
          pendingActions
          targetBody =>

          have hStateValue :
              targetStateValue =
                sourceStateValue := by
            simpa using hStates.stateValue

          have hTargetBodyEmpty :
              targetBody = [] := by
            simpa [
              Translation.compileBody
            ] using hStates.activeBody

          change
            ∃ selectedAction targetRemaining,
              Occurrence.RemovesOne
                  selectedAction
                  pendingActions
                  targetRemaining ∧
              PendingCorresponds
                  selectedMessage
                  selectedAction ∧
              QueueCorresponds
                  remainingMessages
                  targetRemaining ∧
              LF.IsEarliest
                  selectedAction
                  pendingActions ∧
              LF.Tag.PrecedesOrEqual
                  currentTag
                  selectedAction.tag
            at hCompatible

          rcases hCompatible with
            ⟨selectedAction,
             targetRemaining,
             hTargetRemoved,
             hSelectedCorresponds,
             hRemainingCorresponds,
             hTargetEarliest,
             hTargetNotPast⟩

          subst targetStateValue
          subst targetBody

          have hGeneratedTarget :
              selectedAction.name =
                (Translation.translateCore model).reactor.logicalAction := by

            calc
              selectedAction.name
                  =
                Translation.actionNameFor
                  selectedMessage.name :=
                    hSelectedCorresponds.actionName

              _ =
                Translation.actionNameFor model.reactiveClass.messageServer.name := by
                      rw [hSourceTarget]

              _ =
                (Translation.translateCore model).reactor.logicalAction := by
                    rfl

          refine
            ⟨selectedAction,
             {
               currentTag :=
                 selectedAction.tag
               stateValue :=
                 sourceStateValue
               pendingActions :=
                 targetRemaining
               activeBody :=
                 (Translation.translateCore model).reactor.messageReaction.body
             },
             ?_,
             hSelectedCorresponds,
             ?_⟩

          · exact
              LF.DispatchStep.fire
                (program :=
                  Translation.translateCore model)
                (currentTag := currentTag)
                (stateValue := sourceStateValue)
                (pendingActions := pendingActions)
                (remainingActions :=
                  targetRemaining)
                (selectedAction :=
                  selectedAction)
                hTargetRemoved
                hTargetEarliest
                hTargetNotPast
                hGeneratedTarget

          · exact {
              currentTime :=
                hSelectedCorresponds.logicalTime

              stateValue :=
                rfl

              pendingEvents :=
                hRemainingCorresponds

              activeBody :=
                rfl
            }

end Correctness
end Relico
