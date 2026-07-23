import Relico.Correctness.DispatchForward
import Relico.Correctness.StoreForward
import Relico.DTR.StoreDispatchSemantics
import Relico.LF.StoreDispatchSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compatibility required for forward store-dispatch simulation.

The source-selected occurrence must have an aligned target occurrence
that is removable, LF-earliest, and not before the current LF tag.
-/
def StoreForwardDispatchCompatible
    (selectedMessage : DTR.PendingMessage)
    (sourceRemaining : DTR.MessageBag)
    (targetState : LF.StoreState) :
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
Conditional forward simulation for one store-based dispatch.

The full finite state store is preserved. The condition is necessary
because LF microsteps refine equal-logical-time source choices.
-/
theorem store_dispatch_forward_of_compatible
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {sourceState sourceStateAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {targetState : LF.StoreState}
    (hSourceDispatch :
      DTR.StoreDispatchStep
        messageServer
        messageBody
        sourceState
        selectedMessage
        sourceStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState)
    (hCompatible :
      StoreForwardDispatchCompatible
        selectedMessage
        sourceStateAfter.pendingMessages
        targetState) :
    ∃ selectedAction targetStateAfter,
      LF.StoreDispatchStep
          (Translation.actionNameFor
            messageServer)
          (Translation.compileBody
            messageBody)
          targetState
          selectedAction
          targetStateAfter ∧
      PendingCorresponds
        selectedMessage
        selectedAction ∧
      StoreStateCorresponds
        sourceStateAfter
        targetStateAfter := by

  cases hSourceDispatch with

  | fire
      currentTime
      sourceStore
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
          targetStore
          pendingActions
          targetBody =>

          have hStore :
              targetStore =
                sourceStore := by
            simpa using
              hStates.stateStore

          have hTargetBodyEmpty :
              targetBody =
                [] := by
            simpa [
              Translation.compileBody
            ] using
              hStates.activeBody

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

          subst targetStore
          subst targetBody

          have hGeneratedTarget :
              selectedAction.name =
                Translation.actionNameFor
                  messageServer := by

            calc
              selectedAction.name
                  =
                Translation.actionNameFor
                  selectedMessage.name :=
                    hSelectedCorresponds.actionName

              _ =
                Translation.actionNameFor
                  messageServer := by
                    rw [hSourceTarget]

          let targetStateAfter :
              LF.StoreState := {
            currentTag :=
              selectedAction.tag

            stateStore :=
              sourceStore

            pendingActions :=
              targetRemaining

            activeBody :=
              Translation.compileBody
                messageBody
          }

          refine
            ⟨selectedAction,
             targetStateAfter,
             ?_,
             hSelectedCorresponds,
             ?_⟩

          · exact
              LF.StoreDispatchStep.fire
                (logicalAction :=
                  Translation.actionNameFor
                    messageServer)
                (messageReactionBody :=
                  Translation.compileBody
                    messageBody)
                (currentTag :=
                  currentTag)
                (stateStore :=
                  sourceStore)
                (pendingActions :=
                  pendingActions)
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

              stateStore :=
                rfl

              pendingEvents :=
                hRemainingCorresponds

              activeBody :=
                rfl
            }

/--
Unconditional backward simulation for one store-based dispatch.

Every generated-LF dispatch from corresponding states identifies a
matching source message occurrence. The source pending-target invariant
establishes that the recovered occurrence targets the declared message
server.
-/
theorem store_dispatch_backward
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {sourceState : DTR.StoreState}
    {targetState targetStateAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    (hTargetDispatch :
      LF.StoreDispatchStep
        (Translation.actionNameFor
          messageServer)
        (Translation.compileBody
          messageBody)
        targetState
        selectedAction
        targetStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState)
    (hPendingTargets :
      ∀ pendingMessage,
        pendingMessage ∈
          sourceState.pendingMessages →
        pendingMessage.name =
          messageServer) :
    ∃ selectedMessage sourceStateAfter,
      DTR.StoreDispatchStep
          messageServer
          messageBody
          sourceState
          selectedMessage
          sourceStateAfter ∧
      PendingCorresponds
        selectedMessage
        selectedAction ∧
      StoreStateCorresponds
        sourceStateAfter
        targetStateAfter := by

  cases hTargetDispatch with

  | fire
      currentTag
      targetStore
      pendingActions
      remainingActions
      selectedAction
      hTargetRemoved
      hTargetEarliest
      hTargetNotPast
      hTargetName =>

      cases sourceState with

      | mk
          sourceTime
          sourceStore
          pendingMessages
          sourceActiveBody =>

          have hCurrentTime :
              currentTag.time =
                sourceTime := by
            simpa using
              hStates.currentTime

          have hStore :
              targetStore =
                sourceStore := by
            simpa using
              hStates.stateStore

          have hQueues :
              QueueCorresponds
                pendingMessages
                pendingActions := by
            simpa using
              hStates.pendingEvents

          have hCompiledEmpty :
              Translation.compileBody
                  sourceActiveBody =
                [] := by
            simpa using
              hStates.activeBody.symm

          have hSourceBodyEmpty :
              sourceActiveBody =
                [] := by

            cases sourceActiveBody with

            | nil =>
                rfl

            | cons statement remaining =>
                simp [
                  Translation.compileBody
                ] at hCompiledEmpty

          have hPendingTargets' :
              ∀ pendingMessage,
                pendingMessage ∈
                  pendingMessages →
                pendingMessage.name =
                  messageServer := by
            simpa using
              hPendingTargets

          rcases
              QueueCorresponds.remove_target
                hQueues
                hTargetRemoved
            with
              ⟨selectedMessage,
               sourceRemaining,
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
              hTargetEarliest

          have hSelectedMembership :
              selectedMessage ∈
                pendingMessages :=

            Occurrence.RemovesOne.selected_mem
              hSourceRemoved

          have hSourceTarget :
              selectedMessage.name =
                messageServer :=

            hPendingTargets'
              selectedMessage
              hSelectedMembership

          have hSourceNotPast :
              sourceTime ≤
                selectedMessage.arrivalTime := by

            have hTargetTimeOrder :
                currentTag.time ≤
                  selectedAction.tag.time :=

              LF.Tag.time_le_of_precedesOrEqual
                hTargetNotPast

            calc
              sourceTime
                  =
                currentTag.time :=
                  hCurrentTime.symm

              _ ≤
                selectedAction.tag.time :=
                  hTargetTimeOrder

              _ =
                selectedMessage.arrivalTime :=
                  hSelectedCorresponds.logicalTime

          subst targetStore
          subst sourceActiveBody

          let sourceStateAfter :
              DTR.StoreState := {
            currentTime :=
              selectedMessage.arrivalTime

            stateStore :=
              sourceStore

            pendingMessages :=
              sourceRemaining

            activeBody :=
              messageBody
          }

          refine
            ⟨selectedMessage,
             sourceStateAfter,
             ?_,
             hSelectedCorresponds,
             ?_⟩

          · exact
              DTR.StoreDispatchStep.fire
                (messageServer :=
                  messageServer)
                (messageBody :=
                  messageBody)
                (currentTime :=
                  sourceTime)
                (stateStore :=
                  sourceStore)
                (pendingMessages :=
                  pendingMessages)
                (remainingMessages :=
                  sourceRemaining)
                (selectedMessage :=
                  selectedMessage)
                hSourceRemoved
                hSourceEarliest
                hSourceNotPast
                hSourceTarget

          · exact {
              currentTime :=
                hSelectedCorresponds.logicalTime

              stateStore :=
                rfl

              pendingEvents :=
                hRemainingCorresponds

              activeBody :=
                rfl
            }

end Correctness
end Relico
