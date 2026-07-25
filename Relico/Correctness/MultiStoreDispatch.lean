import Relico.Correctness.StoreDispatch
import Relico.DTR.MultiStoreDispatchSemantics
import Relico.LF.MultiStoreDispatchSemantics
import Relico.Translation.MultiStoreBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Conditional forward simulation for one multiple-message-server
dispatch.

The selected source server is translated to the exact generated
reaction loaded by the matching LF logical-action dispatch.
-/
theorem multiStore_dispatch_forward_of_compatible
    {messageServers : List DTR.MessageServer}
    {sourceState sourceStateAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {targetState : LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceState
        selectedMessage
        selectedServer
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
    ∃ selectedAction targetReaction targetStateAfter,
      LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetState
          selectedAction
          targetReaction
          targetStateAfter ∧
      targetReaction =
        Translation.compileMessageReaction
          selectedServer ∧
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
      selectedServer
      hServerDeclared
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
                  selectedServer.name := by

            calc
              selectedAction.name
                  =
                Translation.actionNameFor
                  selectedMessage.name :=
                    hSelectedCorresponds.actionName

              _ =
                Translation.actionNameFor
                  selectedServer.name := by
                    rw [hSourceTarget]

          have hReactionDeclared :
              Translation.compileMessageReaction
                  selectedServer ∈
                Translation.compileMessageReactions
                  messageServers := by

            exact
              Translation.compileMessageReaction_mem
                hServerDeclared

          have hReactionTrigger :
              (Translation.compileMessageReaction
                selectedServer).trigger =
                LF.Trigger.logicalAction
                  selectedAction.name := by

            simp [
              Translation.compileMessageReaction,
              hGeneratedTarget
            ]

          let targetStateAfter :
              LF.StoreState := {
            currentTag :=
              selectedAction.tag

            stateStore :=
              sourceStore

            pendingActions :=
              targetRemaining

            activeBody :=
              (Translation.compileMessageReaction
                selectedServer).body
          }

          refine
            ⟨selectedAction,
             Translation.compileMessageReaction
               selectedServer,
             targetStateAfter,
             ?_,
             rfl,
             hSelectedCorresponds,
             ?_⟩

          · exact
              LF.MultiStoreDispatchStep.fire
                (messageReactions :=
                  Translation.compileMessageReactions
                    messageServers)
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
                (selectedReaction :=
                  Translation.compileMessageReaction
                    selectedServer)
                hReactionDeclared
                hTargetRemoved
                hTargetEarliest
                hTargetNotPast
                hReactionTrigger

          · exact {
              currentTime :=
                hSelectedCorresponds.logicalTime

              stateStore :=
                rfl

              pendingEvents :=
                hRemainingCorresponds

              activeBody := by
                rfl
            }

/--
Backward simulation for one dispatch of a generated reaction.

Membership in the compiled reaction list identifies the exact source
message server. Injectivity of generated action names then establishes
that the recovered source pending message targets that server.
-/
theorem multiStore_dispatch_backward
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState targetStateAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hTargetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetState
        selectedAction
        selectedReaction
        targetStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState) :
    ∃ selectedMessage sourceServer sourceStateAfter,
      DTR.MultiStoreDispatchStep
          messageServers
          sourceState
          selectedMessage
          sourceServer
          sourceStateAfter ∧
      selectedReaction =
        Translation.compileMessageReaction
          sourceServer ∧
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
      selectedReaction
      hReactionDeclared
      hTargetRemoved
      hTargetEarliest
      hTargetNotPast
      hTrigger =>

      rcases
          Translation.mem_compileMessageReactions
            hReactionDeclared
        with
          ⟨sourceServer,
           hSourceServerDeclared,
           hCompiledReaction⟩

      subst selectedReaction

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

          have hTargetActionName :
              selectedAction.name =
                Translation.actionNameFor
                  sourceServer.name := by

            have hTriggerName :
                Translation.actionNameFor
                    sourceServer.name =
                  selectedAction.name := by

              simpa [
                Translation.compileMessageReaction
              ] using
                hTrigger

            exact hTriggerName.symm

          have hSourceTarget :
              selectedMessage.name =
                sourceServer.name := by

            apply
              Translation.actionNameFor_injective

            exact
              hSelectedCorresponds.actionName.symm.trans
                hTargetActionName

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
              sourceServer.body
          }

          refine
            ⟨selectedMessage,
             sourceServer,
             sourceStateAfter,
             ?_,
             rfl,
             hSelectedCorresponds,
             ?_⟩

          · exact
              DTR.MultiStoreDispatchStep.fire
                (messageServers :=
                  messageServers)
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
                (selectedServer :=
                  sourceServer)
                hSourceServerDeclared
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

              activeBody := by
                rfl
            }

end Correctness
end Relico
