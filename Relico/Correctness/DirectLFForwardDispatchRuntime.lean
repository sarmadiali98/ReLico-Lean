/-
Copyright (c) 2026.

Ordinary forward dispatch simulation for the direct DTR-to-generated-LF
translation.

A concrete DTR dispatch is matched by a concrete generated-LF dispatch of the
compiled message reaction.

The proof synchronizes:

- source and target one-occurrence removal;
- DTR and LF scheduler eligibility;
- generated reaction declaration and trigger;
- residual selection compatibility;
- ordinary LF pending-not-past scheduler consistency.

No source-side microstep, ghost state, restricted source semantics, or
positive-delay-only condition is introduced.
-/

import Relico.Correctness.DirectLFDispatchSelection
import Relico.Correctness.DirectLFRuntimeStateCorrespondence
import Relico.DTR.MultiStoreDispatchSemantics
import Relico.LF.MultiStoreDispatchSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness
/--
One ordinary DTR multiple-message-server dispatch constructs the matching
ordinary generated-LF dispatch.

The proof performs the following operations:

1. synchronize the concrete source removal with one concrete generated-LF
   removal that is reaction-priority eligible;
2. obtain complete-tag admissibility from the LF pending-not-past invariant;
3. activate the reaction compiled from the selected DTR message server;
4. preserve structural correspondence for the residual source bag and LF
   action queue;
5. establish pending-not-past for the resulting LF state.

No source-side microstep or restricted source semantics is used.
-/
theorem directLF_multiStore_dispatch_forward_runtime
    {messageServers :
      List DTR.MessageServer}
    {sourceState sourceStateAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    {targetState :
      LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceState
        selectedMessage
        selectedServer
        sourceStateAfter)
    (hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedAction targetStateAfter,
      LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetState
          selectedAction
          (Translation.compileMessageReaction
            selectedServer)
          targetStateAfter ∧
        PendingCorresponds
          selectedMessage
          selectedAction ∧
        DirectLFRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter := by

  cases hSourceDispatch with

  | fire
      currentTime
      stateStore
      pendingMessages
      remainingMessages
      selectedMessage
      selectedServer
      hServerDeclared
      hSourceRemoved
      hSourceEligible
      _hSourceNotPast
      hSourceTarget =>

      obtain
        ⟨selectedAction,
         targetRemaining,
         hTargetRemoved,
         hSelectedCorresponds,
         hTargetEligible,
         hRemainingCompatible⟩ :=
          directLF_sourceDispatchSelection
            hRuntime.selectionCompatible
            hSourceRemoved
            hSourceEligible

      have hTargetSelected :
          selectedAction ∈
            targetState.pendingActions :=
        Occurrence.RemovesOne.selected_mem
          hTargetRemoved

      have hTargetNotPast :
          LF.Tag.PrecedesOrEqual
            targetState.currentTag
            selectedAction.tag :=
        hRuntime.pendingNotPast.action
          hTargetSelected

      have hReactionDeclared :
          Translation.compileMessageReaction
                selectedServer ∈
            Translation.compileMessageReactions
              messageServers :=
        Translation.compileMessageReaction_mem
          hServerDeclared

      have hTargetActionName :
          Translation.actionNameFor
              selectedServer.name =
            selectedAction.name := by

        calc
          Translation.actionNameFor
                selectedServer.name =
              Translation.actionNameFor
                selectedMessage.name :=
            congrArg
              Translation.actionNameFor
              hSourceTarget.symm

          _ =
              selectedAction.name :=
            hSelectedCorresponds.actionName.symm

      have hReactionTrigger :
          (Translation.compileMessageReaction
              selectedServer).trigger =
            LF.Trigger.logicalAction
              selectedAction.name := by

        change
          LF.Trigger.logicalAction
              (Translation.actionNameFor
                selectedServer.name) =
            LF.Trigger.logicalAction
              selectedAction.name

        exact
          congrArg
            LF.Trigger.logicalAction
            hTargetActionName

      have hTargetBodyEmpty :
          targetState.activeBody =
            [] := by

        simpa [
          Translation.compileBody
        ] using
          hRuntime.states.activeBody

      cases targetState with

      | mk
          currentTag
          targetStore
          pendingActions
          targetActiveBody =>

          change
            targetActiveBody =
              []
            at hTargetBodyEmpty

          subst targetActiveBody

          let targetStateAfter :
              LF.StoreState := {
            currentTag :=
              selectedAction.tag

            stateStore :=
              targetStore

            pendingActions :=
              targetRemaining

            activeBody :=
              (Translation.compileMessageReaction
                selectedServer).body
          }

          have hTargetDispatch :
              LF.MultiStoreDispatchStep
                (Translation.compileMessageReactions
                  messageServers)
                {
                  currentTag :=
                    currentTag

                  stateStore :=
                    targetStore

                  pendingActions :=
                    pendingActions

                  activeBody :=
                    []
                }
                selectedAction
                (Translation.compileMessageReaction
                  selectedServer)
                targetStateAfter := by

            simpa [
              targetStateAfter
            ] using
              (LF.MultiStoreDispatchStep.fire
                (messageReactions :=
                  Translation.compileMessageReactions
                    messageServers)
                (currentTag :=
                  currentTag)
                (stateStore :=
                  targetStore)
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
                hTargetEligible
                hTargetNotPast
                hReactionTrigger)

          refine
            ⟨selectedAction,
             targetStateAfter,
             hTargetDispatch,
             hSelectedCorresponds,
             ?_⟩

          exact {
            states := {
              currentTime := by
                change
                  selectedAction.tag.time =
                    selectedMessage.arrivalTime

                exact
                  hSelectedCorresponds.logicalTime

              stateStore := by
                change
                  targetStore =
                    stateStore

                simpa using
                  hRuntime.states.stateStore

              pendingEvents := by
                change
                  DirectLFSelectionCompatible
                    messageServers
                    remainingMessages
                    targetRemaining

                exact
                  hRemainingCompatible

              activeBody := by
                change
                  (Translation.compileMessageReaction
                      selectedServer).body =
                    Translation.compileBody
                      selectedServer.body

                rfl
            }

            pendingNotPast :=
              LF.MultiStoreDispatchStep.establishes_pendingNotPast
                hTargetDispatch
          }

end Correctness
end Relico
