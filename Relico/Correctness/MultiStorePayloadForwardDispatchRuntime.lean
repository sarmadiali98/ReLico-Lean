import Relico.Correctness.MultiStorePayloadRuntimeDispatchSupport
import Relico.Correctness.MultiStorePayloadDispatchSelection
import Relico.LF.PendingNotPast

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
A payload-aware DTR dispatch has a matching generated LF dispatch and
preserves complete payload-aware runtime-state correspondence.

The runtime premise retains the explicit selection-compatibility boundary
needed to reconcile DTR priority selection with complete LF tags.
-/
theorem multiStorePayload_dispatch_forward_runtime
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState sourceStateAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetState :
      LF.MultiStorePayloadState}
    (hSourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceState
        selectedMessage
        selectedServer
        sourceStateAfter)
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedAction targetStateAfter,
      LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetState
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetStateAfter ∧
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        MultiStorePayloadRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter := by

  cases hSourceDispatch with

  | fire
      currentTime
      stateStore
      parameters
      pendingMessages
      remainingMessages
      selectedMessage
      selectedServer
      boundParameters
      hServerDeclared
      hSourceRemoved
      hSourceEligible
      _hSourceNotPast
      hSourceTarget
      hSourceBind =>

      obtain
        ⟨selectionAction,
         selectionRemaining,
         hSelectionRemoved,
         hSelectionCorresponds,
         hSelectionEligible,
         hSelectionRemaining⟩ :=
          multiStorePayload_sourceDispatchSelection
            hRuntime.selectionCompatible
            hSourceRemoved
            hSourceEligible

      obtain
        ⟨positionalAction,
         positionalRemaining,
         hPositionalRemoved,
         hPositionalCorresponds,
         hPositionalQueues⟩ :=
          PayloadQueueCorresponds.remove_source
            hRuntime.payloadQueues
            hSourceRemoved

      have hSelectionMember :
          selectionAction ∈
            targetState.pendingActions :=
        Occurrence.RemovesOne.selected_mem
          hSelectionRemoved

      have hPositionalMember :
          positionalAction ∈
            targetState.pendingActions :=
        Occurrence.RemovesOne.selected_mem
          hPositionalRemoved

      have hTargetTag :
          selectionAction.tag =
            positionalAction.tag :=
        multiStorePayloadBase_targetTag_eq_of_sameSource
          hRuntime.selectionCompatible.toSelectionCompatible
          hSelectionMember
          hPositionalMember
          hSelectionCorresponds.occurrence
          hPositionalCorresponds.occurrence

      have hTargetAction :
          selectionAction =
            positionalAction :=
        pendingPayloadCorresponds_target_eq_of_sameSource_and_tag
          hSelectionCorresponds
          hPositionalCorresponds
          hTargetTag

      subst positionalAction

      have hRemainingCompatible :
          MultiStorePayloadSelectionCompatible
            messageServers
            remainingMessages
            positionalRemaining :=
        multiStorePayload_forwardResidualSelectionMerge
          hSelectionRemoved
          hPositionalRemoved
          hSelectionRemaining

      have hTargetNotPast :
          LF.Tag.PrecedesOrEqual
            targetState.currentTag
            selectionAction.tag :=
        hRuntime.pendingActionNotPast
          hSelectionMember

      have hReactionDeclared :
          Translation.compileMultiStorePayloadReaction
                selectedServer ∈
            Translation.compileMultiStorePayloadMessageReactions
              messageServers :=
        Translation.compileMultiStorePayloadReaction_mem
          hServerDeclared

      have hTargetActionName :
          Translation.actionNameFor
              selectedServer.name =
            selectionAction.name := by

        calc
          Translation.actionNameFor
                selectedServer.name =
              Translation.actionNameFor
                selectedMessage.name :=
            congrArg
              Translation.actionNameFor
              hSourceTarget.symm

          _ =
              selectionAction.name :=
            hSelectionCorresponds.occurrence.actionName.symm

      have hReactionTrigger :
          (Translation.compileMultiStorePayloadReaction
              selectedServer).trigger =
            LF.MultiStorePayloadTrigger.logicalAction
              selectionAction.name := by

        change
          LF.MultiStorePayloadTrigger.logicalAction
              (Translation.actionNameFor
                selectedServer.name) =
            LF.MultiStorePayloadTrigger.logicalAction
              selectionAction.name

        exact
          congrArg
            LF.MultiStorePayloadTrigger.logicalAction
            hTargetActionName

      have hTargetBind :
          ParameterStore.bindPayload
              (Translation.compileMultiStorePayloadReaction
                selectedServer).parameters
              selectionAction.payload =
            some boundParameters := by

        simpa [
          Translation.compileMultiStorePayloadReaction,
          hSelectionCorresponds.payload
        ] using
          hSourceBind

      have hTargetBodyEmpty :
          targetState.activeBody =
            [] := by

        simpa [
          Translation.compileMultiStorePayloadBody
        ] using
          hRuntime.toStateCorresponds.activeBody

      cases targetState with

      | mk
          currentTag
          targetStore
          targetParameters
          pendingActions
          targetActiveBody =>

          change
            targetActiveBody =
              []
            at hTargetBodyEmpty

          subst targetActiveBody

          let targetStateAfter :
              LF.MultiStorePayloadState := {
            currentTag :=
              selectionAction.tag

            stateStore :=
              targetStore

            parameters :=
              boundParameters

            pendingActions :=
              positionalRemaining

            activeBody :=
              (Translation.compileMultiStorePayloadReaction
                selectedServer).body
          }

          have hTargetDispatch :
              LF.MultiStorePayloadDispatchStep
                (Translation.compileMultiStorePayloadMessageReactions
                  messageServers)
                {
                  currentTag :=
                    currentTag

                  stateStore :=
                    targetStore

                  parameters :=
                    targetParameters

                  pendingActions :=
                    pendingActions

                  activeBody :=
                    []
                }
                selectionAction
                (Translation.compileMultiStorePayloadReaction
                  selectedServer)
                targetStateAfter := by

            simpa [
              targetStateAfter
            ] using
              (LF.MultiStorePayloadDispatchStep.fire
                (messageReactions :=
                  Translation.compileMultiStorePayloadMessageReactions
                    messageServers)
                (currentTag :=
                  currentTag)
                (stateStore :=
                  targetStore)
                (parameters :=
                  targetParameters)
                (pendingActions :=
                  pendingActions)
                (remainingActions :=
                  positionalRemaining)
                (selectedAction :=
                  selectionAction)
                (selectedReaction :=
                  Translation.compileMultiStorePayloadReaction
                    selectedServer)
                (boundParameters :=
                  boundParameters)
                hReactionDeclared
                hPositionalRemoved
                hSelectionEligible
                hTargetNotPast
                hReactionTrigger
                hTargetBind)

          have hPostPendingNotPast :
              LF.ActionQueue.PendingNotPast
                selectionAction.tag
                positionalRemaining :=
            LF.ActionQueue.pendingNotPast_of_remove_earliest
              hSelectionEligible.isEarliest
              hPositionalRemoved

          refine
            ⟨selectionAction,
             targetStateAfter,
             hTargetDispatch,
             hSelectionCorresponds,
             ?_⟩

          exact {
            states := {
              states := {
                currentTime :=
                  hSelectionCorresponds.occurrence.logicalTime

                stateStore := by
                  change
                    targetStore =
                      stateStore

                  simpa using
                    hRuntime.toStateCorresponds.stateStore

                parameters :=
                  rfl

                pendingQueues :=
                  hPositionalQueues

                activeBody :=
                  rfl
              }

              pendingEvents :=
                hRemainingCompatible
            }

            pendingNotPast :=
              hPostPendingNotPast
          }

end Correctness
end Relico
