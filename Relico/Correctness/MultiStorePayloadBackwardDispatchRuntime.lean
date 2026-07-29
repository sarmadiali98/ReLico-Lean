import Relico.Correctness.MultiStorePayloadForwardDispatchRuntime
import Relico.Correctness.MultiStorePayloadRuntimeDispatchSupport
import Relico.Correctness.MultiStorePayloadDispatchSelection
import Relico.LF.PendingNotPast

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compilation reflects emptiness of a payload-aware multi-store body.
-/
theorem multiStorePayload_compileBody_eq_nil_iff
    (sourceBody :
      DTR.MultiStorePayloadBody) :
    Translation.compileMultiStorePayloadBody sourceBody =
        [] ↔
      sourceBody =
        [] := by

  simp [
    Translation.compileMultiStorePayloadBody
  ]

/--
Every generated LF payload dispatch has a corresponding DTR payload dispatch,
and complete payload-aware runtime-state correspondence is preserved.

The runtime premise retains the explicit selection-compatibility boundary
needed to reconcile DTR priority selection with complete LF tags.
-/
theorem multiStorePayload_dispatch_backward_runtime
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState targetStateAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetState
        selectedAction
        selectedReaction
        targetStateAfter)
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedMessage selectedServer sourceStateAfter,
      selectedReaction =
          Translation.compileMultiStorePayloadReaction
            selectedServer ∧
        DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceState
          selectedMessage
          selectedServer
          sourceStateAfter ∧
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        MultiStorePayloadRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter := by

  cases hTargetDispatch with

  | fire
      currentTag
      targetStore
      targetParameters
      pendingActions
      remainingActions
      selectedAction
      selectedReaction
      boundParameters
      hReactionDeclared
      hTargetRemoved
      hTargetPriorityEligible
      hTargetNotPast
      hTrigger
      hTargetBind =>

      obtain
        ⟨sourceServer,
         hSourceServerDeclared,
         hCompiledReaction⟩ :=
          Translation.mem_compileMultiStorePayloadMessageReactions
            hReactionDeclared

      subst selectedReaction

      cases sourceState with

      | mk
          sourceTime
          sourceStore
          sourceParameters
          pendingMessages
          sourceActiveBody =>

          have hCurrentTime :
              currentTag.time =
                sourceTime := by

            simpa using
              hRuntime.toStateCorresponds.currentTime

          have hStateStore :
              targetStore =
                sourceStore := by

            simpa using
              hRuntime.toStateCorresponds.stateStore

          obtain
            ⟨selectionMessage,
             selectionRemaining,
             hSelectionRemoved,
             hSelectionCorresponds,
             hSelectionEligible,
             hSelectionRemaining⟩ :=
              multiStorePayload_targetDispatchSelection
                hRuntime.selectionCompatible
                hTargetRemoved
                hTargetPriorityEligible

          obtain
            ⟨positionalMessage,
             positionalRemaining,
             hPositionalRemoved,
             hPositionalCorresponds,
             hPositionalQueues⟩ :=
              PayloadQueueCorresponds.remove_target
                hRuntime.payloadQueues
                hTargetRemoved

          have hSelectedMessage :
              selectionMessage =
                positionalMessage :=
            pendingPayloadCorresponds_source_eq_of_sameTarget
              hSelectionCorresponds
              hPositionalCorresponds

          subst positionalMessage

          have hRemainingCompatible :
              MultiStorePayloadSelectionCompatible
                messageServers
                positionalRemaining
                remainingActions :=
            multiStorePayload_backwardResidualSelectionMerge
              hSelectionRemoved
              hPositionalRemoved
              hSelectionRemaining

          have hCompiledSourceBodyEmpty :
              Translation.compileMultiStorePayloadBody
                  sourceActiveBody =
                [] := by

            simpa using
              hRuntime.toStateCorresponds.activeBody.symm

          have hSourceBodyEmpty :
              sourceActiveBody =
                [] :=
            (multiStorePayload_compileBody_eq_nil_iff
              sourceActiveBody).mp
                hCompiledSourceBodyEmpty

          have hGeneratedServerAction :
              Translation.actionNameFor
                  sourceServer.name =
                selectedAction.name := by

            simpa [
              Translation.compileMultiStorePayloadReaction
            ] using
              hTrigger

          have hSourceTarget :
              selectionMessage.name =
                sourceServer.name := by

            apply
              Translation.actionNameFor_injective

            calc
              Translation.actionNameFor
                    selectionMessage.name =
                  selectedAction.name :=
                hSelectionCorresponds.occurrence.actionName.symm

              _ =
                  Translation.actionNameFor
                    sourceServer.name :=
                hGeneratedServerAction.symm

          have hTargetMetricNotPast :
              currentTag.time ≤
                selectedAction.tag.time :=
            LF.Tag.time_le_of_precedesOrEqual
              hTargetNotPast

          have hSourceNotPast :
              sourceTime ≤
                selectionMessage.arrivalTime := by

            calc
              sourceTime =
                  currentTag.time :=
                hCurrentTime.symm

              _ ≤
                  selectedAction.tag.time :=
                hTargetMetricNotPast

              _ =
                  selectionMessage.arrivalTime :=
                hSelectionCorresponds.occurrence.logicalTime

          have hSourceBind :
              ParameterStore.bindPayload
                  sourceServer.parameters
                  selectionMessage.payload =
                some boundParameters := by

            simpa [
              Translation.compileMultiStorePayloadReaction,
              hPositionalCorresponds.payload
            ] using
              hTargetBind

          subst sourceActiveBody

          let sourceStateAfter :
              DTR.MultiStorePayloadState := {
            currentTime :=
              selectionMessage.arrivalTime

            stateStore :=
              sourceStore

            parameters :=
              boundParameters

            pendingMessages :=
              positionalRemaining

            activeBody :=
              sourceServer.body
          }

          have hSourceDispatch :
              DTR.MultiStorePayloadDispatchStep
                messageServers
                {
                  currentTime :=
                    sourceTime

                  stateStore :=
                    sourceStore

                  parameters :=
                    sourceParameters

                  pendingMessages :=
                    pendingMessages

                  activeBody :=
                    []
                }
                selectionMessage
                sourceServer
                sourceStateAfter := by

            simpa [
              sourceStateAfter
            ] using
              (DTR.MultiStorePayloadDispatchStep.fire
                (messageServers :=
                  messageServers)
                (currentTime :=
                  sourceTime)
                (stateStore :=
                  sourceStore)
                (parameters :=
                  sourceParameters)
                (pendingMessages :=
                  pendingMessages)
                (remainingMessages :=
                  positionalRemaining)
                (selectedMessage :=
                  selectionMessage)
                (selectedServer :=
                  sourceServer)
                (boundParameters :=
                  boundParameters)
                hSourceServerDeclared
                hPositionalRemoved
                hSelectionEligible
                hSourceNotPast
                hSourceTarget
                hSourceBind)

          refine
            ⟨selectionMessage,
             sourceServer,
             sourceStateAfter,
             rfl,
             hSourceDispatch,
             hSelectionCorresponds,
             ?_⟩

          exact {
            states := {
              states := {
                currentTime := by
                  change
                    selectedAction.tag.time =
                      selectionMessage.arrivalTime

                  exact
                    hSelectionCorresponds.occurrence.logicalTime

                stateStore := by
                  change
                    targetStore =
                      sourceStore

                  exact
                    hStateStore

                parameters := by
                  rfl

                pendingQueues :=
                  hPositionalQueues

                activeBody := by
                  rfl
              }

              pendingEvents :=
                hRemainingCompatible
            }

            pendingNotPast := by
              change
                LF.ActionQueue.PendingNotPast
                  selectedAction.tag
                  remainingActions

              exact
                LF.ActionQueue.pendingNotPast_of_remove_earliest
                  hTargetPriorityEligible.isEarliest
                  hTargetRemoved
          }

end Correctness
end Relico
