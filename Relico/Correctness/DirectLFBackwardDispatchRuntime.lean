/-
Copyright (c) 2026.

Ordinary backward dispatch simulation for the direct DTR-to-generated-LF
translation.

A concrete generated-LF dispatch reconstructs the corresponding ordinary DTR
dispatch.

The proof synchronizes:

- generated reaction membership and source server declaration;
- target and source one-occurrence removal;
- LF and DTR priority eligibility;
- complete LF-tag and source metric-time admissibility;
- generated trigger and source message-server name;
- residual runtime correspondence.

No source-side microstep, ghost state, restricted source semantics,
positive-delay-only condition, or positional source-bag correspondence is
introduced.
-/

import Relico.Correctness.DirectLFForwardDispatchRuntime
import Relico.Correctness.DirectLFDispatchSelection
import Relico.Correctness.DirectLFRuntimeStateCorrespondence
import Relico.DTR.MultiStoreDispatchSemantics
import Relico.LF.MultiStoreDispatchSemantics
import Relico.Translation.MultiStoreBasic

set_option autoImplicit false

namespace Relico
namespace Correctness
/--
Compilation maps a source body to the empty LF body exactly when the source
body is empty.

This is ordinary list-map inversion. It adds no semantic restriction.
-/
@[simp]
theorem directLF_compileBody_eq_nil_iff
    (sourceBody : DTR.Body) :
    Translation.compileBody sourceBody = [] ↔
      sourceBody = [] := by

  simp [
    Translation.compileBody
  ]

/--
One ordinary generated-LF dispatch reconstructs the corresponding ordinary
DTR dispatch.

The proof:

1. inverts membership in the generated LF reaction list;
2. synchronizes the selected target occurrence with one source occurrence;
3. transports LF reaction-priority eligibility to DTR priority eligibility;
4. projects complete LF-tag admissibility to DTR metric time;
5. recovers the selected DTR message-server name through the generated trigger;
6. constructs the residual ordinary runtime correspondence.

Repeated equal pending values remain occurrence-sensitive. Payload equality is
not required.
-/
theorem directLF_multiStore_dispatch_backward_runtime
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState targetStateAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    (hTargetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetState
        selectedAction
        selectedReaction
        targetStateAfter)
    (hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedMessage selectedServer sourceStateAfter,
      selectedReaction =
          Translation.compileMessageReaction
            selectedServer ∧
        DTR.MultiStoreDispatchStep
          messageServers
          sourceState
          selectedMessage
          selectedServer
          sourceStateAfter ∧
        PendingCorresponds
          selectedMessage
          selectedAction ∧
        DirectLFRuntimeStateCorresponds
          messageServers
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
      hTargetPriorityEligible
      hTargetNotPast
      hTrigger =>

      obtain
        ⟨sourceServer,
         hSourceServerDeclared,
         hCompiledReaction⟩ :=
          Translation.mem_compileMessageReactions
            hReactionDeclared

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
              hRuntime.states.currentTime

          have hStateStore :
              targetStore =
                sourceStore := by

            simpa using
              hRuntime.states.stateStore

          have hCompatible :
              DirectLFSelectionCompatible
                messageServers
                pendingMessages
                pendingActions := by

            simpa using
              hRuntime.selectionCompatible

          obtain
            ⟨selectedMessage,
             sourceRemaining,
             hSourceRemoved,
             hSelectedCorresponds,
             hSourcePriorityEligible,
             hRemainingCompatible⟩ :=
              directLF_targetDispatchSelection
                hCompatible
                hTargetRemoved
                hTargetPriorityEligible

          have hCompiledSourceBodyEmpty :
              Translation.compileBody
                  sourceActiveBody =
                [] := by

            simpa using
              hRuntime.states.activeBody.symm

          have hSourceBodyEmpty :
              sourceActiveBody =
                [] :=
            (directLF_compileBody_eq_nil_iff
              sourceActiveBody).mp
                hCompiledSourceBodyEmpty

          have hGeneratedServerAction :
              Translation.actionNameFor
                  sourceServer.name =
                selectedAction.name := by

            simpa [
              Translation.compileMessageReaction
            ] using
              hTrigger

          have hSourceTarget :
              selectedMessage.name =
                sourceServer.name := by

            apply
              Translation.actionNameFor_injective

            calc
              Translation.actionNameFor
                    selectedMessage.name =
                  selectedAction.name :=
                hSelectedCorresponds.actionName.symm

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
                selectedMessage.arrivalTime := by

            calc
              sourceTime =
                  currentTag.time :=
                hCurrentTime.symm

              _ ≤
                  selectedAction.tag.time :=
                hTargetMetricNotPast

              _ =
                  selectedMessage.arrivalTime :=
                hSelectedCorresponds.logicalTime

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

          have hSourceDispatch :
              DTR.MultiStoreDispatchStep
                messageServers
                {
                  currentTime :=
                    sourceTime

                  stateStore :=
                    sourceStore

                  pendingMessages :=
                    pendingMessages

                  activeBody :=
                    []
                }
                selectedMessage
                sourceServer
                sourceStateAfter := by

            simpa [
              sourceStateAfter
            ] using
              (DTR.MultiStoreDispatchStep.fire
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
                hSourcePriorityEligible
                hSourceNotPast
                hSourceTarget)

          refine
            ⟨selectedMessage,
             sourceServer,
             sourceStateAfter,
             rfl,
             hSourceDispatch,
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
                    sourceStore

                exact
                  hStateStore

              pendingEvents := by
                change
                  DirectLFSelectionCompatible
                    messageServers
                    sourceRemaining
                    remainingActions

                exact
                  hRemainingCompatible

              activeBody := by
                change
                  (Translation.compileMessageReaction
                      sourceServer).body =
                    Translation.compileBody
                      sourceServer.body

                rfl
            }

            pendingNotPast := by
              change
                LF.ActionQueue.PendingNotPast
                  selectedAction.tag
                  remainingActions

              exact
                LF.ActionQueue.pendingNotPast_of_remove_earliest
                  hTargetPriorityEligible.1
                  hTargetRemoved
          }

end Correctness
end Relico
