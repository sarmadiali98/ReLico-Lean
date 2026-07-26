import Relico.Correctness.BoundPayloadState
import Relico.Correctness.Dispatch
import Relico.DTR.BoundPayloadDispatch
import Relico.LF.BoundPayloadDispatch

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compatibility condition required for forward parameter-aware payload
dispatch.

The source occurrence and residual source queue must have aligned target
occurrences at the same list positions. The selected target action must
also be LF-earliest and must not precede the current LF tag.

The additional scheduler premises are required because DTR orders by
logical time, whereas LF orders by complete tags including microsteps.
-/
def BoundPayloadForwardDispatchCompatible
    (selectedMessage : DTR.PendingMessage)
    (sourceRemaining : DTR.MessageBag)
    (targetState : LF.BoundPayloadState) :
    Prop :=

  ∃ selectedAction targetRemaining,
    Occurrence.RemovesOne
        selectedAction
        targetState.pendingActions
        targetRemaining ∧
      PendingPayloadCorresponds
        selectedMessage
        selectedAction ∧
      PayloadQueueCorresponds
        sourceRemaining
        targetRemaining ∧
      LF.IsEarliest
        selectedAction
        targetState.pendingActions ∧
      LF.Tag.PrecedesOrEqual
        targetState.currentTag
        selectedAction.tag

/--
Conditional forward correctness for one parameter-aware payload
dispatch.

The generated LF transition selects the occurrence corresponding to the
source message, binds the same ordered payload to the same ordered formal
parameters, and produces a corresponding activation state.
-/
theorem boundPayloadDispatch_forward_of_compatible
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter : DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {targetBefore : LF.BoundPayloadState}
    (hSourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter)
    (hStates :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hCompatible :
      BoundPayloadForwardDispatchCompatible
        selectedMessage
        sourceAfter.pendingMessages
        targetBefore) :
    ∃ selectedAction targetAfter,
      LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter ∧
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        BoundPayloadStateCorresponds
          sourceAfter
          targetAfter := by

  cases hSourceDispatch with

  | fire
      currentTime
      stateValue
      sourceParameters
      pendingMessages
      remainingMessages
      selectedMessage
      boundParameters
      hSourceRemoved
      hSourceEarliest
      hSourceNotPast
      hSourceTarget
      hSourceBind =>

      cases targetBefore with

      | mk
          currentTag
          targetStateValue
          targetParameters
          pendingActions
          targetBody =>

          have hCurrentTime :
              currentTag.time =
                currentTime :=
            hStates.currentTime

          have hStateValue :
              targetStateValue =
                stateValue :=
            hStates.stateValue

          have hParameters :
              targetParameters =
                sourceParameters :=
            hStates.parameters

          have hTargetBodyEmpty :
              targetBody =
                [] := by

            simpa [
              Translation.compileBoundPayloadBody
            ] using
              hStates.activeBody

          change
            ∃ selectedAction targetRemaining,
              Occurrence.RemovesOne
                  selectedAction
                  pendingActions
                  targetRemaining ∧
                PendingPayloadCorresponds
                  selectedMessage
                  selectedAction ∧
                PayloadQueueCorresponds
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
          subst targetParameters
          subst targetBody

          have hTargetTrigger :
              selectedAction.name =
                (Translation.compilePayloadMessageServer
                  server).logicalAction := by

            calc
              selectedAction.name =
                  Translation.actionNameFor
                    selectedMessage.name :=
                hSelectedCorresponds.occurrence.actionName

              _ =
                  Translation.actionNameFor
                    server.name := by
                      rw [
                        hSourceTarget
                      ]

              _ =
                  (Translation.compilePayloadMessageServer
                    server).logicalAction := by
                      rfl

          have hTargetBind :
              ParameterStore.bindPayload
                  (Translation.compilePayloadMessageServer
                    server).parameters
                  selectedAction.payload =
                some boundParameters := by

            simpa [
              Translation.compilePayloadMessageServer,
              hSelectedCorresponds.payload
            ] using
              hSourceBind

          let targetAfter :
              LF.BoundPayloadState := {

            currentTag :=
              selectedAction.tag

            stateValue :=
              stateValue

            parameters :=
              boundParameters

            pendingActions :=
              targetRemaining

            activeBody :=
              (Translation.compilePayloadMessageServer
                server).body
          }

          refine
            ⟨selectedAction,
             targetAfter,
             ?_,
             hSelectedCorresponds,
             ?_⟩

          · exact
              LF.BoundPayloadDispatchStep.fire
                (reaction :=
                  Translation.compilePayloadMessageServer
                    server)
                (currentTag :=
                  currentTag)
                (stateValue :=
                  stateValue)
                (parameters :=
                  sourceParameters)
                (pendingActions :=
                  pendingActions)
                (remainingActions :=
                  targetRemaining)
                (selectedAction :=
                  selectedAction)
                (boundParameters :=
                  boundParameters)
                hTargetRemoved
                hTargetEarliest
                hTargetNotPast
                hTargetTrigger
                hTargetBind

          · exact {
              currentTime :=
                hSelectedCorresponds.occurrence.logicalTime

              stateValue :=
                rfl

              parameters :=
                rfl

              pendingEvents :=
                hRemainingCorresponds

              activeBody :=
                rfl
            }

/--
Every generated parameter-aware LF dispatch beginning in corresponding
states can be reconstructed as a source dispatch.

LF-earliest selection implies DTR-earliest selection after forgetting
microsteps. Exact payload equality and preservation of formal-parameter
order ensure that both transitions construct the same parameter store.
-/
theorem boundPayloadDispatch_backward
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hTargetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter)
    (hStates :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore) :
    ∃ selectedMessage sourceAfter,
      DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceAfter ∧
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        BoundPayloadStateCorresponds
          sourceAfter
          targetAfter := by

  cases hTargetDispatch with

  | fire
      currentTag
      targetStateValue
      targetParameters
      pendingActions
      remainingActions
      selectedAction
      boundParameters
      hTargetRemoved
      hTargetEarliest
      hTargetNotPast
      hTargetTrigger
      hTargetBind =>

      cases sourceBefore with

      | mk
          sourceTime
          sourceStateValue
          sourceParameters
          pendingMessages
          sourceBody =>

          have hCurrentTime :
              currentTag.time =
                sourceTime :=
            hStates.currentTime

          have hStateValue :
              targetStateValue =
                sourceStateValue :=
            hStates.stateValue

          have hParameters :
              targetParameters =
                sourceParameters :=
            hStates.parameters

          have hQueues :
              PayloadQueueCorresponds
                pendingMessages
                pendingActions :=
            hStates.pendingEvents

          have hCompiledBodyEmpty :
              Translation.compileBoundPayloadBody
                  sourceBody =
                [] := by

            simpa using
              hStates.activeBody.symm

          have hSourceBodyEmpty :
              sourceBody =
                [] := by

            cases sourceBody with

            | nil =>
                rfl

            | cons statement remaining =>
                simp [
                  Translation.compileBoundPayloadBody
                ] at hCompiledBodyEmpty

          subst targetStateValue
          subst targetParameters
          subst sourceBody

          rcases
              PayloadQueueCorresponds.remove_target
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
              (PayloadQueueCorresponds.toQueueCorresponds
                hQueues)
              hSelectedCorresponds.occurrence
              hTargetEarliest

          have hSourceNotPast :
              sourceTime ≤
                selectedMessage.arrivalTime := by

            have hTargetTimeOrder :
                currentTag.time ≤
                  selectedAction.tag.time :=

              LF.Tag.time_le_of_precedesOrEqual
                hTargetNotPast

            calc
              sourceTime =
                  currentTag.time :=
                hCurrentTime.symm

              _ ≤
                  selectedAction.tag.time :=
                hTargetTimeOrder

              _ =
                  selectedMessage.arrivalTime :=
                hSelectedCorresponds.occurrence.logicalTime

          have hSourceTarget :
              selectedMessage.name =
                server.name := by

            apply
              Translation.actionNameFor_injective

            calc
              Translation.actionNameFor
                  selectedMessage.name =
                selectedAction.name :=
                  hSelectedCorresponds.occurrence.actionName.symm

              _ =
                (Translation.compilePayloadMessageServer
                  server).logicalAction :=
                    hTargetTrigger

              _ =
                Translation.actionNameFor
                  server.name := by
                    rfl

          have hSourceBind :
              ParameterStore.bindPayload
                  server.parameters
                  selectedMessage.payload =
                some boundParameters := by

            simpa [
              Translation.compilePayloadMessageServer,
              hSelectedCorresponds.payload
            ] using
              hTargetBind

          let sourceAfter :
              DTR.BoundPayloadState := {

            currentTime :=
              selectedMessage.arrivalTime

            stateValue :=
              sourceStateValue

            parameters :=
              boundParameters

            pendingMessages :=
              sourceRemaining

            activeBody :=
              server.body
          }

          refine
            ⟨selectedMessage,
             sourceAfter,
             ?_,
             hSelectedCorresponds,
             ?_⟩

          · exact
              DTR.BoundPayloadDispatchStep.fire
                (server :=
                  server)
                (currentTime :=
                  sourceTime)
                (stateValue :=
                  sourceStateValue)
                (parameters :=
                  sourceParameters)
                (pendingMessages :=
                  pendingMessages)
                (remainingMessages :=
                  sourceRemaining)
                (selectedMessage :=
                  selectedMessage)
                (boundParameters :=
                  boundParameters)
                hSourceRemoved
                hSourceEarliest
                hSourceNotPast
                hSourceTarget
                hSourceBind

          · exact {
              currentTime :=
                hSelectedCorresponds.occurrence.logicalTime

              stateValue :=
                rfl

              parameters :=
                rfl

              pendingEvents :=
                hRemainingCorresponds

              activeBody :=
                rfl
            }

end Correctness
end Relico
