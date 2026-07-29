/-
Copyright (c) 2026.

Payload-refined phase-aware state correspondence for the direct
DTR-to-generated-LF translation.

This layer reuses the ordinary detailed state architecture while strengthening
selected pending occurrences and stable runtime states with exact payload
correspondence. It projects to the established DirectLF detailed theorem stack.

No operational semantics, detailed state datatype, source transition, target
microstep phase, or paper premise is changed.
-/

import Relico.Correctness.DirectLFPayloadBackwardDispatchRuntime
import Relico.Correctness.DirectLFDetailedRuntimeStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Runtime-aware detailed dispatch witness.

The witness records correspondence before dispatch, for the selected
occurrence and generated handler, and after dispatch.
-/
abbrev DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
    (messageServers :
      List DTR.MessageServer)
    (sourceBefore :
      DTR.StoreState)
    (selectedMessage :
      DTR.PendingMessage)
    (selectedServer :
      DTR.MessageServer)
    (sourceAfter :
      DTR.StoreState)
    (targetBefore :
      LF.StoreState)
    (selectedAction :
      LF.PendingAction)
    (selectedReaction :
      LF.Reaction)
    (targetAfter :
      LF.StoreState) :
    Prop :=
  DetailedDispatchWitnessCorresponds
    (DirectLFPayloadRuntimeStateCorresponds
      messageServers)
    PendingPayloadCorresponds
    DirectLFCompiledMessageReactionCorresponds
    sourceBefore
    selectedMessage
    selectedServer
    sourceAfter
    targetBefore
    selectedAction
    selectedReaction
    targetAfter

/--
Ordinary detailed-state correspondence for the active DirectLF replacement
path.
-/
abbrev DirectLFPayloadDetailedRuntimeStateCorresponds
    (messageServers :
      List DTR.MessageServer) :
    DTR.DetailedMultiStoreState
        messageServers →
      LF.DetailedMultiStoreState
          (Translation.compileMessageReactions
            messageServers) →
        Prop :=
  DetailedStateCorresponds
    (DirectLFPayloadRuntimeStateCorresponds
      messageServers)
    PendingPayloadCorresponds
    DirectLFCompiledMessageReactionCorresponds
    messageServers
    (Translation.compileMessageReactions
      messageServers)

/--
Stable detailed states correspond exactly when their ordinary runtime states
correspond.
-/
theorem directLFPayloadDetailedRuntime_stable_iff
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState :
      LF.StoreState} :
    DirectLFPayloadDetailedRuntimeStateCorresponds
          messageServers
          (.stable sourceState)
          (.stable targetState) ↔
      DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState := by

  exact
    DetailedStateCorresponds.stable_iff

/--
Construct a detailed dispatch witness from the four active correspondence
facts.
-/
theorem directLFPayloadDetailedRuntimeDispatchWitness_mk
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    {targetBefore targetAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    (hBefore :
      DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hSelected :
      PendingPayloadCorresponds
        selectedMessage
        selectedAction)
    (hReaction :
      selectedReaction =
        Translation.compileMessageReaction
          selectedServer)
    (hAfter :
      DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceAfter
        targetAfter) :
    DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
      messageServers
      sourceBefore
      selectedMessage
      selectedServer
      sourceAfter
      targetBefore
      selectedAction
      selectedReaction
      targetAfter := by

  exact {
    beforeState :=
      hBefore

    selectedOccurrence :=
      hSelected

    selectedHandler :=
      hReaction

    afterState :=
      hAfter
  }

/--
A detailed dispatch witness equates target and source metric times before and
after dispatch.
-/
theorem directLFPayloadDetailedRuntimeDispatchWitness_times
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    {targetBefore targetAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    (hWitness :
      DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    targetBefore.currentTag.time =
          sourceBefore.currentTime ∧
      targetAfter.currentTag.time =
          sourceAfter.currentTime := by

  exact
    ⟨hWitness.beforeState.states.currentTime,
     hWitness.afterState.states.currentTime⟩

/--
Package the active forward dispatch theorem as a detailed dispatch witness.
-/
theorem directLFPayloadDetailedRuntime_dispatch_forward
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    {targetBefore :
      LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hRuntime :
      DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore) :
    ∃ selectedAction targetAfter,
      LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          selectedAction
          (Translation.compileMessageReaction
            selectedServer)
          targetAfter ∧
        DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          (Translation.compileMessageReaction
            selectedServer)
          targetAfter := by

  obtain
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     hSelected,
     hAfter⟩ :=
      directLFPayload_multiStore_dispatch_forward_runtime
        hSourceDispatch
        hRuntime

  refine
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     ?_⟩

  exact
    directLFPayloadDetailedRuntimeDispatchWitness_mk
      hRuntime
      hSelected
      rfl
      hAfter

/--
Package the active backward dispatch theorem as a detailed dispatch witness.
-/
theorem directLFPayloadDetailedRuntime_dispatch_backward
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore :
      DTR.StoreState}
    {targetBefore targetAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    (hTargetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hRuntime :
      DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore) :
    ∃ selectedMessage selectedServer sourceAfter,
      DTR.MultiStoreDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter ∧
        DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          selectedReaction
          targetAfter := by

  obtain
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hReaction,
     hSourceDispatch,
     hSelected,
     hAfter⟩ :=
      directLFPayload_multiStore_dispatch_backward_runtime
        hTargetDispatch
        hRuntime

  refine
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hSourceDispatch,
     ?_⟩

  exact
    directLFPayloadDetailedRuntimeDispatchWitness_mk
      hRuntime
      hSelected
      hReaction
      hAfter

/--
Construct the future `afterTime` phase from a source future dispatch and a
runtime-aware detailed dispatch witness.

The corresponding target metric-time inequality follows from the witness.
-/
theorem directLFPayloadDetailedRuntime_futureAfterTime
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hSourceFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hWitness :
      DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    DirectLFPayloadDetailedRuntimeStateCorresponds
      messageServers
      (.dispatchReady
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        sourceDispatch)
      (.afterTime
        targetBefore
        selectedAction
        selectedReaction
        targetAfter
        targetDispatch) := by

  have hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time := by

    calc
      targetBefore.currentTag.time =
          sourceBefore.currentTime :=
        hWitness.beforeState.states.currentTime

      _ <
          sourceAfter.currentTime :=
        hSourceFuture

      _ =
          targetAfter.currentTag.time :=
        hWitness.afterState.states.currentTime.symm

  exact
    DetailedStateCorresponds.futureAfterTime
      hSourceFuture
      hTargetFuture
      hWitness

/--
Construct the future dispatch-ready phase after LF's internal microstep.
-/
theorem directLFPayloadDetailedRuntime_futureReady
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hSourceFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hPositiveMicrostep :
      0 <
        targetAfter.currentTag.microstep)
    (hWitness :
      DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    DirectLFPayloadDetailedRuntimeStateCorresponds
      messageServers
      (.dispatchReady
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        sourceDispatch)
      (.dispatchReady
        targetBefore
        selectedAction
        selectedReaction
        targetAfter
        targetDispatch) := by

  have hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time := by

    calc
      targetBefore.currentTag.time =
          sourceBefore.currentTime :=
        hWitness.beforeState.states.currentTime

      _ <
          sourceAfter.currentTime :=
        hSourceFuture

      _ =
          targetAfter.currentTag.time :=
        hWitness.afterState.states.currentTime.symm

  exact
    DetailedStateCorresponds.futureReady
      hSourceFuture
      hTargetFuture
      hPositiveMicrostep
      hWitness

/--
Construct the same-metric-time stuttering phase in which LF reaches a later
microstep while DTR remains in its stable pre-dispatch state.
-/
theorem directLFPayloadDetailedRuntime_sameTimeMicrostepAhead
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    (sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    {targetBefore targetAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hSourceSameTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime)
    (hTargetLaterMicrostep :
      targetBefore.currentTag.microstep <
        targetAfter.currentTag.microstep)
    (hWitness :
      DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    DirectLFPayloadDetailedRuntimeStateCorresponds
      messageServers
      (.stable sourceBefore)
      (.dispatchReady
        targetBefore
        selectedAction
        selectedReaction
        targetAfter
        targetDispatch) := by

  have hTargetSameTime :
      targetBefore.currentTag.time =
        targetAfter.currentTag.time := by

    calc
      targetBefore.currentTag.time =
          sourceBefore.currentTime :=
        hWitness.beforeState.states.currentTime

      _ =
          sourceAfter.currentTime :=
        hSourceSameTime

      _ =
          targetAfter.currentTag.time :=
        hWitness.afterState.states.currentTime.symm

  exact
    DetailedStateCorresponds.sameTimeMicrostepAhead
      sourceDispatch
      hSourceSameTime
      hTargetSameTime
      hTargetLaterMicrostep
      hWitness


/--
Forgetting exact payload equality yields the existing detailed dispatch
witness.
-/
theorem DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds.toDetailedRuntimeDispatchWitnessCorresponds
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hWitness :
      DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    DirectLFDetailedRuntimeDispatchWitnessCorresponds
      messageServers
      sourceBefore
      selectedMessage
      selectedServer
      sourceAfter
      targetBefore
      selectedAction
      selectedReaction
      targetAfter := by

  exact {
    beforeState :=
      DirectLFPayloadRuntimeStateCorresponds.toRuntimeStateCorresponds
        hWitness.beforeState

    selectedOccurrence :=
      PendingPayloadCorresponds.toPendingCorresponds
        hWitness.selectedOccurrence

    selectedHandler :=
      hWitness.selectedHandler

    afterState :=
      DirectLFPayloadRuntimeStateCorresponds.toRuntimeStateCorresponds
        hWitness.afterState
  }

/--
Forgetting exact payload equality in every phase yields the existing detailed
runtime-state relation.
-/
theorem DirectLFPayloadDetailedRuntimeStateCorresponds.toDetailedRuntimeStateCorresponds
    {messageServers : List DTR.MessageServer}
    {sourceState :
      DTR.DetailedMultiStoreState
        messageServers}
    {targetState :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    (hStates :
      DirectLFPayloadDetailedRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFDetailedRuntimeStateCorresponds
      messageServers
      sourceState
      targetState := by

  cases hStates with

  | stable hStable =>

      exact
        DetailedStateCorresponds.stable
          (DirectLFPayloadRuntimeStateCorresponds.toRuntimeStateCorresponds
            hStable)

  | futureAfterTime hDtrFuture hLfFuture hWitness =>

      exact
        DetailedStateCorresponds.futureAfterTime
          hDtrFuture
          hLfFuture
          (DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds.toDetailedRuntimeDispatchWitnessCorresponds
              hWitness)

  | futureReady
      hDtrFuture
      hLfFuture
      hPositiveMicrostep
      hWitness =>

      exact
        DetailedStateCorresponds.futureReady
          hDtrFuture
          hLfFuture
          hPositiveMicrostep
          (DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds.toDetailedRuntimeDispatchWitnessCorresponds
              hWitness)

  | sameTimeMicrostepAhead
      sourceDispatch
      hSourceSameTime
      hTargetSameTime
      hTargetLaterMicrostep
      hWitness =>

      exact
        DetailedStateCorresponds.sameTimeMicrostepAhead
          sourceDispatch
          hSourceSameTime
          hTargetSameTime
          hTargetLaterMicrostep
          (DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds.toDetailedRuntimeDispatchWitnessCorresponds
              hWitness)

end Correctness
end Relico
