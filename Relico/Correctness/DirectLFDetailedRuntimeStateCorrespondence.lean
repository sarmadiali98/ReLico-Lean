/-
Copyright (c) 2026.

Ordinary phase-aware state correspondence for the direct DTR-to-generated-LF
translation.

This module instantiates the mature generic detailed-state relation with:

- `DirectLFRuntimeStateCorresponds` for stable runtime states;
- `PendingCorresponds` for selected pending occurrences;
- exact generated-reaction correspondence for selected handlers.

Both sides use their existing ordinary detailed semantics. LF microstep phases
remain target-only.

No source ghost state, source microstep, restricted source semantics,
positive-delay-only assumption, or positional source-bag correspondence is
introduced.
-/

import Relico.Correctness.DirectLFBackwardDispatchRuntime
import Relico.Correctness.DetailedStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between a DTR message server and the generated LF reaction
compiled from it.
-/
def DirectLFCompiledMessageReactionCorresponds
    (sourceServer : DTR.MessageServer)
    (targetReaction : LF.Reaction) :
    Prop :=
  targetReaction =
    Translation.compileMessageReaction
      sourceServer

/--
Runtime-aware detailed dispatch witness.

The witness records correspondence before dispatch, for the selected
occurrence and generated handler, and after dispatch.
-/
abbrev DirectLFDetailedRuntimeDispatchWitnessCorresponds
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
    (DirectLFRuntimeStateCorresponds
      messageServers)
    PendingCorresponds
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
abbrev DirectLFDetailedRuntimeStateCorresponds
    (messageServers :
      List DTR.MessageServer) :
    DTR.DetailedMultiStoreState
        messageServers →
      LF.DetailedMultiStoreState
          (Translation.compileMessageReactions
            messageServers) →
        Prop :=
  DetailedStateCorresponds
    (DirectLFRuntimeStateCorresponds
      messageServers)
    PendingCorresponds
    DirectLFCompiledMessageReactionCorresponds
    messageServers
    (Translation.compileMessageReactions
      messageServers)

/--
Stable detailed states correspond exactly when their ordinary runtime states
correspond.
-/
theorem directLFDetailedRuntime_stable_iff
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState :
      LF.StoreState} :
    DirectLFDetailedRuntimeStateCorresponds
          messageServers
          (.stable sourceState)
          (.stable targetState) ↔
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState := by

  exact
    DetailedStateCorresponds.stable_iff

/--
Construct a detailed dispatch witness from the four active correspondence
facts.
-/
theorem directLFDetailedRuntimeDispatchWitness_mk
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
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hSelected :
      PendingCorresponds
        selectedMessage
        selectedAction)
    (hReaction :
      selectedReaction =
        Translation.compileMessageReaction
          selectedServer)
    (hAfter :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceAfter
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
theorem directLFDetailedRuntimeDispatchWitness_times
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
      DirectLFDetailedRuntimeDispatchWitnessCorresponds
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
theorem directLFDetailedRuntime_dispatch_forward
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
      DirectLFRuntimeStateCorresponds
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
        DirectLFDetailedRuntimeDispatchWitnessCorresponds
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
      directLF_multiStore_dispatch_forward_runtime
        hSourceDispatch
        hRuntime

  refine
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     ?_⟩

  exact
    directLFDetailedRuntimeDispatchWitness_mk
      hRuntime
      hSelected
      rfl
      hAfter

/--
Package the active backward dispatch theorem as a detailed dispatch witness.
-/
theorem directLFDetailedRuntime_dispatch_backward
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
      DirectLFRuntimeStateCorresponds
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

  obtain
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hReaction,
     hSourceDispatch,
     hSelected,
     hAfter⟩ :=
      directLF_multiStore_dispatch_backward_runtime
        hTargetDispatch
        hRuntime

  refine
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hSourceDispatch,
     ?_⟩

  exact
    directLFDetailedRuntimeDispatchWitness_mk
      hRuntime
      hSelected
      hReaction
      hAfter

/--
Construct the future `afterTime` phase from a source future dispatch and a
runtime-aware detailed dispatch witness.

The corresponding target metric-time inequality follows from the witness.
-/
theorem directLFDetailedRuntime_futureAfterTime
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
      DirectLFDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    DirectLFDetailedRuntimeStateCorresponds
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
theorem directLFDetailedRuntime_futureReady
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
      DirectLFDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    DirectLFDetailedRuntimeStateCorresponds
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
theorem directLFDetailedRuntime_sameTimeMicrostepAhead
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
      DirectLFDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    DirectLFDetailedRuntimeStateCorresponds
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

end Correctness
end Relico
