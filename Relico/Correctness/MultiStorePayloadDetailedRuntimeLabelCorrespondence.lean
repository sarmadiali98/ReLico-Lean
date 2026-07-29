import Relico.DTR.DetailedMultiStorePayloadRuntime
import Relico.LF.DetailedMultiStorePayloadRuntime
import Relico.Correctness.MultiStorePayloadBackwardDispatchRuntime

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
A payload-aware detailed dispatch witness records correspondence before and
after dispatch, exact selected occurrence correspondence, and recovery of the
generated reaction from its source message server.
-/
structure MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceBefore :
      DTR.MultiStorePayloadState)
    (selectedMessage :
      DTR.PendingMessage)
    (selectedServer :
      DTR.MultiStorePayloadMessageServer)
    (sourceAfter :
      DTR.MultiStorePayloadState)
    (targetBefore :
      LF.MultiStorePayloadState)
    (selectedAction :
      LF.PendingAction)
    (selectedReaction :
      LF.MultiStorePayloadReaction)
    (targetAfter :
      LF.MultiStorePayloadState) :
    Prop where

  beforeState :
    MultiStorePayloadRuntimeStateCorresponds
      messageServers
      sourceBefore
      targetBefore

  selectedOccurrence :
    PendingPayloadCorresponds
      selectedMessage
      selectedAction

  selectedHandler :
    selectedReaction =
      Translation.compileMultiStorePayloadReaction
        selectedServer

  afterState :
    MultiStorePayloadRuntimeStateCorresponds
      messageServers
      sourceAfter
      targetAfter

/--
Detailed phase correspondence for the payload-aware multi-server runtime.

LF microsteps remain target-only. Same-metric-time microstep progression is
represented by correspondence between a stable DTR state and an LF
`dispatchReady` state.
-/
inductive MultiStorePayloadDetailedRuntimeStateCorresponds
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    DTR.DetailedMultiStorePayloadState
        messageServers →
      LF.DetailedMultiStorePayloadState
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers) →
        Prop where

  | stable
      {sourceState :
        DTR.MultiStorePayloadState}
      {targetState :
        LF.MultiStorePayloadState}
      (runtime :
        MultiStorePayloadRuntimeStateCorresponds
          messageServers
          sourceState
          targetState) :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceState)
        (.stable targetState)

  | futureAfterTime
      {sourceBefore sourceAfter :
        DTR.MultiStorePayloadState}
      {selectedMessage :
        DTR.PendingMessage}
      {selectedServer :
        DTR.MultiStorePayloadMessageServer}
      {sourceDispatch :
        DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter}
      {targetBefore targetAfter :
        LF.MultiStorePayloadState}
      {selectedAction :
        LF.PendingAction}
      {selectedReaction :
        LF.MultiStorePayloadReaction}
      {targetDispatch :
        LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter}
      (sourceFuture :
        sourceBefore.currentTime <
          sourceAfter.currentTime)
      (targetFuture :
        targetBefore.currentTag.time <
          targetAfter.currentTag.time)
      (witness :
        MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          selectedReaction
          targetAfter) :
      MultiStorePayloadDetailedRuntimeStateCorresponds
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
          targetDispatch)

  | futureReady
      {sourceBefore sourceAfter :
        DTR.MultiStorePayloadState}
      {selectedMessage :
        DTR.PendingMessage}
      {selectedServer :
        DTR.MultiStorePayloadMessageServer}
      {sourceDispatch :
        DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter}
      {targetBefore targetAfter :
        LF.MultiStorePayloadState}
      {selectedAction :
        LF.PendingAction}
      {selectedReaction :
        LF.MultiStorePayloadReaction}
      {targetDispatch :
        LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter}
      (sourceFuture :
        sourceBefore.currentTime <
          sourceAfter.currentTime)
      (targetFuture :
        targetBefore.currentTag.time <
          targetAfter.currentTag.time)
      (positiveMicrostep :
        0 <
          targetAfter.currentTag.microstep)
      (witness :
        MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          selectedReaction
          targetAfter) :
      MultiStorePayloadDetailedRuntimeStateCorresponds
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
          targetDispatch)

  | sameTimeMicrostepAhead
      {sourceBefore sourceAfter :
        DTR.MultiStorePayloadState}
      {selectedMessage :
        DTR.PendingMessage}
      {selectedServer :
        DTR.MultiStorePayloadMessageServer}
      (sourceDispatch :
        DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter)
      {targetBefore targetAfter :
        LF.MultiStorePayloadState}
      {selectedAction :
        LF.PendingAction}
      {selectedReaction :
        LF.MultiStorePayloadReaction}
      {targetDispatch :
        LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetBefore
          selectedAction
          selectedReaction
          targetAfter}
      (sourceSameTime :
        sourceBefore.currentTime =
          sourceAfter.currentTime)
      (targetSameTime :
        targetBefore.currentTag.time =
          targetAfter.currentTag.time)
      (laterMicrostep :
        targetBefore.currentTag.microstep <
          targetAfter.currentTag.microstep)
      (witness :
        MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          selectedReaction
          targetAfter) :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.dispatchReady
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)

/--
Payload-aware correspondence between detailed DTR and LF labels.

Target microstep advancement corresponds to source `tau`. Consumption retains
the selected message, server, action, reaction, and exact payload equality.
-/
inductive MultiStorePayloadDetailedLabelCorresponds :
    DTR.DetailedMultiStorePayloadLabel →
      LF.DetailedMultiStorePayloadLabel →
        Prop where

  | tau :
      MultiStorePayloadDetailedLabelCorresponds
        .tau
        .tau

  | microstep
      (before after :
        LF.Tag) :
      MultiStorePayloadDetailedLabelCorresponds
        .tau
        (.microstepAdvance
          before
          after)

  | timeAdvance
      {sourceBefore sourceAfter :
        LogicalTime}
      {targetBefore targetAfter :
        LogicalTime}
      (beforeTime :
        targetBefore =
          sourceBefore)
      (afterTime :
        targetAfter =
          sourceAfter) :
      MultiStorePayloadDetailedLabelCorresponds
        (.timeAdvance
          sourceBefore
          sourceAfter)
        (.timeAdvance
          targetBefore
          targetAfter)

  | consume
      {sourceMessage :
        DTR.PendingMessage}
      {sourceServer :
        DTR.MultiStorePayloadMessageServer}
      {targetAction :
        LF.PendingAction}
      {targetReaction :
        LF.MultiStorePayloadReaction}
      (occurrence :
        PendingPayloadCorresponds
          sourceMessage
          targetAction)
      (reaction :
        targetReaction =
          Translation.compileMultiStorePayloadReaction
            sourceServer) :
      MultiStorePayloadDetailedLabelCorresponds
        (.consume
          sourceMessage
          sourceServer)
        (.consume
          targetAction
          targetReaction)

/--
Stable detailed states correspond exactly when their ordinary runtime states
correspond.
-/
theorem multiStorePayloadDetailedRuntime_stable_iff
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState} :
    MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          (.stable sourceState)
          (.stable targetState) ↔
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState := by

  constructor

  · intro hStates

    cases hStates with

    | stable hRuntime =>
        exact hRuntime

  · intro hRuntime

    exact
      MultiStorePayloadDetailedRuntimeStateCorresponds.stable
        hRuntime

/--
Construct a detailed dispatch witness from its four correspondence facts.
-/
theorem multiStorePayloadDetailedRuntimeDispatchWitness_mk
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hBefore :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hSelected :
      PendingPayloadCorresponds
        selectedMessage
        selectedAction)
    (hReaction :
      selectedReaction =
        Translation.compileMultiStorePayloadReaction
          selectedServer)
    (hAfter :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceAfter
        targetAfter) :
    MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
      messageServers
      sourceBefore
      selectedMessage
      selectedServer
      sourceAfter
      targetBefore
      selectedAction
      selectedReaction
      targetAfter := {

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
A detailed dispatch witness identifies source and target metric times before
and after dispatch.
-/
theorem multiStorePayloadDetailedRuntimeDispatchWitness_times
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hWitness :
      MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
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
    ⟨hWitness.beforeState.toStateCorresponds.currentTime,
     hWitness.afterState.toStateCorresponds.currentTime⟩

/--
Package forward payload dispatch correspondence as a detailed witness.
-/
theorem multiStorePayloadDetailedRuntime_dispatch_forward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetBefore :
      LF.MultiStorePayloadState}
    (hSourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore) :
    ∃ selectedAction targetAfter,
      LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetBefore
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetAfter ∧
        MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetAfter := by

  obtain
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     hSelected,
     hAfter⟩ :=
      multiStorePayload_dispatch_forward_runtime
        hSourceDispatch
        hRuntime

  exact
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     multiStorePayloadDetailedRuntimeDispatchWitness_mk
       hRuntime
       hSelected
       rfl
       hAfter⟩

/--
Package backward payload dispatch correspondence as a detailed witness.
-/
theorem multiStorePayloadDetailedRuntime_dispatch_backward
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore) :
    ∃ selectedMessage selectedServer sourceAfter,
      DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter ∧
        MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
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
      multiStorePayload_dispatch_backward_runtime
        hTargetDispatch
        hRuntime

  exact
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hSourceDispatch,
     multiStorePayloadDetailedRuntimeDispatchWitness_mk
       hRuntime
       hSelected
       hReaction
       hAfter⟩

/--
Construct the detailed future `afterTime` correspondence phase.
-/
theorem multiStorePayloadDetailedRuntime_futureAfterTime
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {sourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hSourceFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hWitness :
      MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
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
        hWitness.beforeState.toStateCorresponds.currentTime

      _ <
          sourceAfter.currentTime :=
        hSourceFuture

      _ =
          targetAfter.currentTag.time :=
        hWitness.afterState.toStateCorresponds.currentTime.symm

  exact
    MultiStorePayloadDetailedRuntimeStateCorresponds.futureAfterTime
      hSourceFuture
      hTargetFuture
      hWitness

/--
Construct the future LF dispatch-ready phase after a target-only microstep.
-/
theorem multiStorePayloadDetailedRuntime_futureReady
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {sourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
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
      MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
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
        hWitness.beforeState.toStateCorresponds.currentTime

      _ <
          sourceAfter.currentTime :=
        hSourceFuture

      _ =
          targetAfter.currentTag.time :=
        hWitness.afterState.toStateCorresponds.currentTime.symm

  exact
    MultiStorePayloadDetailedRuntimeStateCorresponds.futureReady
      hSourceFuture
      hTargetFuture
      hPositiveMicrostep
      hWitness

/--
Construct the same-metric-time phase where LF advances to a later microstep
while DTR remains in its stable pre-dispatch state.
-/
theorem multiStorePayloadDetailedRuntime_sameTimeMicrostepAhead
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (sourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
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
      MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
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
        hWitness.beforeState.toStateCorresponds.currentTime

      _ =
          sourceAfter.currentTime :=
        hSourceSameTime

      _ =
          targetAfter.currentTag.time :=
        hWitness.afterState.toStateCorresponds.currentTime.symm

  exact
    MultiStorePayloadDetailedRuntimeStateCorresponds.sameTimeMicrostepAhead
      sourceDispatch
      hSourceSameTime
      hTargetSameTime
      hTargetLaterMicrostep
      hWitness

/--
Consume-label correspondence retains exact selected payload equality.
-/
theorem MultiStorePayloadDetailedLabelCorresponds.consume_payload_eq
    {sourceMessage :
      DTR.PendingMessage}
    {sourceServer :
      DTR.MultiStorePayloadMessageServer}
    {targetAction :
      LF.PendingAction}
    {targetReaction :
      LF.MultiStorePayloadReaction}
    (hLabels :
      MultiStorePayloadDetailedLabelCorresponds
        (.consume
          sourceMessage
          sourceServer)
        (.consume
          targetAction
          targetReaction)) :
    targetAction.payload =
      sourceMessage.payload := by

  cases hLabels with

  | consume hOccurrence _hReaction =>
      exact
        hOccurrence.payload

end Correctness
end Relico
