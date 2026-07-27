import Relico.Correctness.DetailedBoundPayloadForwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
One payload-aware backward weak-simulation match.

The package contains a source weak transition matching one generated-LF
detailed label, payload-aware label correspondence, and preservation of
phase-indexed state correspondence.
-/
def DetailedBoundPayloadBackwardMatch
    (server : DTR.PayloadMessageServer)
    (targetLabel :
      LF.DetailedBoundPayloadLabel)
    (targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server))
    (sourceBefore :
      DTR.DetailedBoundPayloadState server) :
    Prop :=
  ∃ sourceLabel : DTR.DetailedBoundPayloadLabel,
    ∃ sourceAfter :
        DTR.DetailedBoundPayloadState server,
      DTR.DetailedBoundPayloadWeakStep
          server
          sourceBefore
          sourceLabel
          sourceAfter ∧
        DetailedBoundPayloadLabelCorresponds
          sourceLabel
          targetLabel ∧
        DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter

/--
Backward weak simulation for one generated-LF parameter-aware statement
transition.
-/
theorem detailedBoundPayload_statement_backward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {targetLabel : LF.BoundPayloadLabel}
    (hTargetStep :
      LF.BoundPayloadStep
        (Translation.compilePayloadMessageServer
          server).logicalAction
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DetailedBoundPayloadBackwardMatch
      server
      .tau
      (.stable targetAfter)
      (.stable sourceBefore) := by

  have hStable :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore :=
    DetailedBoundPayloadStateCorresponds.stable_iff.mp
      hStates

  have hTargetStep' :
      LF.BoundPayloadStep
        (Translation.actionNameFor
          server.name)
        targetBefore
        targetLabel
        targetAfter := by

    simpa [
      Translation.compilePayloadMessageServer
    ] using
      hTargetStep

  rcases
      boundPayloadStep_backward
        hStable
        hTargetStep'
    with
      ⟨sourceLabel,
       sourceAfter,
       hSourceStep,
       _hStatementLabels,
       hFinalStates⟩

  exact
    ⟨
      .tau,
      .stable sourceAfter,
      DTR.detailedBoundPayloadStatement_is_weak
        hSourceStep,
      DetailedBoundPayloadLabelCorresponds.tau,
      DetailedBoundPayloadStateCorresponds.stable
        hFinalStates
    ⟩

/--
Backward weak simulation for visible generated-LF metric-time progression.

The generated dispatch reconstructs a payload-bearing source dispatch. Runtime
state correspondence identifies both metric-time endpoints.
-/
theorem detailedBoundPayload_timeAdvance_backward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hTargetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter)
    (hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DetailedBoundPayloadBackwardMatch
      server
      (.timeAdvance
        targetBefore.currentTag.time
        targetAfter.currentTag.time)
      (.afterTime
        targetBefore
        selectedAction
        targetAfter
        hTargetDispatch)
      (.stable sourceBefore) := by

  have hStable :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore :=
    DetailedBoundPayloadStateCorresponds.stable_iff.mp
      hStates

  rcases
      boundPayloadDispatch_backward
        hTargetDispatch
        hStable
    with
      ⟨selectedMessage,
       sourceAfter,
       hSourceDispatch,
       hSelectedOccurrence,
       hAfterStates⟩

  have hSourceFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime := by

    calc
      sourceBefore.currentTime =
          targetBefore.currentTag.time :=
        hStable.currentTime.symm

      _ <
          targetAfter.currentTag.time :=
        hTargetFuture

      _ =
          sourceAfter.currentTime :=
        hAfterStates.currentTime

  have hWitness :
      DetailedBoundPayloadDispatchWitnessCorresponds
        server
        sourceBefore
        selectedMessage
        sourceAfter
        targetBefore
        selectedAction
        targetAfter := {
    beforeState :=
      hStable

    selectedOccurrence :=
      hSelectedOccurrence

    afterState :=
      hAfterStates
  }

  have hSourceDetailedStep :
      DTR.DetailedBoundPayloadStep
        server
        (.stable sourceBefore)
        (.timeAdvance
          sourceBefore.currentTime
          sourceAfter.currentTime)
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          hSourceDispatch) :=
    DTR.DetailedBoundPayloadStep.timeAdvance
      hSourceDispatch
      hSourceFuture

  exact
    ⟨
      .timeAdvance
        sourceBefore.currentTime
        sourceAfter.currentTime,
      .dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        hSourceDispatch,
      DTR.detailedBoundPayloadTimeAdvance_is_weak
        hSourceDetailedStep,
      DetailedBoundPayloadLabelCorresponds.timeAdvance
        hStable.currentTime
        hAfterStates.currentTime,
      DetailedBoundPayloadStateCorresponds.futureAfterTime
        hSourceFuture
        hTargetFuture
        hWitness
    ⟩

/--
Backward matching for the internal generated-LF microstep following a future
metric-time transition.

The source remains dispatch-ready and performs a reflexive weak-`tau`
transition.
-/
theorem detailedBoundPayload_microstepAfterTime_backward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hPositiveMicrostep :
      0 <
        targetAfter.currentTag.microstep)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)) :
    DetailedBoundPayloadBackwardMatch
      server
      (.microstepAdvance
        {
          time :=
            targetAfter.currentTag.time

          microstep :=
            0
        }
        targetAfter.currentTag)
      (.dispatchReady
        targetBefore
        selectedAction
        targetAfter
        targetDispatch)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        sourceDispatch) := by

  cases hStates with

  | futureAfterTime
      hSourceFuture
      hTargetFuture
      hWitness =>

      exact
        ⟨
          .tau,
          .dispatchReady
            sourceBefore
            selectedMessage
            sourceAfter
            sourceDispatch,
          DTR.detailedBoundPayloadWeakTau_refl
            (.dispatchReady
              sourceBefore
              selectedMessage
              sourceAfter
              sourceDispatch),
          DetailedBoundPayloadLabelCorresponds.microstep
            {
              time :=
                targetAfter.currentTag.time

              microstep :=
                0
            }
            targetAfter.currentTag,
          DetailedBoundPayloadStateCorresponds.futureReady
            hSourceFuture
            hTargetFuture
            hPositiveMicrostep
            hWitness
        ⟩

/--
Backward matching for a same-time generated-LF microstep transition from a
stable state.

The generated dispatch is reconstructed as a source payload dispatch. The
source stutters while generated LF advances internally to dispatch-ready.
-/
theorem detailedBoundPayload_microstepSameTime_backward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hTargetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter)
    (hTargetSameTime :
      targetBefore.currentTag.time =
        targetAfter.currentTag.time)
    (hLaterMicrostep :
      targetBefore.currentTag.microstep <
        targetAfter.currentTag.microstep)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DetailedBoundPayloadBackwardMatch
      server
      (.microstepAdvance
        targetBefore.currentTag
        targetAfter.currentTag)
      (.dispatchReady
        targetBefore
        selectedAction
        targetAfter
        hTargetDispatch)
      (.stable sourceBefore) := by

  have hStable :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore :=
    DetailedBoundPayloadStateCorresponds.stable_iff.mp
      hStates

  rcases
      boundPayloadDispatch_backward
        hTargetDispatch
        hStable
    with
      ⟨selectedMessage,
       sourceAfter,
       hSourceDispatch,
       hSelectedOccurrence,
       hAfterStates⟩

  have hSourceSameTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime := by

    calc
      sourceBefore.currentTime =
          targetBefore.currentTag.time :=
        hStable.currentTime.symm

      _ =
          targetAfter.currentTag.time :=
        hTargetSameTime

      _ =
          sourceAfter.currentTime :=
        hAfterStates.currentTime

  have hWitness :
      DetailedBoundPayloadDispatchWitnessCorresponds
        server
        sourceBefore
        selectedMessage
        sourceAfter
        targetBefore
        selectedAction
        targetAfter := {
    beforeState :=
      hStable

    selectedOccurrence :=
      hSelectedOccurrence

    afterState :=
      hAfterStates
  }

  exact
    ⟨
      .tau,
      .stable sourceBefore,
      DTR.detailedBoundPayloadWeakTau_refl
        (.stable sourceBefore),
      DetailedBoundPayloadLabelCorresponds.microstep
        targetBefore.currentTag
        targetAfter.currentTag,
      DetailedBoundPayloadStateCorresponds.sameTimeMicrostepAhead
        hSourceDispatch
        hSourceSameTime
        hTargetSameTime
        hLaterMicrostep
        hWitness
    ⟩

/--
Backward matching for generated-LF consumption immediately after a future
time transition whose destination microstep is zero.
-/
theorem detailedBoundPayload_consumeAfterTimeZero_backward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (_hZeroMicrostep :
      targetAfter.currentTag.microstep =
        0)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)) :
    DetailedBoundPayloadBackwardMatch
      server
      (.consume selectedAction)
      (.stable targetAfter)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        sourceDispatch) := by

  cases hStates with

  | futureAfterTime
      _hSourceFuture
      _hTargetFuture
      hWitness =>

      have hSourceDetailedStep :
          DTR.DetailedBoundPayloadStep
            server
            (.dispatchReady
              sourceBefore
              selectedMessage
              sourceAfter
              sourceDispatch)
            (.consume selectedMessage)
            (.stable sourceAfter) :=
        DTR.DetailedBoundPayloadStep.consumeReady
          sourceDispatch

      exact
        ⟨
          .consume selectedMessage,
          .stable sourceAfter,
          DTR.detailedBoundPayloadConsume_is_weak
            hSourceDetailedStep,
          DetailedBoundPayloadLabelCorresponds.consume
            hWitness.selectedOccurrence,
          DetailedBoundPayloadStateCorresponds.stable
            hWitness.afterState
        ⟩

/--
Backward matching for generated-LF consumption from a future dispatch-ready
phase.
-/
theorem detailedBoundPayload_consumeReadyFuture_backward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          sourceDispatch)
        (.dispatchReady
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)) :
    DetailedBoundPayloadBackwardMatch
      server
      (.consume selectedAction)
      (.stable targetAfter)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        sourceDispatch) := by

  cases hStates with

  | futureReady
      _hSourceFuture
      _hTargetFuture
      _hPositiveMicrostep
      hWitness =>

      have hSourceDetailedStep :
          DTR.DetailedBoundPayloadStep
            server
            (.dispatchReady
              sourceBefore
              selectedMessage
              sourceAfter
              sourceDispatch)
            (.consume selectedMessage)
            (.stable sourceAfter) :=
        DTR.DetailedBoundPayloadStep.consumeReady
          sourceDispatch

      exact
        ⟨
          .consume selectedMessage,
          .stable sourceAfter,
          DTR.detailedBoundPayloadConsume_is_weak
            hSourceDetailedStep,
          DetailedBoundPayloadLabelCorresponds.consume
            hWitness.selectedOccurrence,
          DetailedBoundPayloadStateCorresponds.stable
            hWitness.afterState
        ⟩

/--
Backward matching for generated-LF consumption from a same-time
dispatch-ready phase.

The related source state remains stable, so source execution performs
`consumeNow`.
-/
theorem detailedBoundPayload_consumeReadySameTime_backward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.dispatchReady
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)) :
    DetailedBoundPayloadBackwardMatch
      server
      (.consume selectedAction)
      (.stable targetAfter)
      (.stable sourceBefore) := by

  have hSourceData :
      ∃ sourceAfter : DTR.BoundPayloadState,
        ∃ selectedMessage : DTR.PendingMessage,
          ∃ sourceDispatch :
              DTR.BoundPayloadDispatchStep
                server
                sourceBefore
                selectedMessage
                sourceAfter,
            sourceBefore.currentTime =
                sourceAfter.currentTime ∧
              DetailedBoundPayloadDispatchWitnessCorresponds
                server
                sourceBefore
                selectedMessage
                sourceAfter
                targetBefore
                selectedAction
                targetAfter := by

    cases hStates with

    | sameTimeMicrostepAhead
        sourceDispatch
        hSourceSameTime
        _hTargetSameTime
        _hLaterMicrostep
        hWitness =>

        exact
          ⟨_,
           _,
           sourceDispatch,
           hSourceSameTime,
           hWitness⟩

  rcases hSourceData with
    ⟨sourceAfter,
     selectedMessage,
     sourceDispatch,
     hSourceSameTime,
     hWitness⟩

  have hSourceDetailedStep :
      DTR.DetailedBoundPayloadStep
        server
        (.stable sourceBefore)
        (.consume selectedMessage)
        (.stable sourceAfter) :=
    DTR.DetailedBoundPayloadStep.consumeNow
      sourceDispatch
      hSourceSameTime

  exact
    ⟨
      .consume selectedMessage,
      .stable sourceAfter,
      DTR.detailedBoundPayloadConsume_is_weak
        hSourceDetailedStep,
      DetailedBoundPayloadLabelCorresponds.consume
        hWitness.selectedOccurrence,
      DetailedBoundPayloadStateCorresponds.stable
        hWitness.afterState
    ⟩

/--
Backward weak simulation for direct generated-LF payload-reaction firing at
the current complete tag.
-/
theorem detailedBoundPayload_consumeNow_backward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hTargetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter)
    (hTargetSameTag :
      targetBefore.currentTag =
        targetAfter.currentTag)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DetailedBoundPayloadBackwardMatch
      server
      (.consume selectedAction)
      (.stable targetAfter)
      (.stable sourceBefore) := by

  have hStable :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore :=
    DetailedBoundPayloadStateCorresponds.stable_iff.mp
      hStates

  rcases
      boundPayloadDispatch_backward
        hTargetDispatch
        hStable
    with
      ⟨selectedMessage,
       sourceAfter,
       hSourceDispatch,
       hSelectedOccurrence,
       hAfterStates⟩

  have hTargetSameTime :
      targetBefore.currentTag.time =
        targetAfter.currentTag.time :=
    congrArg
      LF.Tag.time
      hTargetSameTag

  have hSourceSameTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime := by

    calc
      sourceBefore.currentTime =
          targetBefore.currentTag.time :=
        hStable.currentTime.symm

      _ =
          targetAfter.currentTag.time :=
        hTargetSameTime

      _ =
          sourceAfter.currentTime :=
        hAfterStates.currentTime

  have hSourceDetailedStep :
      DTR.DetailedBoundPayloadStep
        server
        (.stable sourceBefore)
        (.consume selectedMessage)
        (.stable sourceAfter) :=
    DTR.DetailedBoundPayloadStep.consumeNow
      hSourceDispatch
      hSourceSameTime

  exact
    ⟨
      .consume selectedMessage,
      .stable sourceAfter,
      DTR.detailedBoundPayloadConsume_is_weak
        hSourceDetailedStep,
      DetailedBoundPayloadLabelCorresponds.consume
        hSelectedOccurrence,
      DetailedBoundPayloadStateCorresponds.stable
        hAfterStates
    ⟩

/--
Every payload-aware backward match contains a source destination state
corresponding to the generated-LF destination state.
-/
theorem DetailedBoundPayloadBackwardMatch.source_corresponds
    {server : DTR.PayloadMessageServer}
    {targetLabel :
      LF.DetailedBoundPayloadLabel}
    {targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    {sourceBefore :
      DTR.DetailedBoundPayloadState server}
    (hMatch :
      DetailedBoundPayloadBackwardMatch
        server
        targetLabel
        targetAfter
        sourceBefore) :
    ∃ sourceAfter :
        DTR.DetailedBoundPayloadState server,
      DetailedBoundPayloadStateCorresponds
        server
        sourceAfter
        targetAfter := by

  rcases hMatch with
    ⟨_sourceLabel,
     sourceAfter,
     _hWeakStep,
     _hLabels,
     hStates⟩

  exact
    ⟨sourceAfter,
     hStates⟩


end Correctness
end Relico
