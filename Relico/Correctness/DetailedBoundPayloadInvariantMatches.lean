import Relico.Correctness.DetailedBoundPayloadRuntimeInvariantPreservation
import Relico.Correctness.DetailedBoundPayloadFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Phase-aware source timing invariant for detailed bound-payload execution.

A stable phase describes the stored source state. A dispatch-ready phase
describes the post-dispatch state whose message-server body has already been
activated.
-/
def DetailedBoundPayloadSourceRuntimeInvariant
    (server : DTR.PayloadMessageServer)
    (state :
      DTR.DetailedBoundPayloadState
        server) :
    Prop :=

  match state with

  | .stable sourceState =>
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceState.activeBody

  | .dispatchReady
      _sourceBefore
      _selectedMessage
      sourceAfter
      _sourceDispatch =>

      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceAfter.activeBody

/--
Phase-aware target runtime invariant for detailed generated-LF bound-payload
execution.

All three detailed phases refer to a concrete runtime state:

- `stable` uses its stored state;
- `afterTime` uses the embedded post-dispatch state;
- `dispatchReady` uses the same embedded post-dispatch state.

Unlike the ordinary strictly-positive model, `dispatchReady` is valid here
because a zero-delay external invocation may require an LF microstep before
consumption.
-/
def DetailedBoundPayloadTargetRuntimeInvariant
    (server : DTR.PayloadMessageServer)
    (state :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)) :
    Prop :=

  match state with

  | .stable targetState =>
      LF.BoundPayloadState.RuntimeInvariant
        targetState

  | .afterTime
      _targetBefore
      _selectedAction
      targetAfter
      _targetDispatch =>

      LF.BoundPayloadState.RuntimeInvariant
        targetAfter

  | .dispatchReady
      _targetBefore
      _selectedAction
      targetAfter
      _targetDispatch =>

      LF.BoundPayloadState.RuntimeInvariant
        targetAfter

/--
Forward chosen execution uses only phase pairings that can recursively accept
the next exact source step.

The same-time `stable`/`dispatchReady` correspondence is intentionally excluded.
It is a legitimate intermediate generated-LF phase, but exposing it as a
forward recursive endpoint commits the target scheduler before the next source
dispatch choice has been selected.
-/
def DetailedBoundPayloadForwardCanonicalPhase
    {server : DTR.PayloadMessageServer}
    (sourceState :
      DTR.DetailedBoundPayloadState
        server)
    (targetState :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)) :
    Prop :=

  match sourceState, targetState with

  | .stable _,
    .stable _ =>
      True

  | .dispatchReady _ _ _ _,
    .afterTime _ _ _ _ =>
      True

  | .dispatchReady _ _ _ _,
    .dispatchReady _ _ _ _ =>
      True

  | _, _ =>
      False

@[simp]
theorem detailedBoundPayloadSourceRuntimeInvariant_stable
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState} :
    DetailedBoundPayloadSourceRuntimeInvariant
          server
          (.stable sourceState) ↔
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceState.activeBody := by

  rfl

@[simp]
theorem detailedBoundPayloadSourceRuntimeInvariant_dispatchReady
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter} :
    DetailedBoundPayloadSourceRuntimeInvariant
          server
          (.dispatchReady
            sourceBefore
            selectedMessage
            sourceAfter
            sourceDispatch) ↔
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceAfter.activeBody := by

  rfl

@[simp]
theorem detailedBoundPayloadTargetRuntimeInvariant_stable
    {server : DTR.PayloadMessageServer}
    {targetState : LF.BoundPayloadState} :
    DetailedBoundPayloadTargetRuntimeInvariant
          server
          (.stable targetState) ↔
      LF.BoundPayloadState.RuntimeInvariant
        targetState := by

  rfl

@[simp]
theorem detailedBoundPayloadTargetRuntimeInvariant_afterTime
    {server : DTR.PayloadMessageServer}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter} :
    DetailedBoundPayloadTargetRuntimeInvariant
          server
          (.afterTime
            targetBefore
            selectedAction
            targetAfter
            targetDispatch) ↔
      LF.BoundPayloadState.RuntimeInvariant
        targetAfter := by

  rfl

@[simp]
theorem detailedBoundPayloadTargetRuntimeInvariant_dispatchReady
    {server : DTR.PayloadMessageServer}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter} :
    DetailedBoundPayloadTargetRuntimeInvariant
          server
          (.dispatchReady
            targetBefore
            selectedAction
            targetAfter
            targetDispatch) ↔
      LF.BoundPayloadState.RuntimeInvariant
        targetAfter := by

  rfl

@[simp]
theorem detailedBoundPayloadForwardCanonicalPhase_stable
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetState : LF.BoundPayloadState} :
    DetailedBoundPayloadForwardCanonicalPhase
      (server := server)
      (.stable sourceState)
      (.stable targetState) := by

  simp [
    DetailedBoundPayloadForwardCanonicalPhase
  ]

@[simp]
theorem detailedBoundPayloadForwardCanonicalPhase_futureAfterTime
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
        targetAfter} :
    DetailedBoundPayloadForwardCanonicalPhase
      (server := server)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        sourceDispatch)
      (.afterTime
        targetBefore
        selectedAction
        targetAfter
        targetDispatch) := by

  simp [
    DetailedBoundPayloadForwardCanonicalPhase
  ]

@[simp]
theorem detailedBoundPayloadForwardCanonicalPhase_futureReady
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
        targetAfter} :
    DetailedBoundPayloadForwardCanonicalPhase
      (server := server)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        sourceDispatch)
      (.dispatchReady
        targetBefore
        selectedAction
        targetAfter
        targetDispatch) := by

  simp [
    DetailedBoundPayloadForwardCanonicalPhase
  ]

/--
A stable source paired with a target that has already committed to a same-time
dispatch is not a canonical recursive forward endpoint.
-/
theorem detailedBoundPayloadForwardCanonicalPhase_rejects_sameTimeAhead
    {server : DTR.PayloadMessageServer}
    {sourceState : DTR.BoundPayloadState}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter} :
    ¬ DetailedBoundPayloadForwardCanonicalPhase
        (server := server)
        (.stable sourceState)
        (.dispatchReady
          targetBefore
          selectedAction
          targetAfter
          targetDispatch) := by

  intro hCanonical

  simp [
    DetailedBoundPayloadForwardCanonicalPhase
  ] at hCanonical

/--
Canonical phase alignment and the target runtime invariant derive the existing
forward phase-compatibility premise automatically.
-/
theorem detailedBoundPayloadForwardPhaseCompatible_of_canonicalRuntimeInvariant
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    (hSourceStep :
      DTR.DetailedBoundPayloadStep
        server
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hTargetInvariant :
      DetailedBoundPayloadTargetRuntimeInvariant
        server
        targetBefore)
    (hCanonical :
      DetailedBoundPayloadForwardCanonicalPhase
        sourceBefore
        targetBefore) :
    DetailedBoundPayloadForwardPhaseCompatible
      sourceBefore
      sourceLabel
      sourceAfter
      targetBefore := by

  cases hSourceStep with

  | statement hStatement =>
      cases hStates with

      | stable hStable =>
          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ]

      | sameTimeMicrostepAhead
          sourceDispatch
          hSourceSameTime
          hTargetSameTime
          hLaterMicrostep
          hWitness =>

          simp [
            DetailedBoundPayloadForwardCanonicalPhase
          ] at hCanonical

  | timeAdvance hSourceDispatch hFuture =>
      cases hStates with

      | stable hStable =>
          have hTargetRuntime :=
            detailedBoundPayloadTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          have hScheduler :
              BoundPayloadForwardDispatchCompatible
                _
                _
                _ :=

            boundPayloadForwardDispatchCompatible_of_runtimeInvariant
              hSourceDispatch
              hStable
              hTargetRuntime

          simpa [
            DetailedBoundPayloadForwardPhaseCompatible
          ] using
            hScheduler

      | sameTimeMicrostepAhead
          sourceDispatch
          hSourceSameTime
          hTargetSameTime
          hLaterMicrostep
          hWitness =>

          simp [
            DetailedBoundPayloadForwardCanonicalPhase
          ] at hCanonical

  | consumeReady hSourceDispatch =>
      cases hStates with

      | futureAfterTime
          hSourceFuture
          hTargetFuture
          hWitness =>

          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ]

      | futureReady
          hSourceFuture
          hTargetFuture
          hPositiveMicrostep
          hWitness =>

          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ]

  | consumeNow hSourceDispatch hSameTime =>
      cases hStates with

      | stable hStable =>
          have hTargetRuntime :=
            detailedBoundPayloadTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          have hScheduler :
              BoundPayloadForwardDispatchCompatible
                _
                _
                _ :=

            boundPayloadForwardDispatchCompatible_of_runtimeInvariant
              hSourceDispatch
              hStable
              hTargetRuntime

          simpa [
            DetailedBoundPayloadForwardPhaseCompatible
          ] using
            hScheduler

      | sameTimeMicrostepAhead
          sourceDispatch
          hSourceSameTime
          hTargetSameTime
          hLaterMicrostep
          hWitness =>

          simp [
            DetailedBoundPayloadForwardCanonicalPhase
          ] at hCanonical

/--
Every exact target step from a corresponding detailed phase satisfies the
existing backward compatibility predicate.

Unlike the forward direction, the backward interface explicitly supports the
same-time `stable`/`dispatchReady` correspondence.
-/
theorem detailedBoundPayloadBackwardPhaseCompatible_of_correspondence
    {server : DTR.PayloadMessageServer}
    {sourceBefore :
      DTR.DetailedBoundPayloadState
        server}
    {targetBefore targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    {targetLabel :
      LF.DetailedBoundPayloadLabel}
    (hTargetStep :
      LF.DetailedBoundPayloadStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore) :
    DetailedBoundPayloadBackwardPhaseCompatible
      sourceBefore
      targetBefore
      targetLabel
      targetAfter := by

  cases hTargetStep with

  | statement hStatement =>
      cases hStates with
      | stable hStable =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ]

  | timeAdvance hTargetDispatch hFuture =>
      cases hStates with
      | stable hStable =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ]

  | microstepAfterTime
      hTargetDispatch
      hPositiveMicrostep =>

      cases hStates with
      | futureAfterTime
          hSourceFuture
          hTargetFuture
          hWitness =>

          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ]

  | consumeAfterTimeZero
      hTargetDispatch
      hZeroMicrostep =>

      cases hStates with
      | futureAfterTime
          hSourceFuture
          hTargetFuture
          hWitness =>

          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ]

  | microstepSameTime
      hTargetDispatch
      hSameTime
      hLaterMicrostep =>

      cases hStates with
      | stable hStable =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ]

  | consumeReady hTargetDispatch =>
      cases hStates with

      | futureReady
          hSourceFuture
          hTargetFuture
          hPositiveMicrostep
          hWitness =>

          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ]

      | sameTimeMicrostepAhead
          sourceDispatch
          hSourceSameTime
          hTargetSameTime
          hLaterMicrostep
          hWitness =>

          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ]

  | consumeNow hTargetDispatch hSameTag =>
      cases hStates with
      | stable hStable =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ]

/--
Canonical forward phases can invoke the existing phase weak bisimulation
without an externally supplied compatibility premise.
-/
theorem detailedBoundPayloadForwardMatch_of_canonicalRuntimeInvariant
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    (hSourceStep :
      DTR.DetailedBoundPayloadStep
        server
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hTargetInvariant :
      DetailedBoundPayloadTargetRuntimeInvariant
        server
        targetBefore)
    (hCanonical :
      DetailedBoundPayloadForwardCanonicalPhase
        sourceBefore
        targetBefore) :
    DetailedBoundPayloadForwardMatch
      server
      sourceLabel
      sourceAfter
      targetBefore := by

  exact
    (detailedBoundPayload_phaseWeakBisimulation
      server).forwardStep
        hSourceStep
        hStates
        (detailedBoundPayloadForwardPhaseCompatible_of_canonicalRuntimeInvariant
          hSourceStep
          hStates
          hTargetInvariant
          hCanonical)

/--
Backward exact phases can invoke the existing phase weak bisimulation without
an externally supplied compatibility premise.
-/
theorem detailedBoundPayloadBackwardMatch_of_correspondence
    {server : DTR.PayloadMessageServer}
    {sourceBefore :
      DTR.DetailedBoundPayloadState
        server}
    {targetBefore targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    {targetLabel :
      LF.DetailedBoundPayloadLabel}
    (hTargetStep :
      LF.DetailedBoundPayloadStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore) :
    DetailedBoundPayloadBackwardMatch
      server
      targetLabel
      targetAfter
      sourceBefore := by

  exact
    (detailedBoundPayload_phaseWeakBisimulation
      server).backwardStep
        hTargetStep
        hStates
        (detailedBoundPayloadBackwardPhaseCompatible_of_correspondence
          hTargetStep
          hStates)

end Correctness
end Relico
