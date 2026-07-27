import Relico.Correctness.DetailedBoundPayloadInitialization
import Relico.Correctness.DetailedBoundPayloadInvocationEntry
import Relico.Correctness.DetailedBoundPayloadRuntimeInvariant
import Relico.Correctness.DetailedBoundPayloadInvariantMatches
import Relico.Correctness.DetailedBoundPayloadInvariantCarryingFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Canonical idle source initialization satisfies the detailed source runtime
invariant because its active body is empty.
-/
theorem detailedBoundPayloadInitialSourceRuntimeInvariant
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    DetailedBoundPayloadSourceRuntimeInvariant
      server
      (server.initialDetailedBoundPayloadState
        initialStateValue) := by

  apply
    detailedBoundPayloadSourceRuntimeInvariant_stable.mpr

  change
    DTR.BoundPayloadBody.PriorityTimingWellFormed
      []

  exact
    DTR.BoundPayloadBody.priorityTimingWellFormed_nil

/--
Canonical idle generated-LF initialization satisfies the target runtime
invariant. Its queue is empty and its current microstep is zero.
-/
theorem detailedBoundPayloadInitialTargetRuntimeInvariant
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    DetailedBoundPayloadTargetRuntimeInvariant
      server
      ((Translation.compilePayloadMessageServer
          server).initialDetailedBoundPayloadState
        initialStateValue) := by

  apply
    detailedBoundPayloadTargetRuntimeInvariant_stable.mpr

  refine {
    pendingMicrostepsZero := ?_
    currentZeroOrPendingStrictlyFuture :=
      Or.inl ?_
  }

  · intro action hAction

    simp [
      LF.PayloadReaction.initialBoundPayloadState
    ] at hAction

  · rfl

/--
Canonical idle initialization provides all four boundary premises required by
invariant-carrying finite forward execution.
-/
theorem detailedBoundPayloadInitialStates_runtimeBoundary
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    DetailedBoundPayloadStateCorresponds
        server
        (server.initialDetailedBoundPayloadState
          initialStateValue)
        ((Translation.compilePayloadMessageServer
            server).initialDetailedBoundPayloadState
          initialStateValue) ∧

      DetailedBoundPayloadSourceRuntimeInvariant
        server
        (server.initialDetailedBoundPayloadState
          initialStateValue) ∧

      DetailedBoundPayloadTargetRuntimeInvariant
        server
        ((Translation.compilePayloadMessageServer
            server).initialDetailedBoundPayloadState
          initialStateValue) ∧

      DetailedBoundPayloadForwardCanonicalPhase
        (server.initialDetailedBoundPayloadState
          initialStateValue)
        ((Translation.compilePayloadMessageServer
            server).initialDetailedBoundPayloadState
          initialStateValue) := by

  exact
    ⟨detailedBoundPayloadInitialStates_correspond
       server
       initialStateValue,
     detailedBoundPayloadInitialSourceRuntimeInvariant
       server
       initialStateValue,
     detailedBoundPayloadInitialTargetRuntimeInvariant
       server
       initialStateValue,
     detailedBoundPayloadForwardCanonicalPhase_stable⟩

/--
The source invocation-ready state satisfies the phase-aware source invariant
for every external invocation delay because its active body is empty.
-/
theorem detailedBoundPayloadInvocationSourceRuntimeInvariant
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
    DetailedBoundPayloadSourceRuntimeInvariant
      server
      (server.invocationDetailedBoundPayloadState
        initialStateValue
        payload
        delay) := by

  apply
    detailedBoundPayloadSourceRuntimeInvariant_stable.mpr

  change
    DTR.BoundPayloadBody.PriorityTimingWellFormed
      []

  exact
    DTR.BoundPayloadBody.priorityTimingWellFormed_nil

/--
A positive-delay invocation-ready LF state satisfies the target runtime
invariant.

Its singleton pending action has microstep zero, and the current initial tag
also has microstep zero.
-/
theorem detailedBoundPayloadInvocationTargetRuntimeInvariant_of_positive
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (hPositive :
      0 < delay.value) :
    DetailedBoundPayloadTargetRuntimeInvariant
      server
      ((Translation.compilePayloadMessageServer
          server).invocationDetailedBoundPayloadState
        initialStateValue
        payload
        delay) := by

  apply
    detailedBoundPayloadTargetRuntimeInvariant_stable.mpr

  refine {
    pendingMicrostepsZero := ?_
    currentZeroOrPendingStrictlyFuture :=
      Or.inl ?_
  }

  · intro action hAction

    have hSingleton :
        action =
          (Translation.compilePayloadMessageServer
            server).invocationPendingAction
              payload
              delay := by

      simpa [
        LF.PayloadReaction.invocationBoundPayloadState
      ] using
        hAction

    subst action

    simpa [
      LF.PayloadReaction.invocationPendingAction,
      LF.PendingAction.scheduleWithPayload
    ] using
      (boundPayloadSchedule_positive_microstepZero
        LF.initialTag
        delay
        hPositive)

  · rfl

/--
The zero-delay invocation-ready LF state does not satisfy the target runtime
invariant.

Its singleton queued action has a positive microstep, contradicting the
invariant's `pendingMicrostepsZero` field.
-/
theorem detailedBoundPayloadInvocationTargetRuntimeInvariant_zero_impossible
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload) :
    ¬ DetailedBoundPayloadTargetRuntimeInvariant
        server
        ((Translation.compilePayloadMessageServer
            server).invocationDetailedBoundPayloadState
          initialStateValue
          payload
          ⟨0⟩) := by

  intro hDetailedInvariant

  have hRuntimeInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        ((Translation.compilePayloadMessageServer
            server).invocationBoundPayloadState
          initialStateValue
          payload
          ⟨0⟩) :=

    detailedBoundPayloadTargetRuntimeInvariant_stable.mp
      hDetailedInvariant

  have hMember :
      (Translation.compilePayloadMessageServer
          server).invocationPendingAction
            payload
            ⟨0⟩ ∈
        ((Translation.compilePayloadMessageServer
            server).invocationBoundPayloadState
          initialStateValue
          payload
          ⟨0⟩).pendingActions := by

    simp [
      LF.PayloadReaction.invocationBoundPayloadState
    ]

  have hMicrostepZero :
      ((Translation.compilePayloadMessageServer
          server).invocationPendingAction
        payload
        ⟨0⟩).tag.microstep =
        0 :=

    hRuntimeInvariant.pendingMicrostepsZero
      ((Translation.compilePayloadMessageServer
        server).invocationPendingAction
          payload
          ⟨0⟩)
      hMember

  have hMicrostepPositive :
      0 <
        ((Translation.compilePayloadMessageServer
            server).invocationPendingAction
          payload
          ⟨0⟩).tag.microstep := by

    change
      0 <
        (LF.Tag.schedule
          LF.initialTag
          ⟨0⟩).microstep

    exact
      boundPayloadSchedule_zero_microstepPositive
        LF.initialTag

  exact
    (Nat.ne_of_gt
      hMicrostepPositive)
      hMicrostepZero

/--
For positive external delay, invocation entry supplies all four premises of
the generic finite invariant theorem.
-/
theorem detailedBoundPayloadInvocationStates_runtimeBoundary_of_positive
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (hPositive :
      0 < delay.value) :
    DetailedBoundPayloadStateCorresponds
        server
        (server.invocationDetailedBoundPayloadState
          initialStateValue
          payload
          delay)
        ((Translation.compilePayloadMessageServer
            server).invocationDetailedBoundPayloadState
          initialStateValue
          payload
          delay) ∧

      DetailedBoundPayloadSourceRuntimeInvariant
        server
        (server.invocationDetailedBoundPayloadState
          initialStateValue
          payload
          delay) ∧

      DetailedBoundPayloadTargetRuntimeInvariant
        server
        ((Translation.compilePayloadMessageServer
            server).invocationDetailedBoundPayloadState
          initialStateValue
          payload
          delay) ∧

      DetailedBoundPayloadForwardCanonicalPhase
        (server.invocationDetailedBoundPayloadState
          initialStateValue
          payload
          delay)
        ((Translation.compilePayloadMessageServer
            server).invocationDetailedBoundPayloadState
          initialStateValue
          payload
          delay) := by

  exact
    ⟨detailedBoundPayloadInvocationStates_correspond
       server
       initialStateValue
       payload
       delay,
     detailedBoundPayloadInvocationSourceRuntimeInvariant
       server
       initialStateValue
       payload
       delay,
     detailedBoundPayloadInvocationTargetRuntimeInvariant_of_positive
       server
       initialStateValue
       payload
       delay
       hPositive,
     detailedBoundPayloadForwardCanonicalPhase_stable⟩

/--
Top-level finite forward correctness from canonical idle initialization.
-/
theorem detailedBoundPayloadInitialSteps_forward
    {server : DTR.PayloadMessageServer}
    {initialStateValue : Int}
    {sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    {sourceLabels :
      List DTR.DetailedBoundPayloadLabel}
    (hSourceSteps :
      DTR.DetailedBoundPayloadSteps
        server
        (server.initialDetailedBoundPayloadState
          initialStateValue)
        sourceLabels
        sourceAfter)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
    ∃ targetLabels targetAfter,
      LF.DetailedBoundPayloadWeakSteps
          (Translation.compilePayloadMessageServer
            server)
          ((Translation.compilePayloadMessageServer
              server).initialDetailedBoundPayloadState
            initialStateValue)
          targetLabels
          targetAfter ∧

        DetailedBoundPayloadWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧

        DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧

        DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            sourceLabels)
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) ∧

        DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter := by

  rcases
      detailedBoundPayloadInitialStates_runtimeBoundary
        server
        initialStateValue
    with
      ⟨hStates,
       hSourceInvariant,
       hTargetInvariant,
       hCanonical⟩

  exact
    detailedBoundPayloadSteps_forward_with_invariants
      hSourceSteps
      hStates
      hSourceInvariant
      hTargetInvariant
      hCanonical
      hServerTiming

/--
For positive external delay, top-level finite forward correctness also starts
directly from the stable invocation-ready states.
-/
theorem detailedBoundPayloadInvocationSteps_forward_of_positive
    {server : DTR.PayloadMessageServer}
    {initialStateValue : Int}
    {payload : Payload}
    {delay : Delay}
    {sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    {sourceLabels :
      List DTR.DetailedBoundPayloadLabel}
    (hSourceSteps :
      DTR.DetailedBoundPayloadSteps
        server
        (server.invocationDetailedBoundPayloadState
          initialStateValue
          payload
          delay)
        sourceLabels
        sourceAfter)
    (hPositive :
      0 < delay.value)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
    ∃ targetLabels targetAfter,
      LF.DetailedBoundPayloadWeakSteps
          (Translation.compilePayloadMessageServer
            server)
          ((Translation.compilePayloadMessageServer
              server).invocationDetailedBoundPayloadState
            initialStateValue
            payload
            delay)
          targetLabels
          targetAfter ∧

        DetailedBoundPayloadWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧

        DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧

        DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            sourceLabels)
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) ∧

        DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter := by

  rcases
      detailedBoundPayloadInvocationStates_runtimeBoundary_of_positive
        server
        initialStateValue
        payload
        delay
        hPositive
    with
      ⟨hStates,
       hSourceInvariant,
       hTargetInvariant,
       hCanonical⟩

  exact
    detailedBoundPayloadSteps_forward_with_invariants
      hSourceSteps
      hStates
      hSourceInvariant
      hTargetInvariant
      hCanonical
      hServerTiming


/--
The exact source-label prefix used when an external invocation is completely
accepted.

A zero-delay invocation is consumed in one same-time source step. A positive
delay first advances metric time and is then consumed from the source
dispatch-ready phase.
-/
def DetailedBoundPayloadInvocationPrefixLabels
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore) :
    List DTR.DetailedBoundPayloadLabel :=

  if delay.value = 0 then
    [
      DTR.DetailedBoundPayloadLabel.consume
        (server.invocationPendingMessage
          payload
          delay)
    ]
  else
    [
      DTR.DetailedBoundPayloadLabel.timeAdvance
        (server.invocationBoundPayloadState
          initialStateValue
          payload
          delay).currentTime
        (server.invocationDispatchedBoundPayloadState
          initialStateValue
          payload
          delay
          boundParameters).currentTime,

      DTR.DetailedBoundPayloadLabel.consume
        (server.invocationPendingMessage
          payload
          delay)
    ]

/--
A positive-delay invocation advances source metric time when it is dispatched.
-/
theorem boundPayloadInvocation_sourceFuture_of_positive
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore)
    (hPositive :
      0 < delay.value) :
    (server.invocationBoundPayloadState
        initialStateValue
        payload
        delay).currentTime <
      (server.invocationDispatchedBoundPayloadState
        initialStateValue
        payload
        delay
        boundParameters).currentTime := by

  change
    0 <
      0 + delay.value

  rw [
    Nat.zero_add
  ]

  exact
    hPositive

/--
A zero-delay invocation preserves source metric time when it is dispatched.
-/
theorem boundPayloadInvocation_sourceSameTime_zero
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (boundParameters : ParameterStore) :
    (server.invocationBoundPayloadState
        initialStateValue
        payload
        ⟨0⟩).currentTime =
      (server.invocationDispatchedBoundPayloadState
        initialStateValue
        payload
        ⟨0⟩
        boundParameters).currentTime := by

  rfl

/--
The zero-delay generated-LF invocation dispatch preserves metric time.
-/
theorem boundPayloadInvocation_targetSameTime_zero
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (boundParameters : ParameterStore) :
    ((Translation.compilePayloadMessageServer
        server).invocationBoundPayloadState
      initialStateValue
      payload
      ⟨0⟩).currentTag.time =
    ((Translation.compilePayloadMessageServer
        server).invocationDispatchedBoundPayloadState
      initialStateValue
      payload
      ⟨0⟩
      boundParameters).currentTag.time := by

  change
    LF.initialTag.time =
      (LF.Tag.schedule
        LF.initialTag
        ⟨0⟩).time

  rw [
    LF.Tag.schedule_zero
  ]

/--
The zero-delay generated-LF invocation dispatch strictly advances the
microstep.
-/
theorem boundPayloadInvocation_targetMicrostepLater_zero
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (boundParameters : ParameterStore) :
    ((Translation.compilePayloadMessageServer
        server).invocationBoundPayloadState
      initialStateValue
      payload
      ⟨0⟩).currentTag.microstep <
    ((Translation.compilePayloadMessageServer
        server).invocationDispatchedBoundPayloadState
      initialStateValue
      payload
      ⟨0⟩
      boundParameters).currentTag.microstep := by

  change
    0 <
      (LF.Tag.schedule
        LF.initialTag
        ⟨0⟩).microstep

  exact
    boundPayloadSchedule_zero_microstepPositive
      LF.initialTag

/--
Unrestricted external-invocation correctness after crossing the invocation
boundary.

The premise `hSourceTail` starts at the stable state obtained after the
singleton invocation has been dispatched and consumed.

The theorem constructs the complete source execution from the invocation-ready
state:

- zero delay contributes one `consume` label;
- positive delay contributes `timeAdvance` followed by `consume`.

It simultaneously constructs the generated-LF weak execution from the
invocation-ready target state and carries all endpoint properties required for
continued recursive execution.
-/
theorem detailedBoundPayloadInvocationTailSteps_forward
    {server : DTR.PayloadMessageServer}
    {initialStateValue : Int}
    {payload : Payload}
    {delay : Delay}
    {boundParameters : ParameterStore}
    {sourceTailLabels :
      List DTR.DetailedBoundPayloadLabel}
    {sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hSourceTail :
      DTR.DetailedBoundPayloadSteps
        server
        (.stable
          (server.invocationDispatchedBoundPayloadState
            initialStateValue
            payload
            delay
            boundParameters))
        sourceTailLabels
        sourceAfter)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
    ∃ targetLabels targetAfter,
      DTR.DetailedBoundPayloadSteps
          server
          (server.invocationDetailedBoundPayloadState
            initialStateValue
            payload
            delay)
          (DetailedBoundPayloadInvocationPrefixLabels
              server
              initialStateValue
              payload
              delay
              boundParameters ++
            sourceTailLabels)
          sourceAfter ∧

        LF.DetailedBoundPayloadWeakSteps
          (Translation.compilePayloadMessageServer
            server)
          ((Translation.compilePayloadMessageServer
              server).invocationDetailedBoundPayloadState
            initialStateValue
            payload
            delay)
          targetLabels
          targetAfter ∧

        DetailedBoundPayloadWeakLabelTraceCorresponds
          (DetailedBoundPayloadInvocationPrefixLabels
              server
              initialStateValue
              payload
              delay
              boundParameters ++
            sourceTailLabels)
          targetLabels ∧

        DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧

        DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            (DetailedBoundPayloadInvocationPrefixLabels
                server
                initialStateValue
                payload
                delay
                boundParameters ++
              sourceTailLabels))
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) ∧

        DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter := by

  by_cases hZero :
      delay.value = 0

  · have hDelay :
        delay =
          ⟨0⟩ := by

      cases delay with
      | mk value =>
          simp only at hZero
          subst value
          rfl

    subst delay

    let sourceBefore :
        DTR.BoundPayloadState :=
      server.invocationBoundPayloadState
        initialStateValue
        payload
        ⟨0⟩

    let selectedMessage :
        DTR.PendingMessage :=
      server.invocationPendingMessage
        payload
        ⟨0⟩

    let sourceDispatched :
        DTR.BoundPayloadState :=
      server.invocationDispatchedBoundPayloadState
        initialStateValue
        payload
        ⟨0⟩
        boundParameters

    let targetBefore :
        LF.BoundPayloadState :=
      (Translation.compilePayloadMessageServer
        server).invocationBoundPayloadState
          initialStateValue
          payload
          ⟨0⟩

    let selectedAction :
        LF.PendingAction :=
      (Translation.compilePayloadMessageServer
        server).invocationPendingAction
          payload
          ⟨0⟩

    let targetDispatched :
        LF.BoundPayloadState :=
      (Translation.compilePayloadMessageServer
        server).invocationDispatchedBoundPayloadState
          initialStateValue
          payload
          ⟨0⟩
          boundParameters

    have hSourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceDispatched := by

      exact
        boundPayloadInvocation_sourceDispatch
          server
          initialStateValue
          payload
          ⟨0⟩
          boundParameters
          hBind

    have hTargetDispatch :
        LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetDispatched := by

      exact
        boundPayloadInvocation_targetDispatch
          server
          initialStateValue
          payload
          ⟨0⟩
          boundParameters
          hBind

    have hSourceSameTime :
        sourceBefore.currentTime =
          sourceDispatched.currentTime := by

      exact
        boundPayloadInvocation_sourceSameTime_zero
          server
          initialStateValue
          payload
          boundParameters

    have hSourceConsume :
        DTR.DetailedBoundPayloadStep
          server
          (.stable sourceBefore)
          (.consume selectedMessage)
          (.stable sourceDispatched) :=

      DTR.DetailedBoundPayloadStep.consumeNow
        hSourceDispatch
        hSourceSameTime

    have hTargetSameTime :
        targetBefore.currentTag.time =
          targetDispatched.currentTag.time := by

      exact
        boundPayloadInvocation_targetSameTime_zero
          server
          initialStateValue
          payload
          boundParameters

    have hTargetLaterMicrostep :
        targetBefore.currentTag.microstep <
          targetDispatched.currentTag.microstep := by

      exact
        boundPayloadInvocation_targetMicrostepLater_zero
          server
          initialStateValue
          payload
          boundParameters

    have hTargetMicrostep :
        LF.DetailedBoundPayloadStep
          (Translation.compilePayloadMessageServer
            server)
          (.stable targetBefore)
          (.microstepAdvance
            targetBefore.currentTag
            targetDispatched.currentTag)
          (.dispatchReady
            targetBefore
            selectedAction
            targetDispatched
            hTargetDispatch) :=

      LF.DetailedBoundPayloadStep.microstepSameTime
        hTargetDispatch
        hTargetSameTime
        hTargetLaterMicrostep

    have hTargetInternalPrefix :
        LF.DetailedBoundPayloadTauSteps
          (Translation.compilePayloadMessageServer
            server)
          (.stable targetBefore)
          (.dispatchReady
            targetBefore
            selectedAction
            targetDispatched
            hTargetDispatch) :=

      LF.detailedBoundPayloadMicrostep_to_tauSteps
        hTargetMicrostep

    have hTargetConsume :
        LF.DetailedBoundPayloadStep
          (Translation.compilePayloadMessageServer
            server)
          (.dispatchReady
            targetBefore
            selectedAction
            targetDispatched
            hTargetDispatch)
          (.consume selectedAction)
          (.stable targetDispatched) :=

      LF.DetailedBoundPayloadStep.consumeReady
        hTargetDispatch

    have hTargetInvocationWeak :
        LF.DetailedBoundPayloadWeakStep
          (Translation.compilePayloadMessageServer
            server)
          (.stable targetBefore)
          (.consume selectedAction)
          (.stable targetDispatched) :=

      Common.WeakStep.visible
        (LF.detailedBoundPayload_consume_visible
          selectedAction)
        hTargetInternalPrefix
        hTargetConsume
        (Common.TauSteps.refl
          (LF.DetailedBoundPayloadState.stable
            targetDispatched))

    have hHeadLabels :
        DetailedBoundPayloadLabelCorresponds
          (.consume selectedMessage)
          (.consume selectedAction) :=

      DetailedBoundPayloadLabelCorresponds.consume
        (boundPayloadInvocationPending_correspond
          server
          payload
          ⟨0⟩)

    have hDispatchedStates :
        DetailedBoundPayloadStateCorresponds
          server
          (.stable sourceDispatched)
          (.stable targetDispatched) :=

      DetailedBoundPayloadStateCorresponds.stable
        (boundPayloadInvocationDispatchedStates_correspond
          server
          initialStateValue
          payload
          ⟨0⟩
          boundParameters)

    have hDispatchedSourceInvariant :
        DetailedBoundPayloadSourceRuntimeInvariant
          server
          (.stable sourceDispatched) := by

      apply
        detailedBoundPayloadSourceRuntimeInvariant_stable.mpr

      change
        DTR.BoundPayloadBody.PriorityTimingWellFormed
          server.body

      exact
        hServerTiming

    have hDispatchedTargetInvariant :
        DetailedBoundPayloadTargetRuntimeInvariant
          server
          (.stable targetDispatched) := by

      apply
        detailedBoundPayloadTargetRuntimeInvariant_stable.mpr

      exact
        boundPayloadInvocationDispatched_targetRuntimeInvariant
          server
          initialStateValue
          payload
          ⟨0⟩
          boundParameters

    have hDispatchedCanonical :
        DetailedBoundPayloadForwardCanonicalPhase
          (server := server)
          (.stable sourceDispatched)
          (.stable targetDispatched) :=

      detailedBoundPayloadForwardCanonicalPhase_stable
        (server := server)

    rcases
        detailedBoundPayloadSteps_forward_with_invariants
          hSourceTail
          hDispatchedStates
          hDispatchedSourceInvariant
          hDispatchedTargetInvariant
          hDispatchedCanonical
          hServerTiming
      with
        ⟨targetTailLabels,
         targetAfter,
         hTargetTail,
         hTailLabels,
         hFinalStates,
         hObservableTail,
         hFinalSourceInvariant,
         hFinalTargetInvariant,
         hFinalCanonical⟩

    have hCompleteSource :
        DTR.DetailedBoundPayloadSteps
          server
          (server.invocationDetailedBoundPayloadState
            initialStateValue
            payload
            ⟨0⟩)
          (DetailedBoundPayloadInvocationPrefixLabels
              server
              initialStateValue
              payload
              ⟨0⟩
              boundParameters ++
            sourceTailLabels)
          sourceAfter := by

      simpa [
        DetailedBoundPayloadInvocationPrefixLabels,
        DTR.PayloadMessageServer.invocationDetailedBoundPayloadState,
        sourceBefore,
        selectedMessage,
        sourceDispatched
      ] using
        DTR.DetailedBoundPayloadSteps.cons
          hSourceConsume
          hSourceTail

    have hCompleteTrace :
        DetailedBoundPayloadWeakLabelTraceCorresponds
          (DetailedBoundPayloadInvocationPrefixLabels
              server
              initialStateValue
              payload
              ⟨0⟩
              boundParameters ++
            sourceTailLabels)
          (LF.DetailedBoundPayloadLabel.consume
              selectedAction ::
            targetTailLabels) := by

      simpa [
        DetailedBoundPayloadInvocationPrefixLabels,
        selectedMessage
      ] using
        DetailedBoundPayloadWeakLabelTraceCorresponds.cons
          hHeadLabels
          hTailLabels

    exact
      ⟨LF.DetailedBoundPayloadLabel.consume
          selectedAction ::
          targetTailLabels,
       targetAfter,
       hCompleteSource,
       Common.WeakSteps.cons
         hTargetInvocationWeak
         hTargetTail,
       hCompleteTrace,
       hFinalStates,
       hCompleteTrace.observableProjection,
       hFinalSourceInvariant,
       hFinalTargetInvariant,
       hFinalCanonical⟩

  · have hPositive :
        0 < delay.value :=
      Nat.pos_of_ne_zero
        hZero

    let sourceBefore :
        DTR.BoundPayloadState :=
      server.invocationBoundPayloadState
        initialStateValue
        payload
        delay

    let selectedMessage :
        DTR.PendingMessage :=
      server.invocationPendingMessage
        payload
        delay

    let sourceDispatched :
        DTR.BoundPayloadState :=
      server.invocationDispatchedBoundPayloadState
        initialStateValue
        payload
        delay
        boundParameters

    have hSourceDispatch :
        DTR.BoundPayloadDispatchStep
          server
          sourceBefore
          selectedMessage
          sourceDispatched := by

      exact
        boundPayloadInvocation_sourceDispatch
          server
          initialStateValue
          payload
          delay
          boundParameters
          hBind

    have hSourceFuture :
        sourceBefore.currentTime <
          sourceDispatched.currentTime := by

      exact
        boundPayloadInvocation_sourceFuture_of_positive
          server
          initialStateValue
          payload
          delay
          boundParameters
          hPositive

    have hSourceTimeAdvance :
        DTR.DetailedBoundPayloadStep
          server
          (.stable sourceBefore)
          (.timeAdvance
            sourceBefore.currentTime
            sourceDispatched.currentTime)
          (.dispatchReady
            sourceBefore
            selectedMessage
            sourceDispatched
            hSourceDispatch) :=

      DTR.DetailedBoundPayloadStep.timeAdvance
        hSourceDispatch
        hSourceFuture

    have hSourceConsume :
        DTR.DetailedBoundPayloadStep
          server
          (.dispatchReady
            sourceBefore
            selectedMessage
            sourceDispatched
            hSourceDispatch)
          (.consume selectedMessage)
          (.stable sourceDispatched) :=

      DTR.DetailedBoundPayloadStep.consumeReady
        hSourceDispatch

    have hCompleteSource :
        DTR.DetailedBoundPayloadSteps
          server
          (server.invocationDetailedBoundPayloadState
            initialStateValue
            payload
            delay)
          (DetailedBoundPayloadInvocationPrefixLabels
              server
              initialStateValue
              payload
              delay
              boundParameters ++
            sourceTailLabels)
          sourceAfter := by

      simpa [
        DetailedBoundPayloadInvocationPrefixLabels,
        DTR.PayloadMessageServer.invocationDetailedBoundPayloadState,
        hZero,
        sourceBefore,
        selectedMessage,
        sourceDispatched
      ] using
        DTR.DetailedBoundPayloadSteps.cons
          hSourceTimeAdvance
          (DTR.DetailedBoundPayloadSteps.cons
            hSourceConsume
            hSourceTail)

    rcases
        detailedBoundPayloadInvocationSteps_forward_of_positive
          hCompleteSource
          hPositive
          hServerTiming
      with
        ⟨targetLabels,
         targetAfter,
         hTargetSteps,
         hTrace,
         hFinalStates,
         hObservable,
         hFinalSourceInvariant,
         hFinalTargetInvariant,
         hFinalCanonical⟩

    exact
      ⟨targetLabels,
       targetAfter,
       hCompleteSource,
       hTargetSteps,
       hTrace,
       hFinalStates,
       hObservable,
       hFinalSourceInvariant,
       hFinalTargetInvariant,
       hFinalCanonical⟩


end Correctness
end Relico
