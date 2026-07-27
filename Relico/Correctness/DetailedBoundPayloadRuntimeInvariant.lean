import Relico.Correctness.DetailedBoundPayloadInvocationEntry
import Relico.Correctness.PriorityEligibility
import Relico.DTR.BoundPayloadTimingWellFormed
import Relico.LF.BoundPayloadRuntimeInvariant

set_option autoImplicit false

namespace Relico

namespace Correctness

/--
A positive-delay LF schedule resets the generated tag microstep to zero.
-/
theorem boundPayloadSchedule_positive_microstepZero
    (tag : LF.Tag)
    (delay : Delay)
    (hPositive :
      0 < delay.value) :
    (LF.Tag.schedule
      tag
      delay).microstep =
        0 := by

  rw [
    LF.Tag.schedule_positive
      tag
      delay
      hPositive
  ]

/--
A zero-delay schedule necessarily creates a positive microstep.

Thus an unrestricted zero-delay internal self-send does not preserve the
zero-microstep queue property.
-/
theorem boundPayloadSchedule_zero_microstepPositive
    (tag : LF.Tag) :
    0 <
      (LF.Tag.schedule
        tag
        ⟨0⟩).microstep := by

  rw [
    LF.Tag.schedule_zero
  ]

  exact
    Nat.zero_lt_succ
      tag.microstep

/--
The generated state after dispatching the canonical external invocation
satisfies the target runtime invariant for every invocation delay.

The queue is empty. Consequently, a positive current microstep caused by a
zero-delay invocation is harmless: every queued action is strictly future
vacuously.
-/
theorem boundPayloadInvocationDispatched_targetRuntimeInvariant
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore) :
    LF.BoundPayloadState.RuntimeInvariant
      ((Translation.compilePayloadMessageServer
          server).invocationDispatchedBoundPayloadState
        initialStateValue
        payload
        delay
        boundParameters) := by

  refine {
    pendingMicrostepsZero := ?_
    currentZeroOrPendingStrictlyFuture :=
      Or.inr ?_
  }

  · intro action hAction

    simp [
      LF.PayloadReaction.invocationDispatchedBoundPayloadState
    ] at hAction

  · intro action hAction

    simp [
      LF.PayloadReaction.invocationDispatchedBoundPayloadState
    ] at hAction

/--
A source payload dispatch from corresponding states automatically satisfies
forward dispatch compatibility when the target runtime invariant holds.

Queue correspondence identifies the matching target occurrence and residual
queue. Source earliest-time selection transports to target complete-tag
selection because every queued target action has microstep zero.

For the not-past obligation:

- when the current target microstep is zero, source metric-time order lifts
  directly to complete-tag order;
- otherwise the invariant guarantees that every pending action is strictly
  later in metric time.
-/
theorem boundPayloadForwardDispatchCompatible_of_runtimeInvariant
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {targetBefore :
      LF.BoundPayloadState}
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
    (hTargetInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetBefore) :
    BoundPayloadForwardDispatchCompatible
      selectedMessage
      sourceAfter.pendingMessages
      targetBefore := by

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

      rcases
          PayloadQueueCorresponds.remove_source
            hStates.pendingEvents
            hSourceRemoved
        with
          ⟨selectedAction,
           targetRemaining,
           hTargetRemoved,
           hSelectedCorresponds,
           hRemainingCorresponds⟩

      have hTargetSelected :
          selectedAction ∈
            targetBefore.pendingActions :=

        Occurrence.RemovesOne.selected_mem
          hTargetRemoved

      have hTargetEarliest :
          LF.IsEarliest
            selectedAction
            targetBefore.pendingActions :=

        sourceEarliest_implies_targetEarliest_of_allMicrostepsZero
          (PayloadQueueCorresponds.toQueueCorresponds
            hStates.pendingEvents)
          hSelectedCorresponds.occurrence
          hTargetSelected
          hSourceEarliest
          hTargetInvariant.pendingMicrostepsZero

      have hSelectedMicrostepZero :
          selectedAction.tag.microstep =
            0 :=

        hTargetInvariant.pendingMicrostepsZero
          selectedAction
          hTargetSelected

      have hMetricTimeOrder :
          targetBefore.currentTag.time ≤
            selectedAction.tag.time := by

        calc
          targetBefore.currentTag.time =
              currentTime :=
            hStates.currentTime

          _ ≤
              selectedMessage.arrivalTime :=
            hSourceNotPast

          _ =
              selectedAction.tag.time :=
            hSelectedCorresponds.occurrence.logicalTime.symm

      have hTargetNotPast :
          LF.Tag.PrecedesOrEqual
            targetBefore.currentTag
            selectedAction.tag := by

        rcases
            hTargetInvariant.currentZeroOrPendingStrictlyFuture
          with
            hCurrentMicrostepZero |
            hPendingStrictlyFuture

        · by_cases hSameTime :
              targetBefore.currentTag.time =
                selectedAction.tag.time

          · apply
              LF.Tag.precedesOrEqual_same_time
                hSameTime

            rw [
              hCurrentMicrostepZero,
              hSelectedMicrostepZero
            ]

            exact
              Nat.zero_le 0

          · exact
              Or.inl
                (Nat.lt_of_le_of_ne
                  hMetricTimeOrder
                  hSameTime)

        · exact
            Or.inl
              (hPendingStrictlyFuture
                selectedAction
                hTargetSelected)

      exact
        ⟨selectedAction,
         targetRemaining,
         hTargetRemoved,
         hSelectedCorresponds,
         hRemainingCorresponds,
         hTargetEarliest,
         hTargetNotPast⟩

/--
The canonical invocation boundary yields automatic compatibility in two stages:

1. the singleton entry occurrence uses the explicit I4-A2 theorem;
2. after dispatch, the target runtime invariant is established without
   restricting the external invocation delay.
-/
theorem boundPayloadInvocation_runtimeBoundary_package
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore)
    (_hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    BoundPayloadForwardDispatchCompatible
        (server.invocationPendingMessage
          payload
          delay)
        []
        ((Translation.compilePayloadMessageServer
            server).invocationBoundPayloadState
          initialStateValue
          payload
          delay) ∧
      LF.BoundPayloadState.RuntimeInvariant
        ((Translation.compilePayloadMessageServer
            server).invocationDispatchedBoundPayloadState
          initialStateValue
          payload
          delay
          boundParameters) := by

  exact
    ⟨boundPayloadInvocation_forwardDispatchCompatible
       server
       initialStateValue
       payload
       delay,
     boundPayloadInvocationDispatched_targetRuntimeInvariant
       server
       initialStateValue
       payload
       delay
       boundParameters⟩

end Correctness

end Relico
