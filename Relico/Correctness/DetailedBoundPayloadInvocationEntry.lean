import Relico.Correctness.DetailedBoundPayloadInitialization
import Relico.Correctness.DetailedBoundPayloadFiniteWeakExecution

set_option autoImplicit false

namespace Relico

namespace DTR

/--
The source occurrence supplied at the canonical payload invocation boundary.
-/
def PayloadMessageServer.invocationPendingMessage
    (server : DTR.PayloadMessageServer)
    (payload : Payload)
    (delay : Delay) :
    DTR.PendingMessage :=

  DTR.PendingMessage.scheduleWithPayload
    0
    server.name
    payload
    delay

/--
Canonical source invocation-ready state.

It extends the idle payload initialization with exactly one pending occurrence.
No activation has started yet.
-/
def PayloadMessageServer.invocationBoundPayloadState
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
    DTR.BoundPayloadState := {

  currentTime :=
    0

  stateValue :=
    initialStateValue

  parameters :=
    ParameterStore.empty

  pendingMessages := [
    server.invocationPendingMessage
      payload
      delay
  ]

  activeBody :=
    []
}

/--
Stable detailed wrapper around the source invocation-ready state.
-/
def PayloadMessageServer.invocationDetailedBoundPayloadState
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
    DTR.DetailedBoundPayloadState server :=

  DTR.DetailedBoundPayloadState.stable
    (server.invocationBoundPayloadState
      initialStateValue
      payload
      delay)

/--
Source runtime state after the singleton invocation occurrence is dispatched.
-/
def PayloadMessageServer.invocationDispatchedBoundPayloadState
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore) :
    DTR.BoundPayloadState := {

  currentTime :=
    (server.invocationPendingMessage
      payload
      delay).arrivalTime

  stateValue :=
    initialStateValue

  parameters :=
    boundParameters

  pendingMessages :=
    []

  activeBody :=
    server.body
}

end DTR

namespace LF

/--
The generated-LF action occurrence corresponding to one source invocation.
-/
def PayloadReaction.invocationPendingAction
    (reaction : LF.PayloadReaction)
    (payload : Payload)
    (delay : Delay) :
    LF.PendingAction :=

  LF.PendingAction.scheduleWithPayload
    LF.initialTag
    reaction.logicalAction
    payload
    delay

/--
Canonical generated-LF invocation-ready state.

It extends the idle generated state with exactly one pending logical-action
occurrence.
-/
def PayloadReaction.invocationBoundPayloadState
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
    LF.BoundPayloadState := {

  currentTag :=
    LF.initialTag

  stateValue :=
    initialStateValue

  parameters :=
    ParameterStore.empty

  pendingActions := [
    reaction.invocationPendingAction
      payload
      delay
  ]

  activeBody :=
    []
}

/--
Stable detailed wrapper around the target invocation-ready state.
-/
def PayloadReaction.invocationDetailedBoundPayloadState
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
    LF.DetailedBoundPayloadState reaction :=

  LF.DetailedBoundPayloadState.stable
    (reaction.invocationBoundPayloadState
      initialStateValue
      payload
      delay)

/--
Generated-LF runtime state after the singleton invocation action is dispatched.
-/
def PayloadReaction.invocationDispatchedBoundPayloadState
    (reaction : LF.PayloadReaction)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore) :
    LF.BoundPayloadState := {

  currentTag :=
    (reaction.invocationPendingAction
      payload
      delay).tag

  stateValue :=
    initialStateValue

  parameters :=
    boundParameters

  pendingActions :=
    []

  activeBody :=
    reaction.body
}

end LF

namespace Correctness

/--
The source invocation occurrence and generated-LF action retain identical
payloads, translated names, and logical arrival times.
-/
theorem boundPayloadInvocationPending_correspond
    (server : DTR.PayloadMessageServer)
    (payload : Payload)
    (delay : Delay) :
    PendingPayloadCorresponds
      (server.invocationPendingMessage
        payload
        delay)
      ((Translation.compilePayloadMessageServer
          server).invocationPendingAction
        payload
        delay) := by

  simpa [
    DTR.PayloadMessageServer.invocationPendingMessage,
    LF.PayloadReaction.invocationPendingAction,
    Translation.compilePayloadMessageServer
  ] using
    (pendingPayloadCorresponds_scheduleWithPayload
      (currentTime :=
        0)
      (currentTag :=
        LF.initialTag)
      (messageName :=
        server.name)
      (payload :=
        payload)
      (delay :=
        delay)
      (hCurrentTime :=
        rfl))

/--
The complete singleton pending-event queues correspond.
-/
theorem boundPayloadInvocationQueues_correspond
    (server : DTR.PayloadMessageServer)
    (payload : Payload)
    (delay : Delay) :
    PayloadQueueCorresponds
      [
        server.invocationPendingMessage
          payload
          delay
      ]
      [
        (Translation.compilePayloadMessageServer
          server).invocationPendingAction
            payload
            delay
      ] := by

  exact
    payloadQueueCorresponds_singleton
      (boundPayloadInvocationPending_correspond
        server
        payload
        delay)

/--
Canonical source and generated-LF invocation-ready runtime states correspond.
-/
theorem boundPayloadInvocationStates_correspond
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
    BoundPayloadStateCorresponds
      (server.invocationBoundPayloadState
        initialStateValue
        payload
        delay)
      ((Translation.compilePayloadMessageServer
          server).invocationBoundPayloadState
        initialStateValue
        payload
        delay) := by

  exact {
    currentTime :=
      rfl

    stateValue :=
      rfl

    parameters :=
      rfl

    pendingEvents :=
      boundPayloadInvocationQueues_correspond
        server
        payload
        delay

    activeBody :=
      rfl
  }

/--
Invocation-ready runtime correspondence lifts to stable detailed-state
correspondence.
-/
theorem detailedBoundPayloadInvocationStates_correspond
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
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
        delay) := by

  exact
    DetailedBoundPayloadStateCorresponds.stable
      (boundPayloadInvocationStates_correspond
        server
        initialStateValue
        payload
        delay)

/--
The initial generated-LF tag never follows a tag obtained by scheduling from
it.

For zero delay, scheduling advances only the microstep. For positive delay,
it advances logical time.
-/
theorem initialTag_precedesOrEqual_schedule
    (delay : Delay) :
    LF.Tag.PrecedesOrEqual
      LF.initialTag
      (LF.Tag.schedule
        LF.initialTag
        delay) := by

  by_cases hZero :
      delay.value = 0

  · apply
      LF.Tag.precedesOrEqual_same_time

    · simp [
        LF.initialTag,
        LF.Tag.schedule,
        hZero
      ]

    · simp [
        LF.initialTag,
        LF.Tag.schedule,
        hZero
      ]

  · have hPositive :
        0 < delay.value :=
      Nat.pos_of_ne_zero
        hZero

    exact
      Or.inl
        (by
          simpa [
            LF.initialTag,
            LF.Tag.schedule,
            LogicalTime.after,
            hZero
          ] using
            hPositive)

/--
A singleton source queue makes its unique occurrence earliest.
-/
theorem boundPayloadInvocationSource_isEarliest
    (server : DTR.PayloadMessageServer)
    (payload : Payload)
    (delay : Delay) :
    DTR.IsEarliest
      (server.invocationPendingMessage
        payload
        delay)
      [
        server.invocationPendingMessage
          payload
          delay
      ] := by

  intro candidate hCandidate

  simp only [
    List.mem_singleton
  ] at hCandidate

  subst candidate

  exact
    Nat.le_refl _

/--
A singleton target queue makes its unique action earliest.
-/
theorem boundPayloadInvocationTarget_isEarliest
    (server : DTR.PayloadMessageServer)
    (payload : Payload)
    (delay : Delay) :
    LF.IsEarliest
      ((Translation.compilePayloadMessageServer
          server).invocationPendingAction
        payload
        delay)
      [
        (Translation.compilePayloadMessageServer
          server).invocationPendingAction
        payload
        delay
      ] := by

  intro candidate hCandidate

  simp only [
    List.mem_singleton
  ] at hCandidate

  subst candidate

  exact
    LF.Tag.precedesOrEqual_refl _

/--
The canonical singleton invocation boundary discharges every scheduler premise
required by conditional forward payload dispatch.
-/
theorem boundPayloadInvocation_forwardDispatchCompatible
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
    BoundPayloadForwardDispatchCompatible
      (server.invocationPendingMessage
        payload
        delay)
      []
      ((Translation.compilePayloadMessageServer
          server).invocationBoundPayloadState
        initialStateValue
        payload
        delay) := by

  refine
    ⟨(Translation.compilePayloadMessageServer
        server).invocationPendingAction
        payload
        delay,
     [],
     Occurrence.RemovesOne.head [],
     boundPayloadInvocationPending_correspond
       server
       payload
       delay,
     payloadQueueCorresponds_nil,
     boundPayloadInvocationTarget_isEarliest
       server
       payload
       delay,
     ?_⟩

  simpa [
    LF.PayloadReaction.invocationBoundPayloadState,
    LF.PayloadReaction.invocationPendingAction
  ] using
    (initialTag_precedesOrEqual_schedule
      delay)

/--
When ordered payload binding succeeds, the unique source invocation occurrence
can be dispatched.
-/
theorem boundPayloadInvocation_sourceDispatch
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    DTR.BoundPayloadDispatchStep
      server
      (server.invocationBoundPayloadState
        initialStateValue
        payload
        delay)
      (server.invocationPendingMessage
        payload
        delay)
      (server.invocationDispatchedBoundPayloadState
        initialStateValue
        payload
        delay
        boundParameters) := by

  exact
    DTR.BoundPayloadDispatchStep.fire
      (server :=
        server)
      (currentTime :=
        0)
      (stateValue :=
        initialStateValue)
      (parameters :=
        ParameterStore.empty)
      (pendingMessages := [
        server.invocationPendingMessage
          payload
          delay
      ])
      (remainingMessages :=
        [])
      (selectedMessage :=
        server.invocationPendingMessage
          payload
          delay)
      (boundParameters :=
        boundParameters)
      (Occurrence.RemovesOne.head [])
      (boundPayloadInvocationSource_isEarliest
        server
        payload
        delay)
      (Nat.zero_le _)
      (by
        rfl)
      (by
        simpa [
          DTR.PayloadMessageServer.invocationPendingMessage
        ] using
          hBind)

/--
When the same ordered binding succeeds, the unique generated-LF invocation
action can be dispatched.
-/
theorem boundPayloadInvocation_targetDispatch
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    LF.BoundPayloadDispatchStep
      (Translation.compilePayloadMessageServer
        server)
      ((Translation.compilePayloadMessageServer
          server).invocationBoundPayloadState
        initialStateValue
        payload
        delay)
      ((Translation.compilePayloadMessageServer
          server).invocationPendingAction
        payload
        delay)
      ((Translation.compilePayloadMessageServer
          server).invocationDispatchedBoundPayloadState
        initialStateValue
        payload
        delay
        boundParameters) := by

  exact
    LF.BoundPayloadDispatchStep.fire
      (reaction :=
        Translation.compilePayloadMessageServer
          server)
      (currentTag :=
        LF.initialTag)
      (stateValue :=
        initialStateValue)
      (parameters :=
        ParameterStore.empty)
      (pendingActions := [
        (Translation.compilePayloadMessageServer
          server).invocationPendingAction
            payload
            delay
      ])
      (remainingActions :=
        [])
      (selectedAction :=
        (Translation.compilePayloadMessageServer
          server).invocationPendingAction
            payload
            delay)
      (boundParameters :=
        boundParameters)
      (Occurrence.RemovesOne.head [])
      (boundPayloadInvocationTarget_isEarliest
        server
        payload
        delay)
      (by
        simpa [
          LF.PayloadReaction.invocationPendingAction
        ] using
          (initialTag_precedesOrEqual_schedule
            delay))
      (by
        rfl)
      (by
        simpa [
          Translation.compilePayloadMessageServer,
          LF.PayloadReaction.invocationPendingAction
        ] using
          hBind)

/--
After the corresponding singleton dispatches, both activated runtime states
retain equal logical time, persistent state, bound parameters, empty residual
queues, and translated bodies.
-/
theorem boundPayloadInvocationDispatchedStates_correspond
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore) :
    BoundPayloadStateCorresponds
      (server.invocationDispatchedBoundPayloadState
        initialStateValue
        payload
        delay
        boundParameters)
      ((Translation.compilePayloadMessageServer
          server).invocationDispatchedBoundPayloadState
        initialStateValue
        payload
        delay
        boundParameters) := by

  exact {
    currentTime :=
      (boundPayloadInvocationPending_correspond
        server
        payload
        delay).occurrence.logicalTime

    stateValue :=
      rfl

    parameters :=
      rfl

    pendingEvents :=
      payloadQueueCorresponds_nil

    activeBody :=
      rfl
  }

/--
The direct invocation-entry package provides correspondence, forward scheduler
compatibility, both exact dispatches, and correspondence after activation.
-/
theorem boundPayloadInvocationEntry_package
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
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
      DTR.BoundPayloadDispatchStep
        server
        (server.invocationBoundPayloadState
          initialStateValue
          payload
          delay)
        (server.invocationPendingMessage
          payload
          delay)
        (server.invocationDispatchedBoundPayloadState
          initialStateValue
          payload
          delay
          boundParameters) ∧
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        ((Translation.compilePayloadMessageServer
            server).invocationBoundPayloadState
          initialStateValue
          payload
          delay)
        ((Translation.compilePayloadMessageServer
            server).invocationPendingAction
          payload
          delay)
        ((Translation.compilePayloadMessageServer
            server).invocationDispatchedBoundPayloadState
          initialStateValue
          payload
          delay
          boundParameters) ∧
      BoundPayloadStateCorresponds
        (server.invocationDispatchedBoundPayloadState
          initialStateValue
          payload
          delay
          boundParameters)
        ((Translation.compilePayloadMessageServer
            server).invocationDispatchedBoundPayloadState
          initialStateValue
          payload
          delay
          boundParameters) := by

  exact
    ⟨detailedBoundPayloadInvocationStates_correspond
       server
       initialStateValue
       payload
       delay,
     boundPayloadInvocation_forwardDispatchCompatible
       server
       initialStateValue
       payload
       delay,
     boundPayloadInvocation_sourceDispatch
       server
       initialStateValue
       payload
       delay
       boundParameters
       hBind,
     boundPayloadInvocation_targetDispatch
       server
       initialStateValue
       payload
       delay
       boundParameters
       hBind,
     boundPayloadInvocationDispatchedStates_correspond
       server
       initialStateValue
       payload
       delay
       boundParameters⟩

end Correctness
end Relico
