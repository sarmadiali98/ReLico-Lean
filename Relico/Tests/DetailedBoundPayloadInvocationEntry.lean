import Relico.Correctness.DetailedBoundPayloadInvocationEntry

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadInvocationEntry

#check DTR.PayloadMessageServer.invocationPendingMessage
#check DTR.PayloadMessageServer.invocationBoundPayloadState
#check DTR.PayloadMessageServer.invocationDetailedBoundPayloadState
#check DTR.PayloadMessageServer.invocationDispatchedBoundPayloadState

#check LF.PayloadReaction.invocationPendingAction
#check LF.PayloadReaction.invocationBoundPayloadState
#check LF.PayloadReaction.invocationDetailedBoundPayloadState
#check LF.PayloadReaction.invocationDispatchedBoundPayloadState

#check Correctness.boundPayloadInvocationPending_correspond
#check Correctness.boundPayloadInvocationQueues_correspond
#check Correctness.boundPayloadInvocationStates_correspond
#check Correctness.detailedBoundPayloadInvocationStates_correspond

#check Correctness.initialTag_precedesOrEqual_schedule
#check Correctness.boundPayloadInvocationSource_isEarliest
#check Correctness.boundPayloadInvocationTarget_isEarliest

#check Correctness.boundPayloadInvocation_forwardDispatchCompatible
#check Correctness.boundPayloadInvocation_sourceDispatch
#check Correctness.boundPayloadInvocation_targetDispatch
#check Correctness.boundPayloadInvocationDispatchedStates_correspond
#check Correctness.boundPayloadInvocationEntry_package

theorem pending_occurrence_correspondence_interface
    (server : DTR.PayloadMessageServer)
    (payload : Payload)
    (delay : Delay) :
    Correctness.PendingPayloadCorresponds
      (server.invocationPendingMessage
        payload
        delay)
      ((Translation.compilePayloadMessageServer
          server).invocationPendingAction
        payload
        delay) := by

  exact
    Correctness.boundPayloadInvocationPending_correspond
      server
      payload
      delay

theorem invocation_state_correspondence_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
    Correctness.DetailedBoundPayloadStateCorresponds
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
    Correctness.detailedBoundPayloadInvocationStates_correspond
      server
      initialStateValue
      payload
      delay

theorem invocation_scheduler_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay) :
    Correctness.BoundPayloadForwardDispatchCompatible
      (server.invocationPendingMessage
        payload
        delay)
      []
      ((Translation.compilePayloadMessageServer
          server).invocationBoundPayloadState
        initialStateValue
        payload
        delay) := by

  exact
    Correctness.boundPayloadInvocation_forwardDispatchCompatible
      server
      initialStateValue
      payload
      delay

theorem source_dispatch_interface
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
    Correctness.boundPayloadInvocation_sourceDispatch
      server
      initialStateValue
      payload
      delay
      boundParameters
      hBind

theorem target_dispatch_interface
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
    Correctness.boundPayloadInvocation_targetDispatch
      server
      initialStateValue
      payload
      delay
      boundParameters
      hBind

theorem dispatched_state_correspondence_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (boundParameters : ParameterStore) :
    Correctness.BoundPayloadStateCorresponds
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
    Correctness.boundPayloadInvocationDispatchedStates_correspond
      server
      initialStateValue
      payload
      delay
      boundParameters

theorem invocation_entry_package_interface
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
    Correctness.DetailedBoundPayloadStateCorresponds
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
      Correctness.BoundPayloadForwardDispatchCompatible
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
      Correctness.BoundPayloadStateCorresponds
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
    Correctness.boundPayloadInvocationEntry_package
      server
      initialStateValue
      payload
      delay
      boundParameters
      hBind

end DetailedBoundPayloadInvocationEntry
end Tests
end Relico
