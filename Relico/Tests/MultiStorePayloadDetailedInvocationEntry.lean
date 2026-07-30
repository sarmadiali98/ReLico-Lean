import Relico.Correctness.MultiStorePayloadDetailedInvocationEntry

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadDetailedInvocationEntry

open Correctness

example
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (server :
      DTR.MultiStorePayloadMessageServer)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay) :
    MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (DTR.MultiStorePayloadMessageServer.invocationDetailedMultiStorePayloadState
        messageServers
        server
        initialStateStore
        payload
        delay)
      (LF.invocationDetailedLFMultiStorePayloadState
        messageServers
        server
        initialStateStore
        payload
        delay) :=
  detailedMultiStorePayloadInvocationStates_correspond
    messageServers
    server
    initialStateStore
    payload
    delay

example
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    DTR.MultiStorePayloadDispatchStep
      messageServers
      (server.invocationMultiStorePayloadState
        initialStateStore
        payload
        delay)
      (server.invocationPendingMessage
        payload
        delay)
      server
      (server.invocationDispatchedMultiStorePayloadState
        initialStateStore
        payload
        delay
        boundParameters) :=
  multiStorePayloadInvocation_sourceDispatch
    server
    hMember
    initialStateStore
    payload
    delay
    boundParameters
    hBind

example
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    LF.MultiStorePayloadDispatchStep
      (Translation.compileMultiStorePayloadMessageReactions
        messageServers)
      (LF.invocationLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay)
      (LF.invocationMultiStorePayloadPendingAction
        server
        payload
        delay)
      (Translation.compileMultiStorePayloadReaction
        server)
      (LF.invocationDispatchedLFMultiStorePayloadState
        server
        initialStateStore
        payload
        delay
        boundParameters) :=
  multiStorePayloadInvocation_targetDispatch
    server
    hMember
    initialStateStore
    payload
    delay
    boundParameters
    hBind

example
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hPositive :
      0 < delay.value) :
    MultiStorePayloadInvocationPositivePhaseEntry
      server
      hMember
      initialStateStore
      payload
      delay
      boundParameters
      hBind :=
  multiStorePayloadInvocation_positivePhaseEntry
    server
    hMember
    initialStateStore
    payload
    delay
    boundParameters
    hBind
    hPositive

example
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters)
    (hZero :
      delay.value = 0) :
    MultiStorePayloadInvocationZeroPhaseEntry
      server
      hMember
      initialStateStore
      payload
      delay
      boundParameters
      hBind :=
  multiStorePayloadInvocation_zeroPhaseEntry
    server
    hMember
    initialStateStore
    payload
    delay
    boundParameters
    hBind
    hZero

example
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (server :
      DTR.MultiStorePayloadMessageServer)
    (hMember :
      server ∈ messageServers)
    (initialStateStore :
      StateStore)
    (payload :
      Payload)
    (delay :
      Delay)
    (boundParameters :
      ParameterStore)
    (hBind :
      ParameterStore.bindPayload
          server.parameters
          payload =
        some boundParameters) :
    (0 < delay.value ∧
      MultiStorePayloadInvocationPositivePhaseEntry
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) ∨
    (delay.value = 0 ∧
      MultiStorePayloadInvocationZeroPhaseEntry
        server
        hMember
        initialStateStore
        payload
        delay
        boundParameters
        hBind) :=
  multiStorePayloadInvocationDetailedPhaseEntry
    server
    hMember
    initialStateStore
    payload
    delay
    boundParameters
    hBind

end MultiStorePayloadDetailedInvocationEntry
end Tests
end Relico
