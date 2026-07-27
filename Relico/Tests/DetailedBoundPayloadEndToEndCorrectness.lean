import Relico.Correctness.DetailedBoundPayloadEndToEndCorrectness

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadEndToEndCorrectness

#check Correctness.detailedBoundPayloadInitialSourceRuntimeInvariant
#check Correctness.detailedBoundPayloadInitialTargetRuntimeInvariant
#check Correctness.detailedBoundPayloadInitialStates_runtimeBoundary

#check Correctness.detailedBoundPayloadInvocationSourceRuntimeInvariant
#check Correctness.detailedBoundPayloadInvocationTargetRuntimeInvariant_of_positive
#check Correctness.detailedBoundPayloadInvocationTargetRuntimeInvariant_zero_impossible
#check Correctness.detailedBoundPayloadInvocationStates_runtimeBoundary_of_positive

#check Correctness.detailedBoundPayloadInitialSteps_forward
#check Correctness.detailedBoundPayloadInvocationSteps_forward_of_positive

#check Correctness.DetailedBoundPayloadInvocationPrefixLabels
#check Correctness.boundPayloadInvocation_sourceFuture_of_positive
#check Correctness.boundPayloadInvocation_sourceSameTime_zero
#check Correctness.boundPayloadInvocation_targetSameTime_zero
#check Correctness.boundPayloadInvocation_targetMicrostepLater_zero
#check Correctness.detailedBoundPayloadInvocationTailSteps_forward

theorem initial_runtime_boundary_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int) :
    Correctness.DetailedBoundPayloadStateCorresponds
        server
        (server.initialDetailedBoundPayloadState
          initialStateValue)
        ((Translation.compilePayloadMessageServer
            server).initialDetailedBoundPayloadState
          initialStateValue) ∧

      Correctness.DetailedBoundPayloadSourceRuntimeInvariant
        server
        (server.initialDetailedBoundPayloadState
          initialStateValue) ∧

      Correctness.DetailedBoundPayloadTargetRuntimeInvariant
        server
        ((Translation.compilePayloadMessageServer
            server).initialDetailedBoundPayloadState
          initialStateValue) ∧

      Correctness.DetailedBoundPayloadForwardCanonicalPhase
        (server.initialDetailedBoundPayloadState
          initialStateValue)
        ((Translation.compilePayloadMessageServer
            server).initialDetailedBoundPayloadState
          initialStateValue) := by

  exact
    Correctness.detailedBoundPayloadInitialStates_runtimeBoundary
      server
      initialStateValue

theorem positive_invocation_runtime_boundary_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload)
    (delay : Delay)
    (hPositive :
      0 < delay.value) :
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

      Correctness.DetailedBoundPayloadSourceRuntimeInvariant
        server
        (server.invocationDetailedBoundPayloadState
          initialStateValue
          payload
          delay) ∧

      Correctness.DetailedBoundPayloadTargetRuntimeInvariant
        server
        ((Translation.compilePayloadMessageServer
            server).invocationDetailedBoundPayloadState
          initialStateValue
          payload
          delay) ∧

      Correctness.DetailedBoundPayloadForwardCanonicalPhase
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
    Correctness.detailedBoundPayloadInvocationStates_runtimeBoundary_of_positive
      server
      initialStateValue
      payload
      delay
      hPositive

theorem zero_invocation_ready_target_invariant_impossible_interface
    (server : DTR.PayloadMessageServer)
    (initialStateValue : Int)
    (payload : Payload) :
    ¬ Correctness.DetailedBoundPayloadTargetRuntimeInvariant
        server
        ((Translation.compilePayloadMessageServer
            server).invocationDetailedBoundPayloadState
          initialStateValue
          payload
          ⟨0⟩) := by

  exact
    Correctness.detailedBoundPayloadInvocationTargetRuntimeInvariant_zero_impossible
      server
      initialStateValue
      payload

theorem initial_finite_execution_interface
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

        Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧

        Correctness.DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧

        Correctness.DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            sourceLabels)
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) ∧

        Correctness.DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        Correctness.DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        Correctness.DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter := by

  exact
    Correctness.detailedBoundPayloadInitialSteps_forward
      hSourceSteps
      hServerTiming

theorem positive_invocation_finite_execution_interface
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

        Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧

        Correctness.DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧

        Correctness.DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            sourceLabels)
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) ∧

        Correctness.DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        Correctness.DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        Correctness.DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter := by

  exact
    Correctness.detailedBoundPayloadInvocationSteps_forward_of_positive
      hSourceSteps
      hPositive
      hServerTiming

theorem arbitrary_invocation_tail_execution_interface
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
          (Correctness.DetailedBoundPayloadInvocationPrefixLabels
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

        Correctness.DetailedBoundPayloadWeakLabelTraceCorresponds
          (Correctness.DetailedBoundPayloadInvocationPrefixLabels
              server
              initialStateValue
              payload
              delay
              boundParameters ++
            sourceTailLabels)
          targetLabels ∧

        Correctness.DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧

        Correctness.DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            (Correctness.DetailedBoundPayloadInvocationPrefixLabels
                server
                initialStateValue
                payload
                delay
                boundParameters ++
              sourceTailLabels))
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) ∧

        Correctness.DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        Correctness.DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        Correctness.DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter := by

  exact
    Correctness.detailedBoundPayloadInvocationTailSteps_forward
      hBind
      hSourceTail
      hServerTiming

end DetailedBoundPayloadEndToEndCorrectness
end Tests
end Relico
