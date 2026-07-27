import Relico.Correctness.DetailedBoundPayloadRuntimeInvariant

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadRuntimeInvariant

#check DTR.BoundPayloadStmt.PriorityTimingWellFormed
#check DTR.BoundPayloadBody.PriorityTimingWellFormed

#check DTR.BoundPayloadStmt.priorityTimingWellFormed_selfSendInt
#check DTR.BoundPayloadBody.priorityTimingWellFormed_nil
#check DTR.BoundPayloadBody.priorityTimingWellFormed_cons
#check DTR.BoundPayloadBody.priorityTimingWellFormed_head
#check DTR.BoundPayloadBody.priorityTimingWellFormed_tail

#check LF.BoundPayloadState.PendingMicrostepsZero
#check LF.BoundPayloadState.PendingStrictlyFuture
#check LF.BoundPayloadState.RuntimeInvariant

#check Correctness.boundPayloadSchedule_positive_microstepZero
#check Correctness.boundPayloadSchedule_zero_microstepPositive
#check Correctness.boundPayloadInvocationDispatched_targetRuntimeInvariant
#check Correctness.boundPayloadForwardDispatchCompatible_of_runtimeInvariant
#check Correctness.boundPayloadInvocation_runtimeBoundary_package

theorem positive_internal_send_interface
    (targetMessage : MsgName)
    (payloadExpression : DTR.PayloadExpr)
    (delay : Delay)
    (hTiming :
      DTR.BoundPayloadStmt.PriorityTimingWellFormed
        (.selfSendInt
          targetMessage
          payloadExpression
          delay)) :
    0 < delay.value := by

  exact
    (DTR.BoundPayloadStmt.priorityTimingWellFormed_selfSendInt
      targetMessage
      payloadExpression
      delay).mp
      hTiming

theorem positive_body_head_interface
    {statement : DTR.BoundPayloadStmt}
    {remaining : DTR.BoundPayloadBody}
    (hTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        (statement :: remaining)) :
    DTR.BoundPayloadStmt.PriorityTimingWellFormed
      statement := by

  exact
    DTR.BoundPayloadBody.priorityTimingWellFormed_head
      hTiming

theorem zero_delay_internal_send_creates_microstep_interface
    (tag : LF.Tag) :
    0 <
      (LF.Tag.schedule
        tag
        ⟨0⟩).microstep := by

  exact
    Correctness.boundPayloadSchedule_zero_microstepPositive
      tag

theorem invocation_destination_invariant_interface
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

  exact
    Correctness.boundPayloadInvocationDispatched_targetRuntimeInvariant
      server
      initialStateValue
      payload
      delay
      boundParameters

theorem automatic_dispatch_compatibility_interface
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
      Correctness.BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hTargetInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetBefore) :
    Correctness.BoundPayloadForwardDispatchCompatible
      selectedMessage
      sourceAfter.pendingMessages
      targetBefore := by

  exact
    Correctness.boundPayloadForwardDispatchCompatible_of_runtimeInvariant
      hSourceDispatch
      hStates
      hTargetInvariant

theorem invocation_runtime_boundary_interface
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
      LF.BoundPayloadState.RuntimeInvariant
        ((Translation.compilePayloadMessageServer
            server).invocationDispatchedBoundPayloadState
          initialStateValue
          payload
          delay
          boundParameters) := by

  exact
    Correctness.boundPayloadInvocation_runtimeBoundary_package
      server
      initialStateValue
      payload
      delay
      boundParameters
      hBind

end DetailedBoundPayloadRuntimeInvariant
end Tests
end Relico
