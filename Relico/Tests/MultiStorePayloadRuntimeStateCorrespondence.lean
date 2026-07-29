import Relico.Correctness.MultiStorePayloadRuntimeStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadRuntimeStateCorrespondence

theorem store_relation_contains_structural
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hStates :
      Correctness.MultiStorePayloadStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.MultiStorePayloadStateCorresponds
      sourceState
      targetState :=

  hStates.toStateCorresponds

theorem store_relation_contains_selection
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hStates :
      Correctness.MultiStorePayloadStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.MultiStorePayloadSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions :=

  hStates.selectionCompatible

theorem runtime_contains_store_relation
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.MultiStorePayloadStoreStateCorresponds
      messageServers
      sourceState
      targetState :=

  hRuntime.toStoreStateCorresponds

theorem runtime_contains_structural
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.MultiStorePayloadStateCorresponds
      sourceState
      targetState :=

  hRuntime.toStateCorresponds

theorem runtime_contains_selection
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.MultiStorePayloadSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions :=

  hRuntime.selectionCompatible

theorem runtime_contains_exact_payload_queues
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.PayloadQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions :=

  hRuntime.payloadQueues

theorem runtime_pending_action_not_past
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState}
    {action :
      LF.PendingAction}
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState)
    (hAction :
      action ∈
        targetState.pendingActions) :
    targetState.currentTag.PrecedesOrEqual
      action.tag :=

  hRuntime.pendingActionNotPast
    hAction

theorem empty_target_queue_pending_not_past
    {targetState :
      LF.MultiStorePayloadState}
    (hEmpty :
      targetState.pendingActions =
        []) :
    targetState.PendingNotPast :=

  LF.MultiStorePayloadState.pendingNotPast_of_pendingActions_nil
    hEmpty

end MultiStorePayloadRuntimeStateCorrespondence
end Tests
end Relico
