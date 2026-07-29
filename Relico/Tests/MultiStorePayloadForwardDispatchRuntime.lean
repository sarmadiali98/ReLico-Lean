import Relico.Correctness.MultiStorePayloadForwardDispatchRuntime

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadForwardDispatchRuntime

theorem ordinary_forward_dispatch
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState sourceStateAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetState :
      LF.MultiStorePayloadState}
    (hSourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceState
        selectedMessage
        selectedServer
        sourceStateAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedAction targetStateAfter,
      LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetState
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetStateAfter ∧
        Correctness.PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.MultiStorePayloadRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter :=

  Correctness.multiStorePayload_dispatch_forward_runtime
    hSourceDispatch
    hRuntime

theorem forward_dispatch_preserves_exact_payload
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState sourceStateAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetState :
      LF.MultiStorePayloadState}
    (hSourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceState
        selectedMessage
        selectedServer
        sourceStateAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedAction targetStateAfter,
      LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetState
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetStateAfter ∧
        selectedAction.payload =
          selectedMessage.payload := by

  obtain
    ⟨selectedAction,
     targetStateAfter,
     hTargetDispatch,
     hSelected,
     _hAfter⟩ :=
      Correctness.multiStorePayload_dispatch_forward_runtime
        hSourceDispatch
        hRuntime

  exact
    ⟨selectedAction,
     targetStateAfter,
     hTargetDispatch,
     hSelected.payload⟩

theorem forward_dispatch_preserves_runtime_queue_correspondence
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState sourceStateAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetState :
      LF.MultiStorePayloadState}
    (hSourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceState
        selectedMessage
        selectedServer
        sourceStateAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedAction targetStateAfter,
      LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetState
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetStateAfter ∧
        Correctness.PayloadQueueCorresponds
          sourceStateAfter.pendingMessages
          targetStateAfter.pendingActions := by

  obtain
    ⟨selectedAction,
     targetStateAfter,
     hTargetDispatch,
     _hSelected,
     hAfter⟩ :=
      Correctness.multiStorePayload_dispatch_forward_runtime
        hSourceDispatch
        hRuntime

  exact
    ⟨selectedAction,
     targetStateAfter,
     hTargetDispatch,
     hAfter.payloadQueues⟩

theorem forward_dispatch_preserves_scheduler_boundary
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState sourceStateAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetState :
      LF.MultiStorePayloadState}
    (hSourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceState
        selectedMessage
        selectedServer
        sourceStateAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedAction targetStateAfter,
      LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetState
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetStateAfter ∧
        Correctness.MultiStorePayloadSelectionCompatible
          messageServers
          sourceStateAfter.pendingMessages
          targetStateAfter.pendingActions ∧
        targetStateAfter.PendingNotPast := by

  obtain
    ⟨selectedAction,
     targetStateAfter,
     hTargetDispatch,
     _hSelected,
     hAfter⟩ :=
      Correctness.multiStorePayload_dispatch_forward_runtime
        hSourceDispatch
        hRuntime

  exact
    ⟨selectedAction,
     targetStateAfter,
     hTargetDispatch,
     hAfter.selectionCompatible,
     hAfter.pendingNotPast⟩

end MultiStorePayloadForwardDispatchRuntime
end Tests
end Relico
