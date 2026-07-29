import Relico.Correctness.MultiStorePayloadBackwardDispatchRuntime

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadBackwardDispatchRuntime

theorem ordinary_backward_dispatch
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState targetStateAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetState
        selectedAction
        selectedReaction
        targetStateAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedMessage selectedServer sourceStateAfter,
      selectedReaction =
          Translation.compileMultiStorePayloadReaction
            selectedServer ∧
        DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceState
          selectedMessage
          selectedServer
          sourceStateAfter ∧
        Correctness.PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.MultiStorePayloadRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter :=

  Correctness.multiStorePayload_dispatch_backward_runtime
    hTargetDispatch
    hRuntime

theorem backward_dispatch_recovers_generated_reaction
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState targetStateAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetState
        selectedAction
        selectedReaction
        targetStateAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedServer,
      selectedServer ∈
          messageServers ∧
        selectedReaction =
          Translation.compileMultiStorePayloadReaction
            selectedServer := by

  obtain
    ⟨_selectedMessage,
     selectedServer,
     _sourceStateAfter,
     hReaction,
     hSourceDispatch,
     _hSelected,
     _hAfter⟩ :=
      Correctness.multiStorePayload_dispatch_backward_runtime
        hTargetDispatch
        hRuntime

  cases hSourceDispatch with

  | fire
      _currentTime
      _stateStore
      _parameters
      _pendingMessages
      _remainingMessages
      _selectedMessage
      _selectedServer
      _boundParameters
      hServerDeclared
      _hRemoved
      _hEligible
      _hNotPast
      _hTarget
      _hBind =>

      exact
        ⟨selectedServer,
         hServerDeclared,
         hReaction⟩

theorem backward_dispatch_preserves_exact_payload
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState targetStateAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetState
        selectedAction
        selectedReaction
        targetStateAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedMessage selectedServer sourceStateAfter,
      DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceState
          selectedMessage
          selectedServer
          sourceStateAfter ∧
        selectedAction.payload =
          selectedMessage.payload := by

  obtain
    ⟨selectedMessage,
     selectedServer,
     sourceStateAfter,
     _hReaction,
     hSourceDispatch,
     hSelected,
     _hAfter⟩ :=
      Correctness.multiStorePayload_dispatch_backward_runtime
        hTargetDispatch
        hRuntime

  exact
    ⟨selectedMessage,
     selectedServer,
     sourceStateAfter,
     hSourceDispatch,
     hSelected.payload⟩

theorem backward_dispatch_preserves_runtime_queue_correspondence
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState targetStateAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetState
        selectedAction
        selectedReaction
        targetStateAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedMessage selectedServer sourceStateAfter,
      DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceState
          selectedMessage
          selectedServer
          sourceStateAfter ∧
        Correctness.PayloadQueueCorresponds
          sourceStateAfter.pendingMessages
          targetStateAfter.pendingActions := by

  obtain
    ⟨selectedMessage,
     selectedServer,
     sourceStateAfter,
     _hReaction,
     hSourceDispatch,
     _hSelected,
     hAfter⟩ :=
      Correctness.multiStorePayload_dispatch_backward_runtime
        hTargetDispatch
        hRuntime

  exact
    ⟨selectedMessage,
     selectedServer,
     sourceStateAfter,
     hSourceDispatch,
     hAfter.payloadQueues⟩

theorem backward_dispatch_preserves_scheduler_boundary
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState targetStateAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetState
        selectedAction
        selectedReaction
        targetStateAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedMessage selectedServer sourceStateAfter,
      DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceState
          selectedMessage
          selectedServer
          sourceStateAfter ∧
        Correctness.MultiStorePayloadSelectionCompatible
          messageServers
          sourceStateAfter.pendingMessages
          targetStateAfter.pendingActions ∧
        targetStateAfter.PendingNotPast := by

  obtain
    ⟨selectedMessage,
     selectedServer,
     sourceStateAfter,
     _hReaction,
     hSourceDispatch,
     _hSelected,
     hAfter⟩ :=
      Correctness.multiStorePayload_dispatch_backward_runtime
        hTargetDispatch
        hRuntime

  exact
    ⟨selectedMessage,
     selectedServer,
     sourceStateAfter,
     hSourceDispatch,
     hAfter.selectionCompatible,
     hAfter.pendingNotPast⟩

theorem compiled_body_empty_iff_source_body_empty
    (body :
      DTR.MultiStorePayloadBody) :
    Translation.compileMultiStorePayloadBody body =
        [] ↔
      body =
        [] :=

  Correctness.multiStorePayload_compileBody_eq_nil_iff
    body

end MultiStorePayloadBackwardDispatchRuntime
end Tests
end Relico
