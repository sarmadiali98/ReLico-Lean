import Relico.Correctness.DirectLFPayloadBackwardDispatchRuntime

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFPayloadRuntimeDispatch

#check Correctness.DirectLFPayloadStoreStateCorresponds
#check Correctness.DirectLFPayloadStoreStateCorresponds.toStoreStateCorresponds
#check Correctness.DirectLFPayloadStoreStateCorresponds.payloadSelectionCompatible
#check Correctness.DirectLFPayloadStoreStateCorresponds.toPayloadBagQueueCorresponds

#check Correctness.DirectLFPayloadRuntimeStateCorresponds
#check Correctness.DirectLFPayloadRuntimeStateCorresponds.toRuntimeStateCorresponds
#check Correctness.DirectLFPayloadRuntimeStateCorresponds.selectionCompatible
#check Correctness.DirectLFPayloadRuntimeStateCorresponds.toStoreStateCorresponds

#check Correctness.directLF_targetTag_eq_of_sameSource
#check Correctness.directLF_reactionPriorityEligible_of_sameSource
#check Correctness.directLFPayload_sourceDispatchSelection
#check Correctness.directLFPayload_targetDispatchSelection

#check Correctness.directLFPayload_multiStore_dispatch_forward_runtime
#check Correctness.directLFPayload_compileBody_eq_nil_iff
#check Correctness.directLFPayload_multiStore_dispatch_backward_runtime

example
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState : LF.StoreState}
    (hRuntime :
      Correctness.DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.DirectLFRuntimeStateCorresponds
      messageServers
      sourceState
      targetState := by

  exact
    hRuntime.toRuntimeStateCorresponds

example
    {messageServers : List DTR.MessageServer}
    {sourceState sourceStateAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {targetState : LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceState
        selectedMessage
        selectedServer
        sourceStateAfter)
    (hRuntime :
      Correctness.DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedAction targetStateAfter,
      LF.MultiStoreDispatchStep
          (Translation.compileMessageReactions
            messageServers)
          targetState
          selectedAction
          (Translation.compileMessageReaction
            selectedServer)
          targetStateAfter ∧
        Correctness.PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.DirectLFPayloadRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter := by

  exact
    Correctness.directLFPayload_multiStore_dispatch_forward_runtime
      hSourceDispatch
      hRuntime

end DirectLFPayloadRuntimeDispatch
end Tests
end Relico
