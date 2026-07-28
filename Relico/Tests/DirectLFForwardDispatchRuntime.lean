import Relico.Correctness.DirectLFForwardDispatchRuntime

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFForwardDispatchRuntime

/--
Every ordinary DTR multiple-message-server dispatch is matched by an ordinary
generated-LF dispatch of the corresponding compiled reaction.
-/
theorem ordinary_forward_dispatch
    {messageServers :
      List DTR.MessageServer}
    {sourceState sourceStateAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    {targetState :
      LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceState
        selectedMessage
        selectedServer
        sourceStateAfter)
    (hRuntime :
      Correctness.DirectLFRuntimeStateCorresponds
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
        Correctness.PendingCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.DirectLFRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter :=
  Correctness.directLF_multiStore_dispatch_forward_runtime
    hSourceDispatch
    hRuntime

#check
  Correctness.directLF_multiStore_dispatch_forward_runtime

#check ordinary_forward_dispatch

end DirectLFForwardDispatchRuntime
end Tests
end Relico
