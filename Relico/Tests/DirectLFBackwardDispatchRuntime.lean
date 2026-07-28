import Relico.Correctness.DirectLFBackwardDispatchRuntime

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFBackwardDispatchRuntime

/--
Every ordinary generated-LF dispatch reconstructs an ordinary DTR dispatch
of the corresponding declared source message server.
-/
theorem ordinary_backward_dispatch
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState targetStateAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    (hTargetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetState
        selectedAction
        selectedReaction
        targetStateAfter)
    (hRuntime :
      Correctness.DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    ∃ selectedMessage selectedServer sourceStateAfter,
      selectedReaction =
          Translation.compileMessageReaction
            selectedServer ∧
        DTR.MultiStoreDispatchStep
          messageServers
          sourceState
          selectedMessage
          selectedServer
          sourceStateAfter ∧
        Correctness.PendingCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.DirectLFRuntimeStateCorresponds
          messageServers
          sourceStateAfter
          targetStateAfter :=
  Correctness.directLF_multiStore_dispatch_backward_runtime
    hTargetDispatch
    hRuntime

/--
The ordinary body compiler reflects emptiness.
-/
theorem compile_body_empty_iff
    (sourceBody : DTR.Body) :
    Translation.compileBody sourceBody = [] ↔
      sourceBody = [] :=
  Correctness.directLF_compileBody_eq_nil_iff
    sourceBody

#check
  Correctness.directLF_compileBody_eq_nil_iff

#check
  Correctness.directLF_multiStore_dispatch_backward_runtime

#check ordinary_backward_dispatch
#check compile_body_empty_iff

end DirectLFBackwardDispatchRuntime
end Tests
end Relico
