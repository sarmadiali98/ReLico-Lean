import Relico.Correctness.DirectLFRuntimeStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFRuntimeStateCorrespondence

theorem runtime_contains_structural_correspondence
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState :
      LF.StoreState}
    (hRuntime :
      Correctness.DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.DirectLFStoreStateCorresponds
      messageServers
      sourceState
      targetState :=
  hRuntime.states

theorem runtime_contains_pending_not_past
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState :
      LF.StoreState}
    (hRuntime :
      Correctness.DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    LF.StoreState.PendingNotPast
      targetState :=
  hRuntime.pendingNotPast

#check
  Correctness.DirectLFRuntimeStateCorresponds

#check
  Correctness.DirectLFRuntimeStateCorresponds.toBagQueueCorresponds

#check
  Correctness.DirectLFRuntimeStateCorresponds.selectionCompatible

#check
  Correctness.directLF_multiStore_step_forward_runtime

#check
  Correctness.directLF_multiStore_step_backward_runtime

#check runtime_contains_structural_correspondence
#check runtime_contains_pending_not_past

end DirectLFRuntimeStateCorrespondence
end Tests
end Relico
