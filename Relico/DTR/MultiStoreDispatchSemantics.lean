import Relico.DTR.MultiStoreSyntax
import Relico.DTR.Scheduling
import Relico.DTR.StoreState

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Dispatch semantics for finite-store DTR models with multiple message
servers.

The transition carries the exact declared message server selected for
the pending occurrence. Its declaration membership and name match are
explicit premises.
-/
inductive MultiStoreDispatchStep
    (messageServers : List DTR.MessageServer) :
    DTR.StoreState →
    DTR.PendingMessage →
    DTR.MessageServer →
    DTR.StoreState →
    Prop where

  | fire
      (currentTime : LogicalTime)
      (stateStore : StateStore)
      (pendingMessages remainingMessages : DTR.MessageBag)
      (selectedMessage : DTR.PendingMessage)
      (selectedServer : DTR.MessageServer)
      (hServerDeclared :
        selectedServer ∈
          messageServers)
      (hRemoved :
        Occurrence.RemovesOne
          selectedMessage
          pendingMessages
          remainingMessages)
      (hEarliest :
        DTR.IsEarliest
          selectedMessage
          pendingMessages)
      (hNotPast :
        currentTime ≤
          selectedMessage.arrivalTime)
      (hTarget :
        selectedMessage.name =
          selectedServer.name) :

      MultiStoreDispatchStep
        messageServers
        {
          currentTime :=
            currentTime

          stateStore :=
            stateStore

          pendingMessages :=
            pendingMessages

          activeBody :=
            []
        }
        selectedMessage
        selectedServer
        {
          currentTime :=
            selectedMessage.arrivalTime

          stateStore :=
            stateStore

          pendingMessages :=
            remainingMessages

          activeBody :=
            selectedServer.body
        }

namespace MultiStoreDispatchStep

/--
Multi-server dispatch preserves finite-store declaration coverage.
-/
theorem preserves_coverage
    {messageServers : List DTR.MessageServer}
    {declaredVariables : List VarName}
    {before after : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    (hDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after)
    (hCoverage :
      DTR.StoreState.Covers
        declaredVariables
        before) :
    DTR.StoreState.Covers
      declaredVariables
      after := by

  cases hDispatch
  exact hCoverage

/--
The server selected by a dispatch transition belongs to the declared
message-server list.
-/
theorem selectedServer_mem
    {messageServers : List DTR.MessageServer}
    {before after : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    (hDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after) :
    selectedServer ∈
      messageServers := by

  cases hDispatch with
  | fire _ _ _ _ _ _ hServerDeclared =>
      exact hServerDeclared

end MultiStoreDispatchStep
end DTR
end Relico
