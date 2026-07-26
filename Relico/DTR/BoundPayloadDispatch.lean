import Relico.DTR.BoundPayloadState
import Relico.DTR.Scheduling

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Dispatch semantics for one parameter-aware payload message server.

Dispatch is enabled only when the active body is empty. The selected
pending occurrence is removed, its ordered payload is bound to the
server's ordered formal-parameter list, and the resulting activation
environment replaces the previous parameter store.
-/
inductive BoundPayloadDispatchStep
    (server : DTR.PayloadMessageServer) :
    DTR.BoundPayloadState →
    DTR.PendingMessage →
    DTR.BoundPayloadState →
    Prop where

  | fire
      (currentTime : LogicalTime)
      (stateValue : Int)
      (parameters : ParameterStore)
      (pendingMessages remainingMessages : DTR.MessageBag)
      (selectedMessage : DTR.PendingMessage)
      (boundParameters : ParameterStore)
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
          server.name)
      (hBind :
        ParameterStore.bindPayload
            server.parameters
            selectedMessage.payload =
          some boundParameters) :

      BoundPayloadDispatchStep
        server
        {
          currentTime :=
            currentTime

          stateValue :=
            stateValue

          parameters :=
            parameters

          pendingMessages :=
            pendingMessages

          activeBody :=
            []
        }
        selectedMessage
        {
          currentTime :=
            selectedMessage.arrivalTime

          stateValue :=
            stateValue

          parameters :=
            boundParameters

          pendingMessages :=
            remainingMessages

          activeBody :=
            server.body
        }

namespace BoundPayloadDispatchStep

theorem selected_mem
    {server : DTR.PayloadMessageServer}
    {before after : DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    (hDispatch :
      DTR.BoundPayloadDispatchStep
        server
        before
        selectedMessage
        after) :
    selectedMessage ∈
      before.pendingMessages := by

  cases hDispatch with
  | fire _ _ _ _ _ _ _ hRemoved =>
      exact
        Occurrence.RemovesOne.selected_mem
          hRemoved

theorem preserves_stateValue
    {server : DTR.PayloadMessageServer}
    {before after : DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    (hDispatch :
      DTR.BoundPayloadDispatchStep
        server
        before
        selectedMessage
        after) :
    after.stateValue =
      before.stateValue := by

  cases hDispatch
  rfl

theorem activates_server_body
    {server : DTR.PayloadMessageServer}
    {before after : DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    (hDispatch :
      DTR.BoundPayloadDispatchStep
        server
        before
        selectedMessage
        after) :
    after.activeBody =
      server.body := by

  cases hDispatch
  rfl

end BoundPayloadDispatchStep
end DTR
end Relico
