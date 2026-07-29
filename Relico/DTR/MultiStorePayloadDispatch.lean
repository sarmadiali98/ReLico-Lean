import Relico.Common.Occurrence
import Relico.DTR.MultiStorePayloadPriority
import Relico.DTR.MultiStorePayloadSemantics
import Relico.DTR.Scheduling

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Scan an ordered payload-message-server list for the first occurrence
of either requested server name.
-/
private def multiStorePayloadServerNamePrecedesOrEqualBool
    (left right :
      MsgName) :
    List DTR.MultiStorePayloadMessageServer →
    Bool

  | [] =>
      false

  | current :: remaining =>
      if current.name = left then
        true
      else if current.name = right then
        false
      else
        multiStorePayloadServerNamePrecedesOrEqualBool
          left
          right
          remaining

/--
Name order in a concrete payload-message-server declaration list.
-/
def MultiStorePayloadServerNamePrecedesOrEqual
    (left right :
      MsgName)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    Prop :=
  multiStorePayloadServerNamePrecedesOrEqualBool
      left
      right
      messageServers =
    true

instance
    (left right :
      MsgName)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    Decidable
      (MultiStorePayloadServerNamePrecedesOrEqual
        left
        right
        messageServers) := by

  unfold MultiStorePayloadServerNamePrecedesOrEqual
  infer_instance

/--
Name order after stable local-priority normalization.

Smaller explicit priorities precede larger priorities. Explicit
priorities precede `none`.
-/
def MultiStorePayloadPriorityServerNamePrecedesOrEqual
    (left right :
      MsgName)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    Prop :=
  MultiStorePayloadServerNamePrecedesOrEqual
    left
    right
    (DTR.MultiStorePayloadMessageServerPriority.normalize
      messageServers)

instance
    (left right :
      MsgName)
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    Decidable
      (MultiStorePayloadPriorityServerNamePrecedesOrEqual
        left
        right
        messageServers) := by

  unfold MultiStorePayloadPriorityServerNamePrecedesOrEqual
  infer_instance

/--
Priority-aware source eligibility for one payload-bearing pending
message occurrence.

Metric arrival time is selected first. Local message-server priority
then resolves occurrences at that same metric time.
-/
def MultiStorePayloadIsPriorityEligible
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (selected :
      DTR.PendingMessage)
    (pendingMessages :
      DTR.MessageBag) :
    Prop :=
  DTR.IsEarliest
      selected
      pendingMessages ∧
    ∀ candidate,
      candidate ∈
          pendingMessages →
      candidate.arrivalTime =
          selected.arrivalTime →
      DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
        selected.name
        candidate.name
        messageServers

namespace MultiStorePayloadIsPriorityEligible

theorem isEarliest
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {selected :
      DTR.PendingMessage}
    {pendingMessages :
      DTR.MessageBag}
    (hEligible :
      DTR.MultiStorePayloadIsPriorityEligible
        messageServers
        selected
        pendingMessages) :
    DTR.IsEarliest
      selected
      pendingMessages :=
  hEligible.1

theorem precedes_same_time
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {selected candidate :
      DTR.PendingMessage}
    {pendingMessages :
      DTR.MessageBag}
    (hEligible :
      DTR.MultiStorePayloadIsPriorityEligible
        messageServers
        selected
        pendingMessages)
    (hCandidate :
      candidate ∈
        pendingMessages)
    (hSameTime :
      candidate.arrivalTime =
        selected.arrivalTime) :
    DTR.MultiStorePayloadPriorityServerNamePrecedesOrEqual
      selected.name
      candidate.name
      messageServers :=
  hEligible.2
    candidate
    hCandidate
    hSameTime

end MultiStorePayloadIsPriorityEligible

/--
Payload-aware multi-server source dispatch.

Dispatch requires an idle actor. Exactly one selected occurrence is
removed, its ordered payload is bound to the selected server's ordered
formal parameters, and the selected server body becomes active.
-/
inductive MultiStorePayloadDispatchStep
    (messageServers :
      List DTR.MultiStorePayloadMessageServer) :
    DTR.MultiStorePayloadState →
    DTR.PendingMessage →
    DTR.MultiStorePayloadMessageServer →
    DTR.MultiStorePayloadState →
    Prop where

  | fire
      (currentTime :
        LogicalTime)
      (stateStore :
        StateStore)
      (parameters :
        ParameterStore)
      (pendingMessages remainingMessages :
        DTR.MessageBag)
      (selectedMessage :
        DTR.PendingMessage)
      (selectedServer :
        DTR.MultiStorePayloadMessageServer)
      (boundParameters :
        ParameterStore)
      (hServerDeclared :
        selectedServer ∈
          messageServers)
      (hRemoved :
        Occurrence.RemovesOne
          selectedMessage
          pendingMessages
          remainingMessages)
      (hPriorityEligible :
        DTR.MultiStorePayloadIsPriorityEligible
          messageServers
          selectedMessage
          pendingMessages)
      (hNotPast :
        currentTime ≤
          selectedMessage.arrivalTime)
      (hTarget :
        selectedMessage.name =
          selectedServer.name)
      (hBind :
        ParameterStore.bindPayload
            selectedServer.parameters
            selectedMessage.payload =
          some boundParameters) :

      MultiStorePayloadDispatchStep
        messageServers
        {
          currentTime :=
            currentTime

          stateStore :=
            stateStore

          parameters :=
            parameters

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

          parameters :=
            boundParameters

          pendingMessages :=
            remainingMessages

          activeBody :=
            selectedServer.body
        }

namespace MultiStorePayloadDispatchStep

theorem selected_mem
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after) :
    selectedMessage ∈
      before.pendingMessages := by

  cases hDispatch with

  | fire
      _currentTime
      _stateStore
      _parameters
      _pendingMessages
      _remainingMessages
      _selectedMessage
      _selectedServer
      _boundParameters
      _hServerDeclared
      hRemoved
      _hPriorityEligible
      _hNotPast
      _hTarget
      _hBind =>

      exact
        Occurrence.RemovesOne.selected_mem
          hRemoved

theorem selectedServer_mem
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after) :
    selectedServer ∈
      messageServers := by

  cases hDispatch with

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
      _hPriorityEligible
      _hNotPast
      _hTarget
      _hBind =>

      exact hServerDeclared

theorem preserves_stateStore
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after) :
    after.stateStore =
      before.stateStore := by

  cases hDispatch
  rfl

theorem activates_server_body
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after) :
    after.activeBody =
      selectedServer.body := by

  cases hDispatch
  rfl

theorem binds_selected_payload
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {before after :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        before
        selectedMessage
        selectedServer
        after) :
    ParameterStore.bindPayload
        selectedServer.parameters
        selectedMessage.payload =
      some after.parameters := by

  cases hDispatch with

  | fire
      _currentTime
      _stateStore
      _parameters
      _pendingMessages
      _remainingMessages
      _selectedMessage
      _selectedServer
      _boundParameters
      _hServerDeclared
      _hRemoved
      _hPriorityEligible
      _hNotPast
      _hTarget
      hBind =>

      exact hBind

end MultiStorePayloadDispatchStep
end DTR
end Relico
