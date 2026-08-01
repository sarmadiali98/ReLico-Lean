import Relico.DTR.GlobalMultiStorePayloadExternalSend
import Relico.DTR.GlobalMultiStorePayloadExternalSendStatement
import Relico.DTR.MultiStorePayloadDispatch
import Relico.LF.MultiStorePayloadDispatch
import Relico.Translation.MultiStorePayloadBasic

namespace Relico
namespace Correctness
namespace GlobalMultiStorePayloadDeclaredFragment

/--
The source-side collision key for external sends.

It contains the sender, receiver, target message-server name, and logical
sending time. Payload is deliberately absent.
-/
abbrev SourceKey :=
  DTR.GlobalMultiStorePayloadExternalSend.Key

abbrev SourceRequest :=
  DTR.GlobalMultiStorePayloadExternalSend.Request

abbrev SourceStatement :=
  DTR.GlobalMultiStorePayloadExternalSendStatement.Statement

abbrev SourceOccurrence :=
  DTR.GlobalMultiStorePayloadExternalSend.Occurrence

/--
The existing actor-local source priority-eligibility relation.
-/
abbrev SourcePriorityEligible :=
  DTR.MultiStorePayloadIsPriorityEligible

/--
The existing actor-local target priority-eligibility relation.
-/
abbrev TargetPriorityEligible :=
  LF.MultiStorePayloadIsReactionPriorityEligible

/--
An explicit zero delay is an ordinary `Delay` whose natural value is zero.
-/
def explicitZeroDelay :
    Delay :=
  {
    value := 0
  }

@[simp]
theorem explicitZeroDelay_value :
    explicitZeroDelay.value = 0 := by
  rfl

/--
Every source request carries an explicit delay by construction.
-/
theorem request_delay_is_explicit
    (request : SourceRequest) :
    ∃ delay : Delay,
      request.delay = delay := by
  exact ⟨request.delay, rfl⟩

/--
Every expression-bearing source external-send statement carries an explicit
delay by construction.
-/
theorem statement_delay_is_explicit
    (statement : SourceStatement) :
    ∃ delay : Delay,
      statement.delay = delay := by
  exact ⟨statement.delay, rfl⟩

/--
The dynamic declared-fragment contract.

All other E4A facts are structural or definitional. The only stored dynamic
assumption is uniqueness of the accumulated external-send collision keys.
-/
structure Contract
    (history : List SourceKey) :
    Prop where
  historyUnique :
    DTR.GlobalMultiStorePayloadExternalSend.HistoryUnique history

theorem Contract.empty :
    Contract [] := by
  constructor
  simp [
    DTR.GlobalMultiStorePayloadExternalSend.HistoryUnique
  ]

theorem Contract.singleton
    (key : SourceKey) :
    Contract [key] := by
  constructor
  simp [
    DTR.GlobalMultiStorePayloadExternalSend.HistoryUnique
  ]

theorem Contract.history_nodup
    {history : List SourceKey}
    (contract : Contract history) :
    history.Nodup := by
  simpa [
    DTR.GlobalMultiStorePayloadExternalSend.HistoryUnique
  ] using contract.historyUnique

theorem Contract.append_fresh
    {history : List SourceKey}
    {key : SourceKey}
    (contract : Contract history)
    (fresh : ¬key ∈ history) :
    Contract (history ++ [key]) := by
  constructor
  exact
    DTR.GlobalMultiStorePayloadExternalSend.historyUnique_append_fresh
      contract.historyUnique
      fresh

/--
The external-send collision key is completely determined by its four
declared fields.
-/
theorem sourceKey_ext
    {left right : SourceKey}
    (sender :
      left.sender = right.sender)
    (receiver :
      left.receiver = right.receiver)
    (messageName :
      left.messageName = right.messageName)
    (sendTime :
      left.sendTime = right.sendTime) :
    left = right := by
  cases left with
  | mk leftSender leftReceiver leftMessageName leftSendTime =>
      cases right with
      | mk rightSender rightReceiver rightMessageName rightSendTime =>
          cases sender
          cases receiver
          cases messageName
          cases sendTime
          rfl

theorem makeOccurrence_sender
    (request : SourceRequest)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
      request
      receiver
      senderState).sender =
      request.sender := by
  rfl

theorem makeOccurrence_receiver
    (request : SourceRequest)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
      request
      receiver
      senderState).receiver =
      receiver := by
  rfl

theorem makeOccurrence_sendTime
    (request : SourceRequest)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
      request
      receiver
      senderState).sendTime =
      senderState.currentTime := by
  rfl

theorem makeOccurrence_arrivalTime
    (request : SourceRequest)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
      request
      receiver
      senderState).arrivalTime =
      senderState.currentTime.after request.delay := by
  exact
    DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence_arrivalTime
      request
      receiver
      senderState

/--
Compilation preserves actor-local message-server priority definitionally.
-/
@[simp]
theorem compileReaction_priority
    (server : DTR.MultiStorePayloadMessageServer) :
    (Translation.compileMultiStorePayloadReaction server).priority =
      server.priority := by
  rfl

end GlobalMultiStorePayloadDeclaredFragment
end Correctness
end Relico
