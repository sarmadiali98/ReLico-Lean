import Relico.Correctness.GlobalMultiStorePayloadDeclaredFragment

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadDeclaredFragment

open Correctness.GlobalMultiStorePayloadDeclaredFragment

theorem explicitZeroDelay_regression :
    explicitZeroDelay.value = 0 :=
  explicitZeroDelay_value

theorem emptyHistory_contract :
    Contract ([] : List SourceKey) :=
  Contract.empty

theorem singletonHistory_contract
    (key : SourceKey) :
    Contract [key] :=
  Contract.singleton key

theorem appendFresh_contract
    {history : List SourceKey}
    {key : SourceKey}
    (contract : Contract history)
    (fresh : ¬key ∈ history) :
    Contract (history ++ [key]) :=
  Contract.append_fresh contract fresh

theorem contract_exposes_nodup
    {history : List SourceKey}
    (contract : Contract history) :
    history.Nodup :=
  Contract.history_nodup contract

theorem requestDelay_regression
    (request : SourceRequest) :
    ∃ delay : Delay,
      request.delay = delay :=
  request_delay_is_explicit request

theorem statementDelay_regression
    (statement : SourceStatement) :
    ∃ delay : Delay,
      statement.delay = delay :=
  statement_delay_is_explicit statement

theorem sourceKey_ext_regression
    {left right : SourceKey}
    (sender :
      left.sender = right.sender)
    (receiver :
      left.receiver = right.receiver)
    (messageName :
      left.messageName = right.messageName)
    (sendTime :
      left.sendTime = right.sendTime) :
    left = right :=
  sourceKey_ext
    sender
    receiver
    messageName
    sendTime

theorem occurrenceSender_regression
    (request : SourceRequest)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
      request
      receiver
      senderState).sender =
      request.sender :=
  makeOccurrence_sender request receiver senderState

theorem occurrenceReceiver_regression
    (request : SourceRequest)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
      request
      receiver
      senderState).receiver =
      receiver :=
  makeOccurrence_receiver request receiver senderState

theorem occurrenceSendTime_regression
    (request : SourceRequest)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
      request
      receiver
      senderState).sendTime =
      senderState.currentTime :=
  makeOccurrence_sendTime request receiver senderState

theorem occurrenceArrivalTime_regression
    (request : SourceRequest)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (DTR.GlobalMultiStorePayloadExternalSend.makeOccurrence
      request
      receiver
      senderState).arrivalTime =
      senderState.currentTime.after request.delay :=
  makeOccurrence_arrivalTime request receiver senderState

theorem reactionPriority_regression
    (server : DTR.MultiStorePayloadMessageServer) :
    (Translation.compileMultiStorePayloadReaction server).priority =
      server.priority :=
  compileReaction_priority server

#check SourcePriorityEligible
#check TargetPriorityEligible

end GlobalMultiStorePayloadDeclaredFragment
end Tests
end Relico
