import Relico.DTR.GlobalMultiStorePayload

set_option autoImplicit false

namespace Relico
namespace DTR
namespace GlobalMultiStorePayloadExternalSend

/--
One explicit-delay external-send request.

The delay is mandatory in this verified fragment. There is no representation
for an omitted `after` clause.
-/
structure Request where
  sender :
    ActorName

  knownRebec :
    KnownRebecName

  messageName :
    MsgName

  payload :
    Payload

  delay :
    Delay

deriving Repr, DecidableEq, BEq, Inhabited

/--
The uniqueness key used by the supported external-send fragment.

Payload is intentionally absent: two different payloads sent over the same
sender/receiver/message-server edge at the same logical sending time are still
the prohibited LF-port collision case.
-/
structure Key where
  sender :
    ActorName

  receiver :
    ActorName

  messageName :
    MsgName

  sendTime :
    LogicalTime

deriving Repr, DecidableEq, BEq, Inhabited

/--
A resolved source external-send occurrence.

Sender and receiver identity are retained explicitly. Arrival time is computed
from the sender's current time, never from the receiver's local time.
-/
structure Occurrence where
  sender :
    ActorName

  receiver :
    ActorName

  knownRebec :
    KnownRebecName

  messageName :
    MsgName

  payload :
    Payload

  delay :
    Delay

  sendTime :
    LogicalTime

  arrivalTime :
    LogicalTime

deriving Repr, DecidableEq, BEq, Inhabited

inductive Failure where
  | senderModelMissing
  | senderStateMissing
  | receiverResolutionFailed
  | selfSendNotExternal
  | receiverModelMissing
  | receiverStateMissing
  | messageServerMissing
  | payloadArityMismatch
  | duplicateSameEdgeTime

deriving Repr, DecidableEq, BEq, Inhabited

structure Success where
  occurrence :
    Occurrence

  state :
    DTR.GlobalMultiStorePayloadState

  history :
    List Key

deriving Repr, DecidableEq, BEq, Inhabited

/--
Find the first target message-server declaration with the requested name.
-/
def lookupMessageServer :
    List DTR.MultiStorePayloadMessageServer →
    MsgName →
    Option DTR.MultiStorePayloadMessageServer

  | [], _ =>
      none

  | current :: remaining, messageName =>
      if current.name = messageName then
        some current
      else
        lookupMessageServer
          remaining
          messageName

/--
Construct the resolved occurrence from the sender state.
-/
def makeOccurrence
    (request : Request)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    Occurrence where

  sender :=
    request.sender

  receiver :=
    receiver

  knownRebec :=
    request.knownRebec

  messageName :=
    request.messageName

  payload :=
    request.payload

  delay :=
    request.delay

  sendTime :=
    senderState.currentTime

  arrivalTime :=
    LogicalTime.after
      senderState.currentTime
      request.delay

/--
Project the same-edge/same-time uniqueness key.
-/
def Occurrence.key
    (occurrence : Occurrence) :
    Key where

  sender :=
    occurrence.sender

  receiver :=
    occurrence.receiver

  messageName :=
    occurrence.messageName

  sendTime :=
    occurrence.sendTime

/--
The receiver-local pending message represented by the global occurrence.
-/
def Occurrence.pendingMessage
    (occurrence : Occurrence) :
    DTR.PendingMessage :=
  DTR.PendingMessage.scheduleWithPayload
    occurrence.sendTime
    occurrence.messageName
    occurrence.payload
    occurrence.delay

/--
Append exactly one occurrence to the receiver queue and preserve every other
receiver-local field.
-/
def receiverStateAfter
    (receiverState : DTR.MultiStorePayloadState)
    (occurrence : Occurrence) :
    DTR.MultiStorePayloadState :=
  {
    receiverState with
    pendingMessages :=
      receiverState.pendingMessages ++
        [occurrence.pendingMessage]
  }

/--
Execute one resolved and validated external-send construction.

This function performs no dispatch, global event selection, actor-priority
selection, or finite execution. It only resolves the topology, validates the
target declaration and payload arity, rejects the D3 same-edge/same-time
collision, and updates the receiver queue.
-/
def attempt
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history : List Key)
    (request : Request) :
    Except Failure Success :=
  match
      DTR.GlobalMultiStorePayloadModel.lookupActor
        model
        request.sender
  with
  | none =>
      .error .senderModelMissing

  | some _senderModel =>
      match
          DTR.GlobalMultiStorePayloadState.lookupActor
            state
            request.sender
      with
      | none =>
          .error .senderStateMissing

      | some senderState =>
          match
              ActorTopology.resolve
                model.topology
                request.sender
                request.knownRebec
          with
          | none =>
              .error .receiverResolutionFailed

          | some receiver =>
              if receiver = request.sender then
                .error .selfSendNotExternal
              else
                match
                    DTR.GlobalMultiStorePayloadModel.lookupActor
                      model
                      receiver
                with
                | none =>
                    .error .receiverModelMissing

                | some receiverModel =>
                    match
                        DTR.GlobalMultiStorePayloadState.lookupActor
                          state
                          receiver
                    with
                    | none =>
                        .error .receiverStateMissing

                    | some receiverState =>
                        match
                            lookupMessageServer
                              receiverModel.reactiveClass.messageServers
                              request.messageName
                        with
                        | none =>
                            .error .messageServerMissing

                        | some messageServer =>
                            if
                              messageServer.parameters.length =
                                request.payload.length
                            then
                              let occurrence :=
                                makeOccurrence
                                  request
                                  receiver
                                  senderState

                              if history.contains occurrence.key then
                                .error .duplicateSameEdgeTime
                              else
                                .ok {
                                  occurrence :=
                                    occurrence

                                  state :=
                                    DTR.GlobalMultiStorePayloadState.updateActor
                                      state
                                      receiver
                                      (receiverStateAfter
                                        receiverState
                                        occurrence)

                                  history :=
                                    history ++
                                      [occurrence.key]
                                }
                            else
                              .error .payloadArityMismatch

/--
The declarative version of the same-edge/same-time history restriction.
-/
def HistoryUnique
    (history : List Key) :
    Prop :=
  history.Nodup

/--
Appending a fresh external-send key preserves the same-edge/same-time
uniqueness invariant.
-/
theorem historyUnique_append_fresh
    {history : List Key}
    {key : Key}
    (hUnique :
      HistoryUnique history)
    (hFresh :
      key ∉ history) :
    HistoryUnique
      (history ++ [key]) := by

  induction history with

  | nil =>
      simp [HistoryUnique]

  | cons head tail inductionHypothesis =>
      have hHeadNeKey :
          head ≠ key := by
        intro hHeadEqKey
        apply hFresh
        simp [hHeadEqKey]

      simp_all [HistoryUnique]

@[simp]
theorem makeOccurrence_sendTime
    (request : Request)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (makeOccurrence
      request
      receiver
      senderState).sendTime =
      senderState.currentTime := by
  rfl

@[simp]
theorem makeOccurrence_arrivalTime
    (request : Request)
    (receiver : ActorName)
    (senderState : DTR.MultiStorePayloadState) :
    (makeOccurrence
      request
      receiver
      senderState).arrivalTime =
      LogicalTime.after
        senderState.currentTime
        request.delay := by
  rfl

@[simp]
theorem receiverStateAfter_pendingMessages
    (receiverState : DTR.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).pendingMessages =
      receiverState.pendingMessages ++
        [occurrence.pendingMessage] := by
  rfl

@[simp]
theorem receiverStateAfter_currentTime
    (receiverState : DTR.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).currentTime =
      receiverState.currentTime := by
  rfl

@[simp]
theorem receiverStateAfter_stateStore
    (receiverState : DTR.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).stateStore =
      receiverState.stateStore := by
  rfl

@[simp]
theorem receiverStateAfter_parameters
    (receiverState : DTR.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).parameters =
      receiverState.parameters := by
  rfl

@[simp]
theorem receiverStateAfter_activeBody
    (receiverState : DTR.MultiStorePayloadState)
    (occurrence : Occurrence) :
    (receiverStateAfter
      receiverState
      occurrence).activeBody =
      receiverState.activeBody := by
  rfl

end GlobalMultiStorePayloadExternalSend
end DTR
end Relico
