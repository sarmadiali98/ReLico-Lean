import Relico.DTR.GlobalMultiStorePayloadExternalSend

set_option autoImplicit false

namespace Relico
namespace DTR
namespace GlobalMultiStorePayloadExternalSendStatement

/--
An expression-bearing source external-send statement adapter.

This structure is additive. It does not extend or reinterpret
`DTR.MultiStorePayloadStmt`, whose `selfSend` constructor remains local to the
executing actor.
-/
structure Statement where
  sender :
    ActorName

  knownRebec :
    KnownRebecName

  messageName :
    MsgName

  payloadExpressions :
    List DTR.MultiStorePayloadExpr

  delay :
    Delay

deriving Repr, DecidableEq, BEq, Inhabited

namespace Statement

/--
Evaluate the ordered payload expressions in the current sender-local stores.
-/
def evaluatePayload?
    (statement : Statement)
    (senderState : DTR.MultiStorePayloadState) :
    Option Payload :=
  DTR.MultiStorePayloadExpr.evaluateAll
    senderState.stateStore
    senderState.parameters
    statement.payloadExpressions

/--
Construct the published E3a request after payload evaluation succeeds.
-/
def toRequest
    (statement : Statement)
    (payload : Payload) :
    DTR.GlobalMultiStorePayloadExternalSend.Request where

  sender :=
    statement.sender

  knownRebec :=
    statement.knownRebec

  messageName :=
    statement.messageName

  payload :=
    payload

  delay :=
    statement.delay

@[simp]
theorem toRequest_sender
    (statement : Statement)
    (payload : Payload) :
    (statement.toRequest payload).sender =
      statement.sender := by
  rfl

@[simp]
theorem toRequest_knownRebec
    (statement : Statement)
    (payload : Payload) :
    (statement.toRequest payload).knownRebec =
      statement.knownRebec := by
  rfl

@[simp]
theorem toRequest_messageName
    (statement : Statement)
    (payload : Payload) :
    (statement.toRequest payload).messageName =
      statement.messageName := by
  rfl

@[simp]
theorem toRequest_payload
    (statement : Statement)
    (payload : Payload) :
    (statement.toRequest payload).payload =
      payload := by
  rfl

@[simp]
theorem toRequest_delay
    (statement : Statement)
    (payload : Payload) :
    (statement.toRequest payload).delay =
      statement.delay := by
  rfl

end Statement

/--
Adapter-level failures.

Topology resolution, endpoint separation, target-server validation, payload
arity, collision rejection, sender-time scheduling, and receiver updates remain
owned by the published E3a foundation.
-/
inductive Failure where
  | senderStateMissing
  | payloadEvaluationFailed
  | foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Failure →
      Failure

deriving Repr, DecidableEq, BEq, Inhabited

/--
Evaluate one source statement adapter and delegate the validated send to E3a.

This function does not consume the sender active body and therefore is not a
complete global statement transition.
-/
def attempt
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (statement : Statement) :
    Except
      Failure
      DTR.GlobalMultiStorePayloadExternalSend.Success :=
  match
      DTR.GlobalMultiStorePayloadState.lookupActor
        state
        statement.sender
  with
  | none =>
      .error .senderStateMissing

  | some senderState =>
      match
          statement.evaluatePayload?
            senderState
      with
      | none =>
          .error .payloadEvaluationFailed

      | some payload =>
          match
              DTR.GlobalMultiStorePayloadExternalSend.attempt
                model
                state
                history
                (statement.toRequest payload)
          with
          | .error failure =>
              .error (.foundation failure)

          | .ok success =>
              .ok success

/--
Once sender lookup and payload evaluation are known, adapter execution is
definitionally the published E3a attempt with the constructed request.
-/
theorem attempt_of_lookup_and_evaluation
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (statement : Statement)
    (senderState : DTR.MultiStorePayloadState)
    (payload : Payload)
    (hLookup :
      DTR.GlobalMultiStorePayloadState.lookupActor
          state
          statement.sender =
        some senderState)
    (hEvaluate :
      statement.evaluatePayload?
          senderState =
        some payload) :
    attempt
        model
        state
        history
        statement =
      match
          DTR.GlobalMultiStorePayloadExternalSend.attempt
            model
            state
            history
            (statement.toRequest payload)
      with
      | .error failure =>
          .error (.foundation failure)

      | .ok success =>
          .ok success := by

  simp [
    attempt,
    hLookup,
    hEvaluate
  ]

/--
A successful E3a foundation attempt lifts directly to successful adapter
execution.
-/
theorem attempt_of_foundation_success
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (statement : Statement)
    (senderState : DTR.MultiStorePayloadState)
    (payload : Payload)
    (success :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (hLookup :
      DTR.GlobalMultiStorePayloadState.lookupActor
          state
          statement.sender =
        some senderState)
    (hEvaluate :
      statement.evaluatePayload?
          senderState =
        some payload)
    (hFoundation :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          state
          history
          (statement.toRequest payload) =
        .ok success) :
    attempt
        model
        state
        history
        statement =
      .ok success := by

  rw [
    attempt_of_lookup_and_evaluation
      model
      state
      history
      statement
      senderState
      payload
      hLookup
      hEvaluate,
    hFoundation
  ]

/--
An E3a foundation failure is retained exactly as an adapter foundation failure.
-/
theorem attempt_of_foundation_failure
    (model : DTR.GlobalMultiStorePayloadModel)
    (state : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (statement : Statement)
    (senderState : DTR.MultiStorePayloadState)
    (payload : Payload)
    (failure :
      DTR.GlobalMultiStorePayloadExternalSend.Failure)
    (hLookup :
      DTR.GlobalMultiStorePayloadState.lookupActor
          state
          statement.sender =
        some senderState)
    (hEvaluate :
      statement.evaluatePayload?
          senderState =
        some payload)
    (hFoundation :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          state
          history
          (statement.toRequest payload) =
        .error failure) :
    attempt
        model
        state
        history
        statement =
      .error (.foundation failure) := by

  rw [
    attempt_of_lookup_and_evaluation
      model
      state
      history
      statement
      senderState
      payload
      hLookup
      hEvaluate,
    hFoundation
  ]

/--
Reusable history composition for any successful result whose history has the
published E3a fresh-append shape.
-/
theorem historyUnique_of_successShape
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (success :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (hUnique :
      DTR.GlobalMultiStorePayloadExternalSend.HistoryUnique
        history)
    (hHistory :
      success.history =
        history ++
          [success.occurrence.key])
    (hFresh :
      success.occurrence.key ∉
        history) :
    DTR.GlobalMultiStorePayloadExternalSend.HistoryUnique
      success.history := by

  rw [hHistory]

  exact
    DTR.GlobalMultiStorePayloadExternalSend.historyUnique_append_fresh
      hUnique
      hFresh

end GlobalMultiStorePayloadExternalSendStatement
end DTR
end Relico
