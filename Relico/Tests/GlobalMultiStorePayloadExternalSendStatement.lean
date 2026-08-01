import Relico.Correctness.GlobalMultiStorePayloadExternalSendStatementCorrespondence
import Relico.Tests.GlobalMultiStorePayloadExternalSend

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadExternalSendStatement

open DTR.GlobalMultiStorePayloadExternalSend
open Relico.Tests.GlobalMultiStorePayloadExternalSend

def positiveStatement :
    DTR.GlobalMultiStorePayloadExternalSendStatement.Statement where

  sender :=
    senderActor

  knownRebec :=
    receiverReference

  messageName :=
    deliverMessage

  payloadExpressions :=
    [
      .intLiteral 7
    ]

  delay :=
    { value := 3 }

def positiveTargetStatement :
    LF.GlobalMultiStorePayloadExternalSendStatement.Statement :=
  Translation.translateGlobalMultiStorePayloadExternalSendStatement
    positiveStatement

def positiveExpectedSuccess :
    DTR.GlobalMultiStorePayloadExternalSend.Success where

  occurrence :=
    positiveSourceOccurrence

  state :=
    DTR.GlobalMultiStorePayloadState.updateActor
      sourceState
      receiverActor
      (DTR.GlobalMultiStorePayloadExternalSend.receiverStateAfter
        receiverSourceState
        positiveSourceOccurrence)

  history :=
    [
      positiveSourceOccurrence.key
    ]

/--
The additive statement translation preserves sender identity, topology
reference, generated action name, expressions, and explicit delay.
-/
theorem positive_statement_translation_is_exact :
    positiveTargetStatement.sender =
        senderActor ∧
      positiveTargetStatement.knownRebec =
        receiverReference ∧
      positiveTargetStatement.actionName =
        Translation.actionNameFor
          deliverMessage ∧
      positiveTargetStatement.payloadExpressions =
        [
          .intLiteral 7
        ] ∧
      positiveTargetStatement.delay =
        { value := 3 } := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
The source expression list evaluates to the exact ordered payload used by E3a.
-/
theorem positive_source_payload_evaluates :
    positiveStatement.evaluatePayload?
        senderSourceState =
      some [7] := by
  rfl

/--
The translated expression list evaluates to the same ordered payload.
-/
theorem positive_target_payload_evaluates :
    positiveTargetStatement.evaluatePayload?
        senderTargetState =
      some [7] := by

  exact
    Correctness.translated_globalMultiStorePayloadExternalSendStatement_evaluatePayload
      positiveStatement
      senderSourceState
      senderTargetState
      [7]
      senderStatesCorrespond
      rfl

/--
Request construction is exact and introduces no omitted-delay case.
-/
theorem positive_request_is_existing_e3a_request :
    positiveStatement.toRequest [7] =
      positiveRequest := by
  rfl

/--
The successful adapter execution is definitionally the existing validated E3a
send.
-/
theorem positive_adapter_attempt_succeeds :
    DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
        sourceModel
        sourceState
        []
        positiveStatement =
      .ok positiveExpectedSuccess := by
  rfl

/--
The packaged correctness theorem simultaneously establishes translated payload
evaluation and adapter delegation.
-/
theorem positive_translated_attempt_succeeds :
    positiveTargetStatement.evaluatePayload?
          senderTargetState =
        some [7] ∧
      DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
          sourceModel
          sourceState
          []
          positiveStatement =
        .ok positiveExpectedSuccess := by

  exact
    Correctness.translated_globalMultiStorePayloadExternalSendStatement_attempt_success
      positiveStatement
      senderSourceState
      senderTargetState
      [7]
      sourceModel
      sourceState
      []
      positiveExpectedSuccess
      senderStatesCorrespond
      rfl
      rfl
      rfl

def missingPayloadVariable : VarName :=
  ⟨"missingPayload"⟩

def failedEvaluationStatement :
    DTR.GlobalMultiStorePayloadExternalSendStatement.Statement :=
  {
    positiveStatement with

    payloadExpressions :=
      [
        .stateVar missingPayloadVariable
      ]
  }

/--
Failed payload evaluation is detected before topology resolution or receiver
mutation.
-/
theorem failed_payload_evaluation_is_rejected :
    DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
        sourceModel
        sourceState
        []
        failedEvaluationStatement =
      .error .payloadEvaluationFailed := by
  rfl

def stateWithoutSender :
    DTR.GlobalMultiStorePayloadState where

  currentTime :=
    5

  actorStates :=
    [
      (
        receiverActor,
        receiverSourceState
      )
    ]

/--
A missing sender state is an adapter-level failure.
-/
theorem missing_sender_state_is_rejected :
    DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
        sourceModel
        stateWithoutSender
        []
        positiveStatement =
      .error .senderStateMissing := by
  rfl

def wrongArityStatement :
    DTR.GlobalMultiStorePayloadExternalSendStatement.Statement :=
  {
    positiveStatement with

    payloadExpressions :=
      []
  }

/--
Target-server arity validation remains owned by E3a and is retained exactly.
-/
theorem foundation_arity_failure_is_retained :
    DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
        sourceModel
        sourceState
        []
        wrongArityStatement =
      .error
        (.foundation
          .payloadArityMismatch) := by
  rfl

/--
A topology edge resolving to the sender remains rejected as a self-send, not
silently accepted by the external-send adapter.
-/
theorem foundation_self_resolution_failure_is_retained :
    DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
        selfGlobalModel
        selfGlobalState
        []
        positiveStatement =
      .error
        (.foundation
          .selfSendNotExternal) := by
  rfl

def zeroDelayStatement :
    DTR.GlobalMultiStorePayloadExternalSendStatement.Statement :=
  {
    positiveStatement with

    payloadExpressions :=
      [
        .intLiteral 9
      ]

    delay :=
      { value := 0 }
  }

def zeroDelayTargetStatement :
    LF.GlobalMultiStorePayloadExternalSendStatement.Statement :=
  Translation.translateGlobalMultiStorePayloadExternalSendStatement
    zeroDelayStatement

/--
Explicit zero delay remains represented and translated exactly.
-/
theorem explicit_zero_delay_is_preserved :
    zeroDelayTargetStatement.delay =
        { value := 0 } ∧
      zeroDelayTargetStatement.evaluatePayload?
          senderTargetState =
        some [9] := by
  exact ⟨rfl, rfl⟩

/--
The successful result has the E3a fresh-append history shape.
-/
theorem positive_success_history_shape :
    positiveExpectedSuccess.history =
      [] ++
        [positiveExpectedSuccess.occurrence.key] := by
  rfl

/--
The reusable E3b1 history theorem establishes uniqueness of the successful
history.
-/
theorem positive_success_history_unique :
    HistoryUnique
      positiveExpectedSuccess.history := by

  exact
    DTR.GlobalMultiStorePayloadExternalSendStatement.historyUnique_of_successShape
      []
      positiveExpectedSuccess
      (by simp [HistoryUnique])
      rfl
      (by simp)

/--
The executable successful adapter branch therefore returns a unique history.
-/
theorem positive_adapter_attempt_returns_unique_history :
    match
      DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
        sourceModel
        sourceState
        []
        positiveStatement
    with
    | .error _ =>
        False

    | .ok success =>
        HistoryUnique
          success.history := by

  change
    HistoryUnique
      positiveExpectedSuccess.history

  exact
    positive_success_history_unique

/--
E3b1 delegates only the receiver update. It does not consume or replace the
sender continuation.
-/
theorem positive_adapter_preserves_sender_state :
    DTR.GlobalMultiStorePayloadState.lookupActor
        positiveExpectedSuccess.state
        senderActor =
      some senderSourceState := by

  exact
    source_sender_state_is_unchanged

end GlobalMultiStorePayloadExternalSendStatement
end Tests
end Relico
