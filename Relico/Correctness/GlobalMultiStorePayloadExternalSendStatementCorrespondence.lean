import Relico.Correctness.GlobalMultiStorePayloadExternalSendCorrespondence
import Relico.Correctness.MultiStorePayloadStatementCorrespondence
import Relico.Translation.GlobalMultiStorePayloadExternalSendStatement

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Metadata and expression correspondence for one additive external-send statement
adapter.
-/
structure GlobalMultiStorePayloadExternalSendStatementCorresponds
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement)
    (target :
      LF.GlobalMultiStorePayloadExternalSendStatement.Statement) :
    Prop where

  sender :
    target.sender =
      source.sender

  knownRebec :
    target.knownRebec =
      source.knownRebec

  actionName :
    target.actionName =
      Translation.actionNameFor
        source.messageName

  payloadExpressions :
    target.payloadExpressions =
      Translation.compileMultiStorePayloadExprs
        source.payloadExpressions

  delay :
    target.delay =
      source.delay

/--
Canonical statement translation establishes exact metadata and payload-expression
correspondence.
-/
theorem translated_globalMultiStorePayloadExternalSendStatement_corresponds
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement) :
    GlobalMultiStorePayloadExternalSendStatementCorresponds
      source
      (Translation.translateGlobalMultiStorePayloadExternalSendStatement
        source) := by

  exact {
    sender := rfl
    knownRebec := rfl
    actionName := rfl
    payloadExpressions := rfl
    delay := rfl
  }

/--
The request constructed after evaluation retains the exact statement metadata
and the evaluated ordered payload.
-/
structure GlobalMultiStorePayloadExternalSendStatementRequestCorresponds
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement)
    (payload : Payload)
    (request :
      DTR.GlobalMultiStorePayloadExternalSend.Request) :
    Prop where

  sender :
    request.sender =
      source.sender

  knownRebec :
    request.knownRebec =
      source.knownRebec

  messageName :
    request.messageName =
      source.messageName

  payload :
    request.payload =
      payload

  delay :
    request.delay =
      source.delay

theorem globalMultiStorePayloadExternalSendStatement_toRequest_corresponds
    (source :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement)
    (payload : Payload) :
    GlobalMultiStorePayloadExternalSendStatementRequestCorresponds
      source
      payload
      (source.toRequest payload) := by

  exact {
    sender := rfl
    knownRebec := rfl
    messageName := rfl
    payload := rfl
    delay := rfl
  }

/--
Compiled payload expressions evaluate to the same ordered payload whenever the
sender-local states satisfy the published local correspondence.
-/
theorem translated_globalMultiStorePayloadExternalSendStatement_evaluatePayload
    (statement :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement)
    (sourceState : DTR.MultiStorePayloadState)
    (targetState : LF.MultiStorePayloadState)
    (payload : Payload)
    (hStates :
      MultiStorePayloadStateCorresponds
        sourceState
        targetState)
    (hEvaluate :
      statement.evaluatePayload?
          sourceState =
        some payload) :
    (Translation.translateGlobalMultiStorePayloadExternalSendStatement
        statement).evaluatePayload?
        targetState =
      some payload := by

  change
    LF.MultiStorePayloadExpr.evaluateAll
        targetState.stateStore
        targetState.parameters
        (Translation.compileMultiStorePayloadExprs
          statement.payloadExpressions) =
      some payload

  calc
    LF.MultiStorePayloadExpr.evaluateAll
        targetState.stateStore
        targetState.parameters
        (Translation.compileMultiStorePayloadExprs
          statement.payloadExpressions) =
      DTR.MultiStorePayloadExpr.evaluateAll
        targetState.stateStore
        targetState.parameters
        statement.payloadExpressions := by
          exact
            Correctness.compileMultiStorePayloadExprs_evaluateAll
              targetState.stateStore
              targetState.parameters
              statement.payloadExpressions

    _ =
      DTR.MultiStorePayloadExpr.evaluateAll
        sourceState.stateStore
        sourceState.parameters
        statement.payloadExpressions := by
          rw [
            hStates.stateStore,
            hStates.parameters
          ]

    _ =
      some payload :=
        hEvaluate

/--
Package target payload evaluation with successful adapter delegation to a known
successful E3a foundation attempt.
-/
theorem translated_globalMultiStorePayloadExternalSendStatement_attempt_success
    (statement :
      DTR.GlobalMultiStorePayloadExternalSendStatement.Statement)
    (sourceSenderState : DTR.MultiStorePayloadState)
    (targetSenderState : LF.MultiStorePayloadState)
    (payload : Payload)
    (model : DTR.GlobalMultiStorePayloadModel)
    (globalState : DTR.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (success :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (hStates :
      MultiStorePayloadStateCorresponds
        sourceSenderState
        targetSenderState)
    (hEvaluate :
      statement.evaluatePayload?
          sourceSenderState =
        some payload)
    (hLookup :
      DTR.GlobalMultiStorePayloadState.lookupActor
          globalState
          statement.sender =
        some sourceSenderState)
    (hFoundation :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          globalState
          history
          (statement.toRequest payload) =
        .ok success) :
    (Translation.translateGlobalMultiStorePayloadExternalSendStatement
        statement).evaluatePayload?
        targetSenderState =
      some payload ∧
      DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
          model
          globalState
          history
          statement =
        .ok success := by

  constructor

  · exact
      translated_globalMultiStorePayloadExternalSendStatement_evaluatePayload
        statement
        sourceSenderState
        targetSenderState
        payload
        hStates
        hEvaluate

  · exact
      DTR.GlobalMultiStorePayloadExternalSendStatement.attempt_of_foundation_success
        model
        globalState
        history
        statement
        sourceSenderState
        payload
        success
        hLookup
        hEvaluate
        hFoundation

end Correctness
end Relico
