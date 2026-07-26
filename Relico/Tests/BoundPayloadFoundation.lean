import Relico.Correctness.BoundPayloadState
import Relico.Tests.PayloadBinding

set_option autoImplicit false

namespace Relico
namespace Tests

def boundPayloadParameter :
    VarName :=
  ⟨"value"⟩

def boundPayloadMessage :
    MsgName :=
  ⟨"deliver"⟩

def boundPayloadDelay :
    Delay :=
  {
    value := 1
  }

def boundPayloadSourceExpression :
    DTR.PayloadExpr :=
  .parameterVar
    boundPayloadParameter

def boundPayloadSourceServer :
    DTR.PayloadMessageServer := {

  name :=
    boundPayloadMessage

  parameters :=
    [
      boundPayloadParameter
    ]

  body :=
    [
      DTR.BoundPayloadStmt.selfSendInt
        boundPayloadMessage
        boundPayloadSourceExpression
        boundPayloadDelay
    ]

  priority :=
    some 2
}

def boundPayloadTargetReaction :
    LF.PayloadReaction :=
  Translation.compilePayloadMessageServer
    boundPayloadSourceServer

def boundPayloadParameters :
    ParameterStore :=
  ParameterStore.singleton
    boundPayloadParameter
    42

def boundPayloadSourceState :
    DTR.BoundPayloadState := {

  currentTime :=
    3

  stateValue :=
    9

  parameters :=
    boundPayloadParameters

  pendingMessages :=
    []

  activeBody :=
    boundPayloadSourceServer.body
}

def boundPayloadTargetTag :
    LF.Tag := {

  time :=
    3

  microstep :=
    0
}

def boundPayloadTargetState :
    LF.BoundPayloadState := {

  currentTag :=
    boundPayloadTargetTag

  stateValue :=
    9

  parameters :=
    boundPayloadParameters

  pendingActions :=
    []

  activeBody :=
    boundPayloadTargetReaction.body
}

theorem bound_payload_formals_bind_exactly :
    ParameterStore.bindPayload
        boundPayloadSourceServer.parameters
        [
          42
        ] =
      some boundPayloadParameters := by

  simp [
    boundPayloadSourceServer,
    boundPayloadParameters
  ]

theorem bound_payload_action_name_generated :
    boundPayloadTargetReaction.logicalAction =
      Translation.actionNameFor
        boundPayloadMessage := by
  rfl

theorem bound_payload_parameters_preserved :
    boundPayloadTargetReaction.parameters =
      boundPayloadSourceServer.parameters := by
  rfl

theorem bound_payload_priority_preserved :
    boundPayloadTargetReaction.priority =
      boundPayloadSourceServer.priority := by
  rfl

theorem bound_payload_body_compiles_exactly :
    boundPayloadTargetReaction.body =
      Translation.compileBoundPayloadBody
        boundPayloadSourceServer.body := by
  rfl

theorem bound_payload_source_parameter_evaluates :
    DTR.PayloadExpr.evaluate
        boundPayloadSourceState.stateValue
        boundPayloadSourceState.parameters
        boundPayloadSourceExpression =
      some 42 := by

  simp [
    boundPayloadSourceState,
    boundPayloadSourceExpression,
    boundPayloadParameters
  ]

theorem bound_payload_target_parameter_evaluates :
    LF.PayloadExpr.evaluate
        boundPayloadTargetState.stateValue
        boundPayloadTargetState.parameters
        (Translation.compilePayloadExpr
          boundPayloadSourceExpression) =
      some 42 := by

  simp [
    boundPayloadTargetState,
    boundPayloadSourceExpression,
    boundPayloadParameters
  ]

theorem bound_payload_expression_evaluation_preserved :
    LF.PayloadExpr.evaluate
        boundPayloadTargetState.stateValue
        boundPayloadTargetState.parameters
        (Translation.compilePayloadExpr
          boundPayloadSourceExpression) =
      DTR.PayloadExpr.evaluate
        boundPayloadSourceState.stateValue
        boundPayloadSourceState.parameters
        boundPayloadSourceExpression := by

  exact
    Translation.compilePayloadExpr_preserves_evaluation
      boundPayloadSourceExpression
      9
      boundPayloadParameters

theorem bound_payload_foundation_states_correspond :
    Correctness.BoundPayloadStateCorresponds
      boundPayloadSourceState
      boundPayloadTargetState := by

  exact {
    currentTime :=
      rfl

    stateValue :=
      rfl

    parameters :=
      rfl

    pendingEvents :=
      Correctness.PayloadQueueCorresponds.nil

    activeBody :=
      rfl
  }

theorem bound_payload_foundation_ordinary_queues_correspond :
    Correctness.QueueCorresponds
      boundPayloadSourceState.pendingMessages
      boundPayloadTargetState.pendingActions := by

  exact
    Correctness.BoundPayloadStateCorresponds.pendingEventsOrdinary
      bound_payload_foundation_states_correspond

end Tests
end Relico
