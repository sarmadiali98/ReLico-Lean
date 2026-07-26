import Relico.Correctness.BoundPayloadStep
import Relico.Tests.BoundPayloadDispatchCorrectness

set_option autoImplicit false

namespace Relico
namespace Tests

def boundPayloadSemanticsSourceBefore :
    DTR.BoundPayloadState := {

  currentTime :=
    boundPayloadDispatchSourceSelected.arrivalTime

  stateValue :=
    9

  parameters :=
    boundPayloadParameters

  pendingMessages :=
    []

  activeBody :=
    [
      DTR.BoundPayloadStmt.selfSendInt
        boundPayloadMessage
        boundPayloadSourceExpression
        boundPayloadDelay
    ]
}

def boundPayloadSemanticsSourceLabel :
    DTR.BoundPayloadLabel :=
  DTR.BoundPayloadLabel.sendInt
    boundPayloadMessage
    (LogicalTime.after
      boundPayloadDispatchSourceSelected.arrivalTime
      boundPayloadDelay)
    42

def boundPayloadSemanticsSourceAfter :
    DTR.BoundPayloadState := {

  currentTime :=
    boundPayloadDispatchSourceSelected.arrivalTime

  stateValue :=
    9

  parameters :=
    boundPayloadParameters

  pendingMessages :=
    [
      DTR.PendingMessage.scheduleWithPayload
        boundPayloadDispatchSourceSelected.arrivalTime
        boundPayloadMessage
        [
          42
        ]
        boundPayloadDelay
    ]

  activeBody :=
    []
}

def boundPayloadSemanticsTargetBefore :
    LF.BoundPayloadState := {

  currentTag :=
    boundPayloadDispatchTargetSelected.tag

  stateValue :=
    9

  parameters :=
    boundPayloadParameters

  pendingActions :=
    []

  activeBody :=
    [
      LF.BoundPayloadStmt.scheduleInt
        (Translation.actionNameFor
          boundPayloadMessage)
        (Translation.compilePayloadExpr
          boundPayloadSourceExpression)
        boundPayloadDelay
    ]
}

def boundPayloadSemanticsTargetLabel :
    LF.BoundPayloadLabel :=
  LF.BoundPayloadLabel.scheduleInt
    (Translation.actionNameFor
      boundPayloadMessage)
    (LF.Tag.schedule
      boundPayloadDispatchTargetSelected.tag
      boundPayloadDelay)
    42

def boundPayloadSemanticsTargetAfter :
    LF.BoundPayloadState := {

  currentTag :=
    boundPayloadDispatchTargetSelected.tag

  stateValue :=
    9

  parameters :=
    boundPayloadParameters

  pendingActions :=
    [
      LF.PendingAction.scheduleWithPayload
        boundPayloadDispatchTargetSelected.tag
        (Translation.actionNameFor
          boundPayloadMessage)
        [
          42
        ]
        boundPayloadDelay
    ]

  activeBody :=
    []
}

theorem bound_payload_semantics_current_time_corresponds :
    boundPayloadDispatchTargetSelected.tag.time =
      boundPayloadDispatchSourceSelected.arrivalTime := by

  exact
    bound_payload_dispatch_selected_corresponds.occurrence.logicalTime

theorem bound_payload_semantics_before_corresponds :
    Correctness.BoundPayloadStateCorresponds
      boundPayloadSemanticsSourceBefore
      boundPayloadSemanticsTargetBefore := by

  exact {
    currentTime :=
      bound_payload_semantics_current_time_corresponds

    stateValue :=
      rfl

    parameters :=
      rfl

    pendingEvents :=
      Correctness.PayloadQueueCorresponds.nil

    activeBody :=
      rfl
  }

theorem bound_payload_semantics_source_step :
    DTR.BoundPayloadStep
      boundPayloadMessage
      boundPayloadSemanticsSourceBefore
      boundPayloadSemanticsSourceLabel
      boundPayloadSemanticsSourceAfter := by

  have hEvaluate :
      DTR.PayloadExpr.evaluate
          9
          boundPayloadParameters
          boundPayloadSourceExpression =
        some 42 := by

    simp [
      boundPayloadSourceExpression,
      boundPayloadParameters
    ]

  simpa [
    boundPayloadSemanticsSourceBefore,
    boundPayloadSemanticsSourceLabel,
    boundPayloadSemanticsSourceAfter
  ] using
    DTR.BoundPayloadStep.selfSendInt
      (declaredMessageServer :=
        boundPayloadMessage)
      (currentTime :=
        boundPayloadDispatchSourceSelected.arrivalTime)
      (stateValue :=
        9)
      (parameters :=
        boundPayloadParameters)
      (pendingMessages :=
        [])
      (targetMessage :=
        boundPayloadMessage)
      (payloadExpression :=
        boundPayloadSourceExpression)
      (delay :=
        boundPayloadDelay)
      (evaluatedValue :=
        42)
      (remaining :=
        [])
      rfl
      hEvaluate

theorem bound_payload_semantics_target_step :
    LF.BoundPayloadStep
      (Translation.actionNameFor
        boundPayloadMessage)
      boundPayloadSemanticsTargetBefore
      boundPayloadSemanticsTargetLabel
      boundPayloadSemanticsTargetAfter := by

  have hEvaluate :
      LF.PayloadExpr.evaluate
          9
          boundPayloadParameters
          (Translation.compilePayloadExpr
            boundPayloadSourceExpression) =
        some 42 := by

    simp [
      boundPayloadSourceExpression,
      boundPayloadParameters
    ]

  simpa [
    boundPayloadSemanticsTargetBefore,
    boundPayloadSemanticsTargetLabel,
    boundPayloadSemanticsTargetAfter
  ] using
    LF.BoundPayloadStep.scheduleInt
      (declaredAction :=
        Translation.actionNameFor
          boundPayloadMessage)
      (currentTag :=
        boundPayloadDispatchTargetSelected.tag)
      (stateValue :=
        9)
      (parameters :=
        boundPayloadParameters)
      (pendingActions :=
        [])
      (targetAction :=
        Translation.actionNameFor
          boundPayloadMessage)
      (payloadExpression :=
        Translation.compilePayloadExpr
          boundPayloadSourceExpression)
      (delay :=
        boundPayloadDelay)
      (evaluatedValue :=
        42)
      (remaining :=
        [])
      rfl
      hEvaluate

theorem bound_payload_semantics_label_corresponds :
    Correctness.BoundPayloadLabelCorresponds
      boundPayloadSemanticsSourceLabel
      boundPayloadSemanticsTargetLabel := by

  unfold
    Correctness.BoundPayloadLabelCorresponds

  refine
    ⟨rfl,
     ?_,
     rfl⟩

  calc
    (LF.Tag.schedule
      boundPayloadDispatchTargetSelected.tag
      boundPayloadDelay).time =
      LogicalTime.after
        boundPayloadDispatchTargetSelected.tag.time
        boundPayloadDelay :=

          LF.Tag.schedule_time
            boundPayloadDispatchTargetSelected.tag
            boundPayloadDelay

    _ =
      LogicalTime.after
        boundPayloadDispatchSourceSelected.arrivalTime
        boundPayloadDelay := by

          rw [
            bound_payload_semantics_current_time_corresponds
          ]

theorem bound_payload_semantics_after_corresponds :
    Correctness.BoundPayloadStateCorresponds
      boundPayloadSemanticsSourceAfter
      boundPayloadSemanticsTargetAfter := by

  refine {
    currentTime :=
      bound_payload_semantics_current_time_corresponds

    stateValue :=
      rfl

    parameters :=
      rfl

    pendingEvents :=
      ?_

    activeBody :=
      rfl
  }

  simpa [
    boundPayloadSemanticsSourceAfter,
    boundPayloadSemanticsTargetAfter
  ] using
    Correctness.payloadQueueCorresponds_append_scheduleWithPayload
      Correctness.PayloadQueueCorresponds.nil
      boundPayloadDispatchSourceSelected.arrivalTime
      boundPayloadDispatchTargetSelected.tag
      boundPayloadMessage
      [
        42
      ]
      boundPayloadDelay
      bound_payload_semantics_current_time_corresponds

theorem bound_payload_semantics_forward_exists :
    ∃ targetLabel targetAfter,
      LF.BoundPayloadStep
          (Translation.actionNameFor
            boundPayloadMessage)
          boundPayloadSemanticsTargetBefore
          targetLabel
          targetAfter ∧
        Correctness.BoundPayloadLabelCorresponds
          boundPayloadSemanticsSourceLabel
          targetLabel ∧
        Correctness.BoundPayloadStateCorresponds
          boundPayloadSemanticsSourceAfter
          targetAfter := by

  exact
    Correctness.boundPayloadStep_forward
      bound_payload_semantics_before_corresponds
      bound_payload_semantics_source_step

theorem bound_payload_semantics_backward_exists :
    ∃ sourceLabel sourceAfter,
      DTR.BoundPayloadStep
          boundPayloadMessage
          boundPayloadSemanticsSourceBefore
          sourceLabel
          sourceAfter ∧
        Correctness.BoundPayloadLabelCorresponds
          sourceLabel
          boundPayloadSemanticsTargetLabel ∧
        Correctness.BoundPayloadStateCorresponds
          sourceAfter
          boundPayloadSemanticsTargetAfter := by

  exact
    Correctness.boundPayloadStep_backward
      bound_payload_semantics_before_corresponds
      bound_payload_semantics_target_step

theorem bound_payload_semantics_source_parameter_preserved :
    boundPayloadSemanticsSourceAfter.parameters =
      boundPayloadSemanticsSourceBefore.parameters := by

  exact
    DTR.BoundPayloadStep.preserves_parameters
      bound_payload_semantics_source_step

theorem bound_payload_semantics_target_parameter_preserved :
    boundPayloadSemanticsTargetAfter.parameters =
      boundPayloadSemanticsTargetBefore.parameters := by

  exact
    LF.BoundPayloadStep.preserves_parameters
      bound_payload_semantics_target_step

theorem bound_payload_semantics_scheduled_value_exact :
    boundPayloadSemanticsSourceAfter.pendingMessages =
      [
        DTR.PendingMessage.scheduleWithPayload
          boundPayloadDispatchSourceSelected.arrivalTime
          boundPayloadMessage
          [
            42
          ]
          boundPayloadDelay
      ] := by
  rfl

end Tests
end Relico
