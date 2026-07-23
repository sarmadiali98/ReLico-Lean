import Relico.Correctness.Forward
import Relico.Tests.SmallStep

set_option autoImplicit false

namespace Relico
namespace Tests

theorem assignmentSourceStateCorresponds :
    Correctness.StateCorresponds
      dtrAssignmentSource
      lfAssignmentSource := by
  refine {
    currentTime := ?_
    stateValue := ?_
    pendingEvents := ?_
    activeBody := ?_
  }

  · simp [
      dtrAssignmentSource,
      lfAssignmentSource,
      initialLFTag
    ]

  · simp [
      dtrAssignmentSource,
      lfAssignmentSource
    ]

  · exact
      Correctness.QueueCorresponds.nil

  · simp [
      dtrAssignmentSource,
      lfAssignmentSource,
      Translation.compileBody,
      Translation.compileStmt,
      Translation.compileExpr
    ]

theorem assignment_has_matching_lf_step :
    ∃ targetLabel targetStateAfter,
      LF.Step
          (Translation.translateCore validModel)
          lfAssignmentSource
          targetLabel
          targetStateAfter ∧
      Correctness.LabelCorresponds
          DTR.Label.internal
          targetLabel ∧
      Correctness.StateCorresponds
          dtrAssignmentTarget
          targetStateAfter := by
  exact
    Correctness.step_forward
      (DTR.Step.assign
        (model := validModel)
        (currentTime := 2)
        (stateValue := 5)
        (pendingMessages := [])
        (target := stateVariableName)
        (expression := .intLiteral 7)
        (remaining := [])
        (hTarget := rfl))
      assignmentSourceStateCorresponds

theorem sendSourceStateCorresponds :
    Correctness.StateCorresponds
      dtrSendSource
      lfScheduleSource := by
  refine {
    currentTime := ?_
    stateValue := ?_
    pendingEvents := ?_
    activeBody := ?_
  }

  · simp [
      dtrSendSource,
      lfScheduleSource,
      initialLFTag
    ]

  · simp [
      dtrSendSource,
      lfScheduleSource
    ]

  · exact
      Correctness.QueueCorresponds.nil

  · simp [
      dtrSendSource,
      lfScheduleSource,
      expectedActionName,
      tickMessageName,
      Translation.compileBody,
      Translation.compileStmt,
      Translation.actionNameFor
    ]

theorem selfSend_has_matching_lf_step :
    ∃ targetLabel targetStateAfter,
      LF.Step
          (Translation.translateCore validModel)
          lfScheduleSource
          targetLabel
          targetStateAfter ∧
      Correctness.LabelCorresponds
          (.send
            tickMessageName
            (LogicalTime.after 2 ⟨3⟩))
          targetLabel ∧
      Correctness.StateCorresponds
          dtrSendTarget
          targetStateAfter := by
  exact
    Correctness.step_forward
      (DTR.Step.selfSend
        (model := validModel)
        (currentTime := 2)
        (stateValue := 5)
        (pendingMessages := [])
        (targetMessage := tickMessageName)
        (delay := ⟨3⟩)
        (remaining := [])
        (hTarget := rfl))
      sendSourceStateCorresponds

end Tests
end Relico
