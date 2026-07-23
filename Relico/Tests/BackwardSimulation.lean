import Relico.Correctness.Backward
import Relico.Tests.ForwardSimulation
import Relico.Tests.RuntimeInvariant

set_option autoImplicit false

namespace Relico
namespace Tests

theorem assignmentTargetStep :
    LF.Step
      (Translation.translateCore validModel)
      lfAssignmentSource
      LF.Label.internal
      lfAssignmentTarget := by
  simpa [
    lfAssignmentSource,
    lfAssignmentTarget,
    Translation.translateCore,
    Translation.compileReactor
  ] using
    (LF.Step.assign
      (program :=
        Translation.translateCore validModel)
      (currentTag := initialLFTag)
      (stateValue := 5)
      (pendingActions := [])
      (target := stateVariableName)
      (expression := .intLiteral 7)
      (remaining := [])
      (hTarget := rfl))

theorem assignment_has_matching_dtr_step :
    ∃ sourceLabel sourceStateAfter,
      DTR.Step
          validModel
          dtrAssignmentSource
          sourceLabel
          sourceStateAfter ∧
      Correctness.LabelCorresponds
          sourceLabel
          LF.Label.internal ∧
      Correctness.StateCorresponds
          sourceStateAfter
          lfAssignmentTarget := by
  exact
    Correctness.step_backward
      assignmentTargetStep
      assignmentSourceStateCorresponds
      dtrAssignmentSource_runtimeWellFormed

theorem scheduleTargetStep :
    LF.Step
      (Translation.translateCore validModel)
      lfScheduleSource
      (LF.Label.schedule
        expectedActionName
        (LF.Tag.schedule
          initialLFTag
          ⟨3⟩))
      lfScheduleTarget := by
  simpa [
    lfScheduleSource,
    lfScheduleTarget,
    expectedActionName,
    tickMessageName,
    Translation.actionNameFor,
    Translation.translateCore,
    Translation.compileReactor
  ] using
    (LF.Step.schedule
      (program :=
        Translation.translateCore validModel)
      (currentTag := initialLFTag)
      (stateValue := 5)
      (pendingActions := [])
      (targetAction :=
        Translation.actionNameFor
          tickMessageName)
      (delay := ⟨3⟩)
      (remaining := [])
      (hTarget := rfl))

theorem schedule_has_matching_dtr_step :
    ∃ sourceLabel sourceStateAfter,
      DTR.Step
          validModel
          dtrSendSource
          sourceLabel
          sourceStateAfter ∧
      Correctness.LabelCorresponds
          sourceLabel
          (LF.Label.schedule
            expectedActionName
            (LF.Tag.schedule
              initialLFTag
              ⟨3⟩)) ∧
      Correctness.StateCorresponds
          sourceStateAfter
          lfScheduleTarget := by
  exact
    Correctness.step_backward
      scheduleTargetStep
      sendSourceStateCorresponds
      dtrSendSource_runtimeWellFormed

end Tests
end Relico
