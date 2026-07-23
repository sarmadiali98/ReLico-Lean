import Relico.Correctness.Trace
import Relico.Tests.BackwardSimulation

set_option autoImplicit false

namespace Relico
namespace Tests

theorem assignmentSourceTrace :
    DTR.Steps
      validModel
      dtrAssignmentSource
      [DTR.Label.internal]
      dtrAssignmentTarget := by
  apply DTR.Steps.cons

  · exact
      DTR.Step.assign
        (model := validModel)
        (currentTime := 2)
        (stateValue := 5)
        (pendingMessages := [])
        (target := stateVariableName)
        (expression := .intLiteral 7)
        (remaining := [])
        (hTarget := rfl)

  · exact
      DTR.Steps.refl
        dtrAssignmentTarget

theorem assignment_trace_has_matching_lf_trace :
    ∃ targetLabels targetStateAfter,
      LF.Steps
          (Translation.translateCore validModel)
          lfAssignmentSource
          targetLabels
          targetStateAfter ∧
      Correctness.TraceCorresponds
          [DTR.Label.internal]
          targetLabels ∧
      Correctness.StateCorresponds
          dtrAssignmentTarget
          targetStateAfter := by
  exact
    Correctness.steps_forward
      assignmentSourceTrace
      assignmentSourceStateCorresponds

theorem assignmentTargetTrace :
    LF.Steps
      (Translation.translateCore validModel)
      lfAssignmentSource
      [LF.Label.internal]
      lfAssignmentTarget := by
  apply LF.Steps.cons

  · exact assignmentTargetStep

  · exact
      LF.Steps.refl
        lfAssignmentTarget

theorem assignment_trace_has_matching_dtr_trace :
    ∃ sourceLabels sourceStateAfter,
      DTR.Steps
          validModel
          dtrAssignmentSource
          sourceLabels
          sourceStateAfter ∧
      Correctness.TraceCorresponds
          sourceLabels
          [LF.Label.internal] ∧
      Correctness.StateCorresponds
          sourceStateAfter
          lfAssignmentTarget ∧
      DTR.State.WellFormed
          validModel
          sourceStateAfter := by
  exact
    Correctness.steps_backward
      assignmentTargetTrace
      assignmentSourceStateCorresponds
      dtrAssignmentSource_runtimeWellFormed

end Tests
end Relico
