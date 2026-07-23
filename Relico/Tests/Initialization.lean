import Relico.Correctness.Initialization
import Relico.Tests.DTRWellFormed

set_option autoImplicit false

namespace Relico
namespace Tests

theorem validInitialStatesCorrespond :
    Correctness.StateCorresponds
      (DTR.initialState validModel 0)
      (LF.initialState
        (Translation.translateCore validModel)
        0) := by
  exact
    Correctness.initialStates_correspond
      validModel
      0

theorem validInitialDTRStateWellFormed :
    DTR.State.WellFormed
      validModel
      (DTR.initialState validModel 0) := by
  exact
    DTR.initialState_wellFormed
      validModel
      0
      validModel_wellFormed

def constructorAfterAssignment :
    DTR.State where
  currentTime := 0
  stateValue := 0
  pendingMessages := []
  activeBody := [
    .selfSend
      tickMessageName
      ⟨1⟩
  ]

theorem constructorFirstStep :
    DTR.Step
      validModel
      (DTR.initialState validModel 0)
      DTR.Label.internal
      constructorAfterAssignment := by
  simpa [
    DTR.initialState,
    constructorAfterAssignment,
    validModel,
    validReactiveClass,
    validConstructor
  ] using
    (DTR.Step.assign
      (model := validModel)
      (currentTime := 0)
      (stateValue := 0)
      (pendingMessages := [])
      (target := stateVariableName)
      (expression := .intLiteral 0)
      (remaining := [
        .selfSend
          tickMessageName
          ⟨1⟩
      ])
      (hTarget := rfl))

theorem constructorFirstTrace :
    DTR.Steps
      validModel
      (DTR.initialState validModel 0)
      [DTR.Label.internal]
      constructorAfterAssignment := by
  exact
    DTR.Steps.cons
      constructorFirstStep
      (DTR.Steps.refl
        constructorAfterAssignment)

theorem constructor_trace_has_matching_startup_trace :
    ∃ targetLabels targetStateAfter,
      LF.Steps
          (Translation.translateCore validModel)
          (LF.initialState
            (Translation.translateCore validModel)
            0)
          targetLabels
          targetStateAfter ∧
      Correctness.TraceCorresponds
          [DTR.Label.internal]
          targetLabels ∧
      Correctness.StateCorresponds
          constructorAfterAssignment
          targetStateAfter := by
  exact
    Correctness.initial_steps_forward
      constructorFirstTrace

theorem startupReflTrace :
    LF.Steps
      (Translation.translateCore validModel)
      (LF.initialState
        (Translation.translateCore validModel)
        0)
      []
      (LF.initialState
        (Translation.translateCore validModel)
        0) := by
  exact
    LF.Steps.refl
      (LF.initialState
        (Translation.translateCore validModel)
        0)

theorem startup_refl_has_matching_constructor_trace :
    ∃ sourceLabels sourceStateAfter,
      DTR.Steps
          validModel
          (DTR.initialState validModel 0)
          sourceLabels
          sourceStateAfter ∧
      Correctness.TraceCorresponds
          sourceLabels
          [] ∧
      Correctness.StateCorresponds
          sourceStateAfter
          (LF.initialState
            (Translation.translateCore validModel)
            0) ∧
      DTR.State.WellFormed
          validModel
          sourceStateAfter := by
  exact
    Correctness.initial_steps_backward
      startupReflTrace
      validModel_wellFormed

end Tests
end Relico
