import Relico.Correctness.Trace
import Relico.DTR.Initialization
import Relico.LF.Initialization

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
The source constructor-entry state corresponds to the generated LF
startup-reaction entry state.
-/
theorem initialStates_correspond
    (model : DTR.Model)
    (initialValue : Int) :
    StateCorresponds
      (DTR.initialState model initialValue)
      (LF.initialState
        (Translation.translateCore model)
        initialValue) := by
  exact {
    currentTime := rfl
    stateValue := rfl
    pendingEvents :=
      QueueCorresponds.nil
    activeBody := rfl
  }

/--
Every finite constructor execution has a corresponding generated-LF
startup-reaction execution.
-/
theorem initial_steps_forward
    {model : DTR.Model}
    {initialValue : Int}
    {sourceStateAfter : DTR.State}
    {sourceLabels : List DTR.Label}
    (hSourceSteps :
      DTR.Steps
        model
        (DTR.initialState
          model
          initialValue)
        sourceLabels
        sourceStateAfter) :
    ∃ targetLabels targetStateAfter,
      LF.Steps
          (Translation.translateCore model)
          (LF.initialState
            (Translation.translateCore model)
            initialValue)
          targetLabels
          targetStateAfter ∧
      TraceCorresponds
          sourceLabels
          targetLabels ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by
  exact
    steps_forward
      hSourceSteps
      (initialStates_correspond
        model
        initialValue)

/--
Every finite generated-LF startup-reaction execution has a matching
DTR constructor execution for a well-formed source model.
-/
theorem initial_steps_backward
    {model : DTR.Model}
    {initialValue : Int}
    {targetStateAfter : LF.State}
    {targetLabels : List LF.Label}
    (hTargetSteps :
      LF.Steps
        (Translation.translateCore model)
        (LF.initialState
          (Translation.translateCore model)
          initialValue)
        targetLabels
        targetStateAfter)
    (hModel :
      DTR.Model.WellFormed model) :
    ∃ sourceLabels sourceStateAfter,
      DTR.Steps
          model
          (DTR.initialState
            model
            initialValue)
          sourceLabels
          sourceStateAfter ∧
      TraceCorresponds
          sourceLabels
          targetLabels ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter ∧
      DTR.State.WellFormed
          model
          sourceStateAfter := by
  exact
    steps_backward
      hTargetSteps
      (initialStates_correspond
        model
        initialValue)
      (DTR.initialState_wellFormed
        model
        initialValue
        hModel)

end Correctness
end Relico
