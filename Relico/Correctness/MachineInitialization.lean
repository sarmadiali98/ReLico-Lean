import Relico.Correctness.Initialization
import Relico.Correctness.MachineTrace
import Relico.Correctness.MachineTraceForward

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Constructor-entry and generated startup-entry states correspond for the
combined machine semantics.
-/
theorem initialMachineStates_correspond
    (model : DTR.Model)
    (initialValue : Int) :
    StateCorresponds
      (DTR.initialState model initialValue)
      (LF.initialState
        (Translation.translateCore model)
        initialValue) := by
  exact
    initialStates_correspond
      model
      initialValue

/--
Conditional finite forward simulation from constructor/startup entry.

The compatibility witness records the LF scheduler condition required
at every source dispatch step.
-/
theorem initialMachineSteps_forward_of_compatible
    {model : DTR.Model}
    {initialValue : Int}
    {sourceLabels : List DTR.MachineLabel}
    {sourceStateAfter : DTR.State}
    (hCompatible :
      ForwardMachineExecutionCompatible
        model
        (DTR.initialState
          model
          initialValue)
        sourceLabels
        sourceStateAfter
        (LF.initialState
          (Translation.translateCore model)
          initialValue)) :
    ∃ targetLabels targetStateAfter,
      DTR.MachineSteps
          model
          (DTR.initialState
            model
            initialValue)
          sourceLabels
          sourceStateAfter ∧
      LF.MachineSteps
          (Translation.translateCore model)
          (LF.initialState
            (Translation.translateCore model)
            initialValue)
          targetLabels
          targetStateAfter ∧
      MachineTraceCorresponds
          sourceLabels
          targetLabels ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by
  exact
    machineSteps_forward_of_compatible
      hCompatible

/--
Unconditional finite backward simulation from generated startup entry.

For a well-formed source model, every finite generated-LF startup
execution has a corresponding finite DTR constructor execution.
-/
theorem initialMachineSteps_backward
    {model : DTR.Model}
    {initialValue : Int}
    {targetLabels : List LF.MachineLabel}
    {targetStateAfter : LF.State}
    (hTargetSteps :
      LF.MachineSteps
        (Translation.translateCore model)
        (LF.initialState
          (Translation.translateCore model)
          initialValue)
        targetLabels
        targetStateAfter)
    (hModel :
      DTR.Model.WellFormed model) :
    ∃ sourceLabels sourceStateAfter,
      DTR.MachineSteps
          model
          (DTR.initialState
            model
            initialValue)
          sourceLabels
          sourceStateAfter ∧
      MachineTraceCorresponds
          sourceLabels
          targetLabels ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter ∧
      DTR.State.WellFormed
          model
          sourceStateAfter := by
  exact
    machineSteps_backward
      hTargetSteps
      (initialMachineStates_correspond
        model
        initialValue)
      hModel
      (DTR.initialState_wellFormed
        model
        initialValue
        hModel)

end Correctness
end Relico
