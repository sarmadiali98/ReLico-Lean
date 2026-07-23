import Relico.Correctness.StoreBackward
import Relico.Tests.StoreForward
import Relico.Tests.StoreStructural

set_option autoImplicit false

namespace Relico
namespace Tests

/--
The compiled cross-variable assignment performs the expected generated
LF store step.
-/
theorem compiled_cross_variable_target_step :
    LF.StoreStep
      [
        stateVariableName,
        secondStateVariableName
      ]
      (Translation.actionNameFor
        storeRuntimeMessageName)
      lfStoreCorrespondingBefore
      LF.Label.internal
      lfStoreAssignmentAfter := by

  apply LF.StoreStep.assign

  · simp

  · rfl

/--
Backward simulation recovers a matching DTR store transition from the
compiled cross-variable LF assignment.
-/
theorem compiled_cross_variable_step_has_source :
    ∃ sourceLabel sourceStateAfter,
      DTR.StoreStep
          [
            stateVariableName,
            secondStateVariableName
          ]
          storeRuntimeMessageName
          dtrStoreAssignmentBefore
          sourceLabel
          sourceStateAfter ∧
      Correctness.LabelCorresponds
        sourceLabel
        LF.Label.internal ∧
      Correctness.StoreStateCorresponds
        sourceStateAfter
        lfStoreAssignmentAfter := by

  exact
    Correctness.store_step_backward
      compiled_cross_variable_target_step
      crossVariableStatesCorrespond
      dtr_crossVariable_body_storeWellFormed

end Tests
end Relico
