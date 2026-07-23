import Relico.Correctness.StoreForward
import Relico.Tests.StoreSemantics

set_option autoImplicit false

namespace Relico
namespace Tests

def lfStoreCorrespondingBefore :
    LF.StoreState where

  currentTag :=
    default

  stateStore :=
    twoVariableStore

  pendingActions :=
    []

  activeBody :=
    Translation.compileBody
      dtrStoreAssignmentBefore.activeBody

theorem crossVariableStatesCorrespond :
    Correctness.StoreStateCorresponds
      dtrStoreAssignmentBefore
      lfStoreCorrespondingBefore := by

  exact {
    currentTime :=
      rfl

    stateStore :=
      rfl

    pendingEvents :=
      Correctness.QueueCorresponds.nil

    activeBody :=
      rfl
  }

/--
The executable compiler produces a matching LF store transition for the
cross-variable DTR assignment.
-/
theorem compiled_cross_variable_step_exists :
    ∃ targetLabel targetStateAfter,
      LF.StoreStep
          [
            stateVariableName,
            secondStateVariableName
          ]
          (Translation.actionNameFor
            storeRuntimeMessageName)
          lfStoreCorrespondingBefore
          targetLabel
          targetStateAfter ∧
      Correctness.LabelCorresponds
        DTR.Label.internal
        targetLabel ∧
      Correctness.StoreStateCorresponds
        dtrStoreAssignmentAfter
        targetStateAfter := by

  exact
    Correctness.store_step_forward
      dtr_cross_variable_assignment
      crossVariableStatesCorrespond

end Tests
end Relico
