import Relico.Correctness.StoreTrace
import Relico.Tests.StoreBackward

set_option autoImplicit false

namespace Relico
namespace Tests

/--
The cross-variable DTR assignment forms a one-transition finite trace.
-/
theorem dtr_cross_variable_trace :
    DTR.StoreTrace
      [
        stateVariableName,
        secondStateVariableName
      ]
      storeRuntimeMessageName
      dtrStoreAssignmentBefore
      [DTR.Label.internal]
      dtrStoreAssignmentAfter := by

  exact
    DTR.StoreTrace.step
      dtr_cross_variable_assignment
      (DTR.StoreTrace.refl
        dtrStoreAssignmentAfter)

/--
The compiled LF assignment forms the corresponding one-transition
finite trace.
-/
theorem lf_cross_variable_trace :
    LF.StoreTrace
      [
        stateVariableName,
        secondStateVariableName
      ]
      (Translation.actionNameFor
        storeRuntimeMessageName)
      lfStoreCorrespondingBefore
      [LF.Label.internal]
      lfStoreAssignmentAfter := by

  exact
    LF.StoreTrace.step
      compiled_cross_variable_target_step
      (LF.StoreTrace.refl
        lfStoreAssignmentAfter)

/--
Forward finite-trace simulation applies to the cross-variable
assignment.
-/
theorem compiled_cross_variable_trace_exists :
    ∃ targetLabels targetFinal,
      LF.StoreTrace
          [
            stateVariableName,
            secondStateVariableName
          ]
          (Translation.actionNameFor
            storeRuntimeMessageName)
          lfStoreCorrespondingBefore
          targetLabels
          targetFinal ∧
      Correctness.LabelTraceCorresponds
        [DTR.Label.internal]
        targetLabels ∧
      Correctness.StoreStateCorresponds
        dtrStoreAssignmentAfter
        targetFinal := by

  exact
    Correctness.store_trace_forward
      dtr_cross_variable_trace
      crossVariableStatesCorrespond

/--
Backward finite-trace simulation recovers a source trace from the
compiled LF execution.
-/
theorem compiled_cross_variable_trace_has_source :
    ∃ sourceLabels sourceFinal,
      DTR.StoreTrace
          [
            stateVariableName,
            secondStateVariableName
          ]
          storeRuntimeMessageName
          dtrStoreAssignmentBefore
          sourceLabels
          sourceFinal ∧
      Correctness.LabelTraceCorresponds
        sourceLabels
        [LF.Label.internal] ∧
      Correctness.StoreStateCorresponds
        sourceFinal
        lfStoreAssignmentAfter := by

  exact
    Correctness.store_trace_backward
      lf_cross_variable_trace
      crossVariableStatesCorrespond
      dtr_crossVariable_body_storeWellFormed

end Tests
end Relico
