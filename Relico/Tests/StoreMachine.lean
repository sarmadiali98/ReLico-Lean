import Relico.Correctness.StoreMachine
import Relico.Tests.StoreBackward
import Relico.Tests.StoreDispatch

set_option autoImplicit false

namespace Relico
namespace Tests

def storeDeclaredVariables :
    List VarName := [
  stateVariableName,
  secondStateVariableName
]

/--
The cross-variable assignment is a combined DTR store-machine step.
-/
theorem dtr_cross_variable_store_machine_step :
    DTR.StoreMachineStep
      storeDeclaredVariables
      storeRuntimeMessageName
      storeDispatchBody
      dtrStoreAssignmentBefore
      (DTR.StoreMachineLabel.statement
        DTR.Label.internal)
      dtrStoreAssignmentAfter := by

  exact
    DTR.StoreMachineStep.statement
      dtr_cross_variable_assignment

/--
The compiled cross-variable assignment is the matching generated-LF
combined-machine step.
-/
theorem lf_cross_variable_store_machine_step :
    LF.StoreMachineStep
      storeDeclaredVariables
      (Translation.actionNameFor
        storeRuntimeMessageName)
      (Translation.compileBody
        storeDispatchBody)
      lfStoreCorrespondingBefore
      (LF.StoreMachineLabel.statement
        LF.Label.internal)
      lfStoreAssignmentAfter := by

  exact
    LF.StoreMachineStep.statement
      compiled_cross_variable_target_step

theorem crossVariableAssignmentPendingTargets :
    ∀ pendingMessage,
      pendingMessage ∈
        dtrStoreAssignmentBefore.pendingMessages →
      pendingMessage.name =
        storeRuntimeMessageName := by

  intro pendingMessage hMember

  simp [
    dtrStoreAssignmentBefore
  ] at hMember

/--
Forward combined-machine simulation applies to the cross-variable
assignment.
-/
theorem cross_variable_store_machine_forward :
    ∃ targetLabel targetStateAfter,
      LF.StoreMachineStep
          storeDeclaredVariables
          (Translation.actionNameFor
            storeRuntimeMessageName)
          (Translation.compileBody
            storeDispatchBody)
          lfStoreCorrespondingBefore
          targetLabel
          targetStateAfter ∧
      Correctness.StoreMachineLabelCorresponds
        (DTR.StoreMachineLabel.statement
          DTR.Label.internal)
        targetLabel ∧
      Correctness.StoreStateCorresponds
        dtrStoreAssignmentAfter
        targetStateAfter := by

  apply
    Correctness.storeMachineStep_forward
      dtr_cross_variable_store_machine_step
      crossVariableStatesCorrespond

  simp [
    Correctness.StoreForwardMachineCompatible
  ]

/--
Backward combined-machine simulation recovers the source assignment
from the generated LF machine step.
-/
theorem cross_variable_store_machine_backward :
    ∃ sourceLabel sourceStateAfter,
      DTR.StoreMachineStep
          storeDeclaredVariables
          storeRuntimeMessageName
          storeDispatchBody
          dtrStoreAssignmentBefore
          sourceLabel
          sourceStateAfter ∧
      Correctness.StoreMachineLabelCorresponds
        sourceLabel
        (LF.StoreMachineLabel.statement
          LF.Label.internal) ∧
      Correctness.StoreStateCorresponds
        sourceStateAfter
        lfStoreAssignmentAfter := by

  exact
    Correctness.storeMachineStep_backward
      lf_cross_variable_store_machine_step
      crossVariableStatesCorrespond
      dtr_crossVariable_body_storeWellFormed
      crossVariableAssignmentPendingTargets

/--
The finite-store message dispatch is a combined source-machine step.
-/
theorem dtr_store_dispatch_machine_step :
    DTR.StoreMachineStep
      storeDeclaredVariables
      storeRuntimeMessageName
      storeDispatchBody
      dtrStoreDispatchSource
      (DTR.StoreMachineLabel.dispatch
        storeDispatchMessage)
      dtrStoreDispatchTarget := by

  exact
    DTR.StoreMachineStep.dispatch
      dtr_store_dispatch

/--
The corresponding generated logical-action dispatch is a combined
target-machine step.
-/
theorem lf_store_dispatch_machine_step :
    LF.StoreMachineStep
      storeDeclaredVariables
      (Translation.actionNameFor
        storeRuntimeMessageName)
      (Translation.compileBody
        storeDispatchBody)
      lfStoreDispatchSource
      (LF.StoreMachineLabel.dispatch
        storeDispatchAction)
      lfStoreDispatchTarget := by

  exact
    LF.StoreMachineStep.dispatch
      lf_store_dispatch

theorem storeDispatchMachineCompatible :
    Correctness.StoreForwardMachineCompatible
      (DTR.StoreMachineLabel.dispatch
        storeDispatchMessage)
      dtrStoreDispatchTarget
      lfStoreDispatchSource := by

  simpa [
    Correctness.StoreForwardMachineCompatible,
    dtrStoreDispatchTarget
  ] using
    storeDispatchForwardCompatible

theorem dtrStoreDispatchSourceBodyWellFormed :
    DTR.Body.StoreWellFormed
      storeDeclaredVariables
      storeRuntimeMessageName
      dtrStoreDispatchSource.activeBody := by

  simp [
    dtrStoreDispatchSource,
    storeDeclaredVariables
  ]

/--
Forward combined-machine simulation covers dispatch as well as
statement execution.
-/
theorem store_dispatch_machine_forward :
    ∃ targetLabel targetStateAfter,
      LF.StoreMachineStep
          storeDeclaredVariables
          (Translation.actionNameFor
            storeRuntimeMessageName)
          (Translation.compileBody
            storeDispatchBody)
          lfStoreDispatchSource
          targetLabel
          targetStateAfter ∧
      Correctness.StoreMachineLabelCorresponds
        (DTR.StoreMachineLabel.dispatch
          storeDispatchMessage)
        targetLabel ∧
      Correctness.StoreStateCorresponds
        dtrStoreDispatchTarget
        targetStateAfter := by

  exact
    Correctness.storeMachineStep_forward
      dtr_store_dispatch_machine_step
      storeDispatchSourceStatesCorrespond
      storeDispatchMachineCompatible

/--
Backward combined-machine simulation recovers the source dispatch from
the generated LF machine step.
-/
theorem store_dispatch_machine_backward :
    ∃ sourceLabel sourceStateAfter,
      DTR.StoreMachineStep
          storeDeclaredVariables
          storeRuntimeMessageName
          storeDispatchBody
          dtrStoreDispatchSource
          sourceLabel
          sourceStateAfter ∧
      Correctness.StoreMachineLabelCorresponds
        sourceLabel
        (LF.StoreMachineLabel.dispatch
          storeDispatchAction) ∧
      Correctness.StoreStateCorresponds
        sourceStateAfter
        lfStoreDispatchTarget := by

  exact
    Correctness.storeMachineStep_backward
      lf_store_dispatch_machine_step
      storeDispatchSourceStatesCorrespond
      dtrStoreDispatchSourceBodyWellFormed
      storeDispatchPendingTargets

end Tests
end Relico
