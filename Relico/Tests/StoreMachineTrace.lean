import Relico.Correctness.StoreMachineTrace
import Relico.Tests.StoreMachine

set_option autoImplicit false

namespace Relico
namespace Tests

/--
The store-backed message dispatch forms a finite source machine
execution.
-/
theorem dtr_store_dispatch_machine_steps :
    DTR.StoreMachineSteps
      storeDeclaredVariables
      storeRuntimeMessageName
      storeDispatchBody
      dtrStoreDispatchSource
      [
        DTR.StoreMachineLabel.dispatch
          storeDispatchMessage
      ]
      dtrStoreDispatchTarget := by

  exact
    DTR.StoreMachineSteps.cons
      dtr_store_dispatch_machine_step
      (DTR.StoreMachineSteps.refl
        dtrStoreDispatchTarget)

/--
The generated logical-action dispatch forms the corresponding finite
target machine execution.
-/
theorem lf_store_dispatch_machine_steps :
    LF.StoreMachineSteps
      storeDeclaredVariables
      (Translation.actionNameFor
        storeRuntimeMessageName)
      (Translation.compileBody
        storeDispatchBody)
      lfStoreDispatchSource
      [
        LF.StoreMachineLabel.dispatch
          storeDispatchAction
      ]
      lfStoreDispatchTarget := by

  exact
    LF.StoreMachineSteps.cons
      lf_store_dispatch_machine_step
      (LF.StoreMachineSteps.refl
        lfStoreDispatchTarget)

theorem storeDispatchBodyWellFormed :
    DTR.Body.StoreWellFormed
      storeDeclaredVariables
      storeRuntimeMessageName
      storeDispatchBody := by

  simp [
    storeDispatchBody,
    storeDeclaredVariables,
    DTR.Body.StoreWellFormed,
    DTR.Stmt.StoreWellFormed,
    DTR.Expr.StoreWellFormed
  ]

theorem dtrStoreDispatchSource_runtimeWellFormed :
    DTR.StoreState.RuntimeWellFormed
      storeDeclaredVariables
      storeRuntimeMessageName
      dtrStoreDispatchSource := by

  exact {
    coverage := by
      simpa [
        DTR.StoreState.Covers,
        dtrStoreDispatchSource,
        storeDeclaredVariables
      ] using
        twoVariableStore_covers

    activeBody := by
      simp [
        dtrStoreDispatchSource,
        DTR.Body.StoreWellFormed
      ]

    pendingTargets :=
      storeDispatchPendingTargets
  }

/--
The dispatch trace preserves complete finite-store runtime
well-formedness.
-/
theorem dtr_store_dispatch_trace_preserves_runtimeWellFormed :
    DTR.StoreState.RuntimeWellFormed
      storeDeclaredVariables
      storeRuntimeMessageName
      dtrStoreDispatchTarget := by

  exact
    Correctness.dtrStoreMachineSteps_preserve_runtimeWellFormed
      dtr_store_dispatch_machine_steps
      storeDispatchBodyWellFormed
      dtrStoreDispatchSource_runtimeWellFormed

/--
Compatibility evidence for the one-dispatch forward execution.
-/
theorem storeDispatchMachineStepsCompatible :
    Correctness.StoreForwardMachineStepsCompatible
      storeDeclaredVariables
      storeRuntimeMessageName
      storeDispatchBody
      dtr_store_dispatch_machine_steps
      lfStoreDispatchSource := by

  unfold
    Correctness.StoreForwardMachineStepsCompatible

  simp only [
    Correctness.StoreForwardMachineLabelsCompatible
  ]

  intro sourceMiddle
  intro hSourceHead
  intro hSourceTail

  cases hSourceTail with

  | refl state =>
      refine
        ⟨storeDispatchMachineCompatible,
         ?_⟩

      intro targetLabel
      intro targetMiddle
      intro hTargetStep
      intro hLabels
      intro hStates

      rfl

/--
Forward finite-machine simulation applies to the compatible dispatch
execution.
-/
theorem store_dispatch_machine_steps_forward :
    ∃ targetLabels targetAfter,
      LF.StoreMachineSteps
          storeDeclaredVariables
          (Translation.actionNameFor
            storeRuntimeMessageName)
          (Translation.compileBody
            storeDispatchBody)
          lfStoreDispatchSource
          targetLabels
          targetAfter ∧
      Correctness.StoreMachineTraceCorresponds
        [
          DTR.StoreMachineLabel.dispatch
            storeDispatchMessage
        ]
        targetLabels ∧
      Correctness.StoreStateCorresponds
        dtrStoreDispatchTarget
        targetAfter := by

  exact
    Correctness.storeMachineSteps_forward_of_compatible
      dtr_store_dispatch_machine_steps
      storeDispatchSourceStatesCorrespond
      storeDispatchMachineStepsCompatible

/--
Backward finite-machine simulation recovers a source execution from
the generated LF dispatch trace.
-/
theorem store_dispatch_machine_steps_backward :
    ∃ sourceLabels sourceAfter,
      DTR.StoreMachineSteps
          storeDeclaredVariables
          storeRuntimeMessageName
          storeDispatchBody
          dtrStoreDispatchSource
          sourceLabels
          sourceAfter ∧
      Correctness.StoreMachineTraceCorresponds
        sourceLabels
        [
          LF.StoreMachineLabel.dispatch
            storeDispatchAction
        ] ∧
      Correctness.StoreStateCorresponds
        sourceAfter
        lfStoreDispatchTarget ∧
      DTR.StoreState.RuntimeWellFormed
        storeDeclaredVariables
        storeRuntimeMessageName
        sourceAfter := by

  exact
    Correctness.storeMachineSteps_backward
      lf_store_dispatch_machine_steps
      storeDispatchSourceStatesCorrespond
      storeDispatchBodyWellFormed
      dtrStoreDispatchSource_runtimeWellFormed

end Tests
end Relico
