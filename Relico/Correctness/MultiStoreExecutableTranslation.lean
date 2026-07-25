import Relico.Correctness.MultiStoreInitialization
import Relico.Correctness.MultiStoreMachineTrace
import Relico.DTR.MultiStoreModelWellFormed

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Conditional finite forward correctness from source constructor entry
to generated startup entry for the executable multi-server compiler
core.

The compatibility premise records source scheduler choices that can be
represented by the generated LF tag and microstep order.
-/
theorem translateMultiStoreCore_initialMachineSteps_forward
    {model : DTR.MultiStoreModel}
    {sourceAfter : DTR.StoreState}
    {sourceLabels :
      List DTR.MultiStoreMachineLabel}
    (hSourceSteps :
      DTR.MultiStoreMachineSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServers
        (DTR.MultiStoreModel.initialState
          model)
        sourceLabels
        sourceAfter)
    (hCompatible :
      MultiStoreForwardMachineStepsCompatible
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServers
        hSourceSteps
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            model))) :
    ∃ targetLabels targetAfter,
      LF.MultiStoreMachineSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          (Translation.compileLogicalActions
            model.reactiveClass.messageServers)
          (Translation.compileMessageReactions
            model.reactiveClass.messageServers)
          (LF.MultiStoreProgram.initialState
            (Translation.translateMultiStoreCore
              model))
          targetLabels
          targetAfter ∧
      MultiStoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter := by

  exact
    multiStoreMachineSteps_forward_of_compatible
      hSourceSteps
      (translateMultiStoreCore_initialStates_correspond
        model)
      hCompatible

/--
Conditional finite forward correctness for the program returned by the
public executable multi-server translator.
-/
theorem translateMultiStore_initialMachineSteps_forward
    {model : DTR.MultiStoreModel}
    {program : LF.MultiStoreProgram}
    {sourceAfter : DTR.StoreState}
    {sourceLabels :
      List DTR.MultiStoreMachineLabel}
    (hTranslate :
      Translation.translateMultiStore model =
        .ok program)
    (hSourceSteps :
      DTR.MultiStoreMachineSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServers
        (DTR.MultiStoreModel.initialState
          model)
        sourceLabels
        sourceAfter)
    (hCompatible :
      MultiStoreForwardMachineStepsCompatible
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServers
        hSourceSteps
        (LF.MultiStoreProgram.initialState
          program)) :
    ∃ targetLabels targetAfter,
      LF.MultiStoreMachineSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          (Translation.compileLogicalActions
            model.reactiveClass.messageServers)
          (Translation.compileMessageReactions
            model.reactiveClass.messageServers)
          (LF.MultiStoreProgram.initialState
            program)
          targetLabels
          targetAfter ∧
      MultiStoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter := by

  have hProgram :
      Translation.translateMultiStoreCore
          model =
        program := by

    simpa [
      Translation.translateMultiStore
    ] using
      hTranslate

  subst program

  exact
    translateMultiStoreCore_initialMachineSteps_forward
      hSourceSteps
      hCompatible

/--
Finite backward correctness from generated startup entry to source
constructor entry for a structurally well-formed multi-server model in
the positive-delay priority timing fragment.

Every finite generated-LF execution is matched by a finite source
execution. Runtime well-formedness and the priority timing invariants
used by dispatch correspondence are preserved.
-/
theorem translateMultiStoreCore_initialMachineSteps_backward
    {model : DTR.MultiStoreModel}
    (hModel :
      DTR.MultiStoreModel.WellFormed
        model)
    (hPriorityTiming :
      DTR.MultiStoreModel.PriorityTimingWellFormed
        model)
    {targetAfter : LF.StoreState}
    {targetLabels :
      List LF.MultiStoreMachineLabel}
    (hTargetSteps :
      LF.MultiStoreMachineSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        (Translation.compileLogicalActions
          model.reactiveClass.messageServers)
        (Translation.compileMessageReactions
          model.reactiveClass.messageServers)
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            model))
        targetLabels
        targetAfter) :
    ∃ sourceLabels sourceAfter,
      DTR.MultiStoreMachineSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          model.reactiveClass.messageServers
          (DTR.MultiStoreModel.initialState
            model)
          sourceLabels
          sourceAfter ∧
      MultiStoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter ∧
      DTR.StoreState.MultiStoreRuntimeWellFormed
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServers
        sourceAfter := by

  have hTargetInitialMicrostepsZero :
      LF.StoreState.PendingMicrostepsZero
        (LF.MultiStoreProgram.initialState
          (Translation.translateMultiStoreCore
            model)) := by

    intro action hAction

    simp [
      LF.MultiStoreProgram.initialState,
      Translation.translateMultiStoreCore
    ] at hAction

  have hSourceInitialTiming :
      DTR.Body.PriorityTimingWellFormed
        (DTR.MultiStoreModel.initialState
          model).activeBody := by

    simpa [
      DTR.MultiStoreModel.initialState
    ] using
      hPriorityTiming.constructorBody

  exact
    multiStoreMachineSteps_backward
      hTargetSteps
      (translateMultiStoreCore_initialStates_correspond
        model)
      hTargetInitialMicrostepsZero
      hModel.messageServerBodiesWellFormed
      hPriorityTiming.messageServerBodies
      (DTR.MultiStoreModel.initialState_runtimeWellFormed
        model
        hModel)
      hSourceInitialTiming

/--
Finite backward correctness for the program returned by the public
executable multi-server translator in the positive-delay priority timing
fragment.
-/
theorem translateMultiStore_initialMachineSteps_backward
    {model : DTR.MultiStoreModel}
    {program : LF.MultiStoreProgram}
    (hModel :
      DTR.MultiStoreModel.WellFormed
        model)
    (hPriorityTiming :
      DTR.MultiStoreModel.PriorityTimingWellFormed
        model)
    (hTranslate :
      Translation.translateMultiStore model =
        .ok program)
    {targetAfter : LF.StoreState}
    {targetLabels :
      List LF.MultiStoreMachineLabel}
    (hTargetSteps :
      LF.MultiStoreMachineSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        (Translation.compileLogicalActions
          model.reactiveClass.messageServers)
        (Translation.compileMessageReactions
          model.reactiveClass.messageServers)
        (LF.MultiStoreProgram.initialState
          program)
        targetLabels
        targetAfter) :
    ∃ sourceLabels sourceAfter,
      DTR.MultiStoreMachineSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          model.reactiveClass.messageServers
          (DTR.MultiStoreModel.initialState
            model)
          sourceLabels
          sourceAfter ∧
      MultiStoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter ∧
      DTR.StoreState.MultiStoreRuntimeWellFormed
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServers
        sourceAfter := by

  have hProgram :
      Translation.translateMultiStoreCore
          model =
        program := by

    simpa [
      Translation.translateMultiStore
    ] using
      hTranslate

  subst program

  exact
    translateMultiStoreCore_initialMachineSteps_backward
      hModel
      hPriorityTiming
      hTargetSteps

end Correctness
end Relico
