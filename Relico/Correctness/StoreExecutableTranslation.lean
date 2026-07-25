import Relico.Correctness.StoreInitialization
import Relico.Correctness.StoreMachineTrace
import Relico.DTR.StoreModelWellFormed

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Conditional finite forward correctness from constructor entry to
generated startup entry for the executable finite-store compiler core.

The compatibility premise records the source scheduling choices that
can be represented by the generated LF microstep order.
-/
theorem translateStoreCore_initialMachineSteps_forward
    {model : DTR.StoreModel}
    {sourceAfter : DTR.StoreState}
    {sourceLabels : List DTR.StoreMachineLabel}
    (hSourceSteps :
      DTR.StoreMachineSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServer.name
        model.reactiveClass.messageServer.body
        (DTR.StoreModel.initialState
          model)
        sourceLabels
        sourceAfter)
    (hCompatible :
      StoreForwardMachineStepsCompatible
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServer.name
        model.reactiveClass.messageServer.body
        hSourceSteps
        (LF.StoreProgram.initialState
          (Translation.translateStoreCore
            model))) :
    ∃ targetLabels targetAfter,
      LF.StoreMachineSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          (Translation.actionNameFor
            model.reactiveClass.messageServer.name)
          (Translation.compileBody
            model.reactiveClass.messageServer.body)
          (LF.StoreProgram.initialState
            (Translation.translateStoreCore
              model))
          targetLabels
          targetAfter ∧
      StoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter := by

  exact
    storeMachineSteps_forward_of_compatible
      hSourceSteps
      (translateStoreCore_initialStates_correspond
        model)
      hCompatible

/--
Conditional finite forward correctness for the program returned by
the public executable finite-store translator.
-/
theorem translateStore_initialMachineSteps_forward
    {model : DTR.StoreModel}
    {program : LF.StoreProgram}
    {sourceAfter : DTR.StoreState}
    {sourceLabels : List DTR.StoreMachineLabel}
    (hTranslate :
      Translation.translateStore model =
        .ok program)
    (hSourceSteps :
      DTR.StoreMachineSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServer.name
        model.reactiveClass.messageServer.body
        (DTR.StoreModel.initialState
          model)
        sourceLabels
        sourceAfter)
    (hCompatible :
      StoreForwardMachineStepsCompatible
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServer.name
        model.reactiveClass.messageServer.body
        hSourceSteps
        (LF.StoreProgram.initialState
          program)) :
    ∃ targetLabels targetAfter,
      LF.StoreMachineSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          (Translation.actionNameFor
            model.reactiveClass.messageServer.name)
          (Translation.compileBody
            model.reactiveClass.messageServer.body)
          (LF.StoreProgram.initialState
            program)
          targetLabels
          targetAfter ∧
      StoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter := by

  have hProgram :
      Translation.translateStoreCore
          model =
        program := by

    simpa [
      Translation.translateStore
    ] using
      hTranslate

  subst program

  exact
    translateStoreCore_initialMachineSteps_forward
      hSourceSteps
      hCompatible

/--
Unconditional finite backward correctness from generated startup entry
to source constructor entry for a well-formed finite-store model.

Every finite execution of the generated LF machine is matched by a
finite DTR execution. Runtime well-formedness is preserved in the
recovered source state.
-/
theorem translateStoreCore_initialMachineSteps_backward
    {model : DTR.StoreModel}
    (hModel :
      DTR.StoreModel.WellFormed
        model)
    {targetAfter : LF.StoreState}
    {targetLabels : List LF.StoreMachineLabel}
    (hTargetSteps :
      LF.StoreMachineSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        (Translation.actionNameFor
          model.reactiveClass.messageServer.name)
        (Translation.compileBody
          model.reactiveClass.messageServer.body)
        (LF.StoreProgram.initialState
          (Translation.translateStoreCore
            model))
        targetLabels
        targetAfter) :
    ∃ sourceLabels sourceAfter,
      DTR.StoreMachineSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          model.reactiveClass.messageServer.name
          model.reactiveClass.messageServer.body
          (DTR.StoreModel.initialState
            model)
          sourceLabels
          sourceAfter ∧
      StoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter ∧
      DTR.StoreState.RuntimeWellFormed
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServer.name
        sourceAfter := by

  exact
    storeMachineSteps_backward
      hTargetSteps
      (translateStoreCore_initialStates_correspond
        model)
      hModel.messageServerBodyWellFormed
      (DTR.StoreModel.initialState_runtimeWellFormed
        model
        hModel)

/--
Unconditional finite backward correctness for the program returned by
the public executable finite-store translator.
-/
theorem translateStore_initialMachineSteps_backward
    {model : DTR.StoreModel}
    {program : LF.StoreProgram}
    (hModel :
      DTR.StoreModel.WellFormed
        model)
    (hTranslate :
      Translation.translateStore model =
        .ok program)
    {targetAfter : LF.StoreState}
    {targetLabels : List LF.StoreMachineLabel}
    (hTargetSteps :
      LF.StoreMachineSteps
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        (Translation.actionNameFor
          model.reactiveClass.messageServer.name)
        (Translation.compileBody
          model.reactiveClass.messageServer.body)
        (LF.StoreProgram.initialState
          program)
        targetLabels
        targetAfter) :
    ∃ sourceLabels sourceAfter,
      DTR.StoreMachineSteps
          (DTR.stateVariableNames
            model.reactiveClass.stateVariables)
          model.reactiveClass.messageServer.name
          model.reactiveClass.messageServer.body
          (DTR.StoreModel.initialState
            model)
          sourceLabels
          sourceAfter ∧
      StoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter ∧
      DTR.StoreState.RuntimeWellFormed
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        model.reactiveClass.messageServer.name
        sourceAfter := by

  have hProgram :
      Translation.translateStoreCore
          model =
        program := by

    simpa [
      Translation.translateStore
    ] using
      hTranslate

  subst program

  exact
    translateStoreCore_initialMachineSteps_backward
      hModel
      hTargetSteps

end Correctness
end Relico
