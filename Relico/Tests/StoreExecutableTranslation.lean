import Relico.Correctness.StoreExecutableTranslation
import Relico.Tests.StoreInitialization

set_option autoImplicit false

namespace Relico
namespace Tests

theorem twoState_initial_refl_execution_forward :
    ∃ targetLabels targetAfter,
      LF.StoreMachineSteps
          (DTR.stateVariableNames
            twoStateModel.reactiveClass.stateVariables)
          (Translation.actionNameFor
            twoStateModel.reactiveClass.messageServer.name)
          (Translation.compileBody
            twoStateModel.reactiveClass.messageServer.body)
          (LF.StoreProgram.initialState
            (Translation.translateStoreCore
              twoStateModel))
          targetLabels
          targetAfter ∧
      Correctness.StoreMachineTraceCorresponds
        []
        targetLabels ∧
      Correctness.StoreStateCorresponds
        (DTR.StoreModel.initialState
          twoStateModel)
        targetAfter := by

  have hSourceSteps :
      DTR.StoreMachineSteps
        (DTR.stateVariableNames
          twoStateModel.reactiveClass.stateVariables)
        twoStateModel.reactiveClass.messageServer.name
        twoStateModel.reactiveClass.messageServer.body
        (DTR.StoreModel.initialState
          twoStateModel)
        []
        (DTR.StoreModel.initialState
          twoStateModel) :=

    DTR.StoreMachineSteps.refl
      _

  have hCompatible :
      Correctness.StoreForwardMachineStepsCompatible
        (DTR.stateVariableNames
          twoStateModel.reactiveClass.stateVariables)
        twoStateModel.reactiveClass.messageServer.name
        twoStateModel.reactiveClass.messageServer.body
        hSourceSteps
        (LF.StoreProgram.initialState
          (Translation.translateStoreCore
            twoStateModel)) := by

    simp [
      Correctness.StoreForwardMachineStepsCompatible,
      Correctness.StoreForwardMachineLabelsCompatible
    ]

  exact
    Correctness.translateStoreCore_initialMachineSteps_forward
      hSourceSteps
      hCompatible

theorem twoState_initial_refl_execution_backward :
    ∃ sourceLabels sourceAfter,
      DTR.StoreMachineSteps
          (DTR.stateVariableNames
            twoStateModel.reactiveClass.stateVariables)
          twoStateModel.reactiveClass.messageServer.name
          twoStateModel.reactiveClass.messageServer.body
          (DTR.StoreModel.initialState
            twoStateModel)
          sourceLabels
          sourceAfter ∧
      Correctness.StoreMachineTraceCorresponds
        sourceLabels
        [] ∧
      Correctness.StoreStateCorresponds
        sourceAfter
        (LF.StoreProgram.initialState
          (Translation.translateStoreCore
            twoStateModel)) ∧
      DTR.StoreState.RuntimeWellFormed
        (DTR.stateVariableNames
          twoStateModel.reactiveClass.stateVariables)
        twoStateModel.reactiveClass.messageServer.name
        sourceAfter := by

  exact
    Correctness.translateStoreCore_initialMachineSteps_backward
      twoStateModel_wellFormed
      (LF.StoreMachineSteps.refl
        _)

theorem twoState_public_translation_initial_refl_backward :
    ∃ sourceLabels sourceAfter,
      DTR.StoreMachineSteps
          (DTR.stateVariableNames
            twoStateModel.reactiveClass.stateVariables)
          twoStateModel.reactiveClass.messageServer.name
          twoStateModel.reactiveClass.messageServer.body
          (DTR.StoreModel.initialState
            twoStateModel)
          sourceLabels
          sourceAfter ∧
      Correctness.StoreMachineTraceCorresponds
        sourceLabels
        [] ∧
      Correctness.StoreStateCorresponds
        sourceAfter
        (LF.StoreProgram.initialState
          (Translation.translateStoreCore
            twoStateModel)) ∧
      DTR.StoreState.RuntimeWellFormed
        (DTR.stateVariableNames
          twoStateModel.reactiveClass.stateVariables)
        twoStateModel.reactiveClass.messageServer.name
        sourceAfter := by

  exact
    Correctness.translateStore_initialMachineSteps_backward
      twoStateModel_wellFormed
      (program :=
        Translation.translateStoreCore
          twoStateModel)
      (by rfl)
      (LF.StoreMachineSteps.refl
        _)

end Tests
end Relico
