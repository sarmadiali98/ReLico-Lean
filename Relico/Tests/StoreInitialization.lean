import Relico.Correctness.StoreInitialization
import Relico.Tests.StoreModelTranslation

set_option autoImplicit false

namespace Relico
namespace Tests

def expectedTwoStateInitialStore :
    StateStore := [
  (twoStateX, 1),
  (twoStateY, 2)
]

theorem twoState_dtr_initial_store :
    DTR.initialStore
        twoStateDeclarations =
      expectedTwoStateInitialStore := by
  rfl

theorem twoState_lf_initial_store :
    LF.initialStore
        (Translation.translateStoreCore
          twoStateModel).reactor.stateVariables =
      expectedTwoStateInitialStore := by
  rfl

theorem twoState_initial_store_covers_declarations :
    StateStore.Covers
      (DTR.stateVariableNames
        twoStateDeclarations)
      expectedTwoStateInitialStore := by

  simpa [
    twoState_dtr_initial_store
  ] using
    DTR.initialStore_covers
      twoStateDeclarations

theorem twoState_dtr_initial_state :
    DTR.StoreModel.initialState
        twoStateModel = {
      currentTime :=
        0

      stateStore :=
        expectedTwoStateInitialStore

      pendingMessages :=
        []

      activeBody :=
        twoStateConstructor.body
    } := by
  rfl

theorem twoState_lf_initial_state :
    LF.StoreProgram.initialState
        (Translation.translateStoreCore
          twoStateModel) = {
      currentTag :=
        LF.initialTag

      stateStore :=
        expectedTwoStateInitialStore

      pendingActions :=
        []

      activeBody :=
        Translation.compileBody
          twoStateConstructor.body
    } := by
  rfl

theorem twoState_initial_store_preserved :
    (LF.StoreProgram.initialState
      (Translation.translateStoreCore
        twoStateModel)).stateStore =
      (DTR.StoreModel.initialState
        twoStateModel).stateStore := by

  exact
    Correctness.translateStoreCore_initialState_store
      twoStateModel

theorem twoState_constructor_startup_body_preserved :
    (LF.StoreProgram.initialState
      (Translation.translateStoreCore
        twoStateModel)).activeBody =
      Translation.compileBody
        (DTR.StoreModel.initialState
          twoStateModel).activeBody := by

  exact
    Correctness.translateStoreCore_initialState_body
      twoStateModel

theorem twoState_initial_source_runtimeWellFormed :
    DTR.StoreState.RuntimeWellFormed
      (DTR.stateVariableNames
        twoStateModel.reactiveClass.stateVariables)
      twoStateModel.reactiveClass.messageServer.name
      (DTR.StoreModel.initialState
        twoStateModel) := by

  exact
    DTR.StoreModel.initialState_runtimeWellFormed
      twoStateModel
      twoStateModel_wellFormed

theorem twoState_initial_states_correspond :
    Correctness.StoreStateCorresponds
      (DTR.StoreModel.initialState
        twoStateModel)
      (LF.StoreProgram.initialState
        (Translation.translateStoreCore
          twoStateModel)) := by

  exact
    Correctness.translateStoreCore_initialStates_correspond
      twoStateModel

theorem twoState_public_translation_initial_states_correspond :
    Correctness.StoreStateCorresponds
      (DTR.StoreModel.initialState
        twoStateModel)
      (LF.StoreProgram.initialState
        (Translation.translateStoreCore
          twoStateModel)) := by

  apply
    Correctness.translateStore_initialStates_correspond

  rfl

end Tests
end Relico
