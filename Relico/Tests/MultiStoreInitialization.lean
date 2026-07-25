import Relico.Correctness.MultiStoreInitialization
import Relico.Tests.MultiStoreModelTranslation
import Relico.Tests.StoreInitialization

set_option autoImplicit false

namespace Relico
namespace Tests

theorem twoMessage_dtr_initial_store :
    (DTR.MultiStoreModel.initialState
      twoMessageModel).stateStore =
      expectedTwoStateInitialStore := by
  rfl

theorem twoMessage_lf_initial_store :
    (LF.MultiStoreProgram.initialState
      (Translation.translateMultiStoreCore
        twoMessageModel)).stateStore =
      expectedTwoStateInitialStore := by
  rfl

theorem twoMessage_dtr_initial_state :
    DTR.MultiStoreModel.initialState
        twoMessageModel = {
      currentTime :=
        0

      stateStore :=
        expectedTwoStateInitialStore

      pendingMessages :=
        []

      activeBody :=
        twoMessageConstructor.body
    } := by
  rfl

theorem twoMessage_lf_initial_state :
    LF.MultiStoreProgram.initialState
        (Translation.translateMultiStoreCore
          twoMessageModel) = {
      currentTag :=
        LF.initialTag

      stateStore :=
        expectedTwoStateInitialStore

      pendingActions :=
        []

      activeBody :=
        Translation.compileBody
          twoMessageConstructor.body
    } := by
  rfl

theorem twoMessage_initial_source_runtimeWellFormed :
    DTR.StoreState.MultiStoreRuntimeWellFormed
      (DTR.stateVariableNames
        twoMessageModel.reactiveClass.stateVariables)
      twoMessageModel.reactiveClass.messageServers
      (DTR.MultiStoreModel.initialState
        twoMessageModel) := by

  exact
    DTR.MultiStoreModel.initialState_runtimeWellFormed
      twoMessageModel
      twoMessageModel_wellFormed

theorem twoMessage_initial_states_correspond :
    Correctness.StoreStateCorresponds
      (DTR.MultiStoreModel.initialState
        twoMessageModel)
      (LF.MultiStoreProgram.initialState
        (Translation.translateMultiStoreCore
          twoMessageModel)) := by

  exact
    Correctness.translateMultiStoreCore_initialStates_correspond
      twoMessageModel

theorem twoMessage_public_translation_initial_states_correspond :
    Correctness.StoreStateCorresponds
      (DTR.MultiStoreModel.initialState
        twoMessageModel)
      (LF.MultiStoreProgram.initialState
        (Translation.translateMultiStoreCore
          twoMessageModel)) := by

  apply
    Correctness.translateMultiStore_initialStates_correspond

  rfl

end Tests
end Relico
