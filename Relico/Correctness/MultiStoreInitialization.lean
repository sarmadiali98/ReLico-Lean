import Relico.Correctness.StoreInitialization
import Relico.DTR.MultiStoreInitialization
import Relico.LF.MultiStoreInitialization
import Relico.Translation.MultiStoreBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
The generated and source multi-server models begin with the same
complete declaration-derived finite store.
-/
theorem translateMultiStoreCore_initialState_store
    (model : DTR.MultiStoreModel) :
    (LF.MultiStoreProgram.initialState
      (Translation.translateMultiStoreCore
        model)).stateStore =
      (DTR.MultiStoreModel.initialState
        model).stateStore := by

  simpa [
    LF.MultiStoreProgram.initialState,
    DTR.MultiStoreModel.initialState,
    Translation.translateMultiStoreCore,
    Translation.compileMultiStoreReactor
  ] using
    compileStateVariableDecls_initialStore
      model.reactiveClass.stateVariables

/--
The generated startup reaction contains exactly the compiled source
constructor body.
-/
theorem translateMultiStoreCore_initialState_body
    (model : DTR.MultiStoreModel) :
    (LF.MultiStoreProgram.initialState
      (Translation.translateMultiStoreCore
        model)).activeBody =
      Translation.compileBody
        (DTR.MultiStoreModel.initialState
          model).activeBody := by
  rfl

/--
Constructor entry and generated startup entry correspond for every
finite-store, multiple-message-server source model.
-/
theorem translateMultiStoreCore_initialStates_correspond
    (model : DTR.MultiStoreModel) :
    StoreStateCorresponds
      (DTR.MultiStoreModel.initialState
        model)
      (LF.MultiStoreProgram.initialState
        (Translation.translateMultiStoreCore
          model)) := by

  refine {
    currentTime := ?_
    stateStore := ?_
    pendingEvents := ?_
    activeBody := ?_
  }

  · rfl

  · exact
      translateMultiStoreCore_initialState_store
        model

  · exact
      QueueCorresponds.nil

  · exact
      translateMultiStoreCore_initialState_body
        model

/--
Initial-state correspondence for the program returned by the public
executable multi-server translator.
-/
theorem translateMultiStore_initialStates_correspond
    {model : DTR.MultiStoreModel}
    {program : LF.MultiStoreProgram}
    (hTranslate :
      Translation.translateMultiStore model =
        .ok program) :
    StoreStateCorresponds
      (DTR.MultiStoreModel.initialState
        model)
      (LF.MultiStoreProgram.initialState
        program) := by

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
    translateMultiStoreCore_initialStates_correspond
      model

end Correctness
end Relico
