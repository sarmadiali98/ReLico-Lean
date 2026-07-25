import Relico.Correctness.StoreForward
import Relico.DTR.StoreInitialization
import Relico.LF.StoreInitialization
import Relico.Translation.StoreBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compilation preserves the complete declaration-initialized finite
store.
-/
theorem compileStateVariableDecls_initialStore
    (declarations : List DTR.StateVariableDecl) :
    LF.initialStore
        (Translation.compileStateVariableDecls
          declarations) =
      DTR.initialStore
        declarations := by

  induction declarations with

  | nil =>
      rfl

  | cons declaration remaining inductionHypothesis =>
      simp [
        LF.initialStore,
        DTR.initialStore,
        Translation.compileStateVariableDecls,
        Translation.compileStateVariableDecl
      ]

/--
The generated program and source model begin with the same complete
finite store.
-/
theorem translateStoreCore_initialState_store
    (model : DTR.StoreModel) :
    (LF.StoreProgram.initialState
      (Translation.translateStoreCore
        model)).stateStore =
      (DTR.StoreModel.initialState
        model).stateStore := by

  simpa [
    LF.StoreProgram.initialState,
    DTR.StoreModel.initialState,
    Translation.translateStoreCore,
    Translation.compileStoreReactor
  ] using
    compileStateVariableDecls_initialStore
      model.reactiveClass.stateVariables

/--
The generated startup body is the compiled source constructor body.
-/
theorem translateStoreCore_initialState_body
    (model : DTR.StoreModel) :
    (LF.StoreProgram.initialState
      (Translation.translateStoreCore
        model)).activeBody =
      Translation.compileBody
        (DTR.StoreModel.initialState
          model).activeBody := by
  rfl

/--
Constructor entry and generated startup entry correspond for every
finite-store source model.

This theorem connects the executable generalized translator directly
to the generalized runtime-state relation.
-/
theorem translateStoreCore_initialStates_correspond
    (model : DTR.StoreModel) :
    StoreStateCorresponds
      (DTR.StoreModel.initialState
        model)
      (LF.StoreProgram.initialState
        (Translation.translateStoreCore
          model)) := by

  refine {
    currentTime := ?_
    stateStore := ?_
    pendingEvents := ?_
    activeBody := ?_
  }

  · rfl

  · exact
      translateStoreCore_initialState_store
        model

  · exact
      QueueCorresponds.nil

  · exact
      translateStoreCore_initialState_body
        model

/--
Initial-state correspondence for the program returned by the public
executable finite-store translator.
-/
theorem translateStore_initialStates_correspond
    {model : DTR.StoreModel}
    {program : LF.StoreProgram}
    (hTranslate :
      Translation.translateStore model =
        .ok program) :
    StoreStateCorresponds
      (DTR.StoreModel.initialState
        model)
      (LF.StoreProgram.initialState
        program) := by

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
    translateStoreCore_initialStates_correspond
      model

end Correctness
end Relico
