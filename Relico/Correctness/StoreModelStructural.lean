import Relico.Correctness.StoreStructural
import Relico.DTR.StoreModelWellFormed
import Relico.LF.StoreModelWellFormed
import Relico.Translation.StoreBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compilation preserves structural validity of a finite-store reactor.
-/
theorem compileStoreReactor_wellFormed
    {reactiveClass : DTR.StoreReactiveClass}
    (hClassName :
      ClassName.isValid
        reactiveClass.name)
    (hStateVariableNames :
      ∀ declaration,
        declaration ∈
          reactiveClass.stateVariables →
        VarName.isValid
          declaration.name)
    (hStateVariableNamesUnique :
      (DTR.stateVariableNames
        reactiveClass.stateVariables).Nodup)
    (hConstructorBody :
      DTR.Body.StoreWellFormed
        (DTR.stateVariableNames
          reactiveClass.stateVariables)
        reactiveClass.messageServer.name
        reactiveClass.constructor.body)
    (hMessageBody :
      DTR.Body.StoreWellFormed
        (DTR.stateVariableNames
          reactiveClass.stateVariables)
        reactiveClass.messageServer.name
        reactiveClass.messageServer.body) :
    LF.StoreReactor.WellFormed
      (Translation.compileStoreReactor
        reactiveClass) := by

  refine {
    reactorNameValid := ?_
    stateVariableNamesValid := ?_
    stateVariableNamesUnique := ?_
    actionNameValid := ?_
    startupReactionNameValid := ?_
    startupTriggerCorrect := ?_
    startupBodyWellFormed := ?_
    messageReactionNameValid := ?_
    messageTriggerCorrect := ?_
    messageBodyWellFormed := ?_
  }

  · simpa [
      Translation.compileStoreReactor,
      Translation.reactorNameFor,
      ReactorName.isValid,
      ClassName.isValid
    ] using
      hClassName

  · intro targetDeclaration hTargetDeclaration

    change
      targetDeclaration ∈
        Translation.compileStateVariableDecls
          reactiveClass.stateVariables
      at hTargetDeclaration

    simp only [
      Translation.compileStateVariableDecls,
      List.mem_map
    ] at hTargetDeclaration

    rcases hTargetDeclaration with
      ⟨sourceDeclaration,
       hSourceDeclaration,
       rfl⟩

    simpa [
      Translation.compileStateVariableDecl
    ] using
      hStateVariableNames
        sourceDeclaration
        hSourceDeclaration

  · simpa [
      Translation.compileStoreReactor
    ] using
      hStateVariableNamesUnique

  · simp [
      Translation.compileStoreReactor,
      Translation.actionNameFor,
      ActionName.isValid
    ]

  · simp [
      Translation.compileStoreReactor,
      Translation.compileStartupReaction,
      Translation.startupReactionName,
      ReactionName.isValid
    ]

  · rfl

  · simpa [
      Translation.compileStoreReactor,
      Translation.compileStartupReaction
    ] using
      compileBody_storeWellFormed
        hConstructorBody

  · simp [
      Translation.compileStoreReactor,
      Translation.compileMessageReaction,
      Translation.messageReactionNameFor,
      ReactionName.isValid
    ]

  · rfl

  · simpa [
      Translation.compileStoreReactor,
      Translation.compileMessageReaction
    ] using
      compileBody_storeWellFormed
        hMessageBody

/--
The executable finite-store compiler core preserves complete program
structural validity.
-/
theorem translateStoreCore_wellFormed
    {model : DTR.StoreModel}
    (hModel :
      DTR.StoreModel.WellFormed
        model) :
    LF.StoreProgram.WellFormed
      (Translation.translateStoreCore
        model) := by

  refine {
    reactorWellFormed := ?_
    instanceNameValid := ?_
    instanceReactorMatches := ?_
  }

  · exact
      compileStoreReactor_wellFormed
        hModel.classNameValid
        hModel.stateVariableNamesValid
        hModel.stateVariableNamesUnique
        hModel.constructorBodyWellFormed
        hModel.messageServerBodyWellFormed

  · simpa [
      Translation.translateStoreCore,
      Translation.compileReactorInstance
    ] using
      hModel.actorNameValid

  · simpa [
      Translation.translateStoreCore,
      Translation.compileStoreReactor,
      Translation.compileReactorInstance
    ] using
      congrArg
        Translation.reactorNameFor
        hModel.actorClassMatches

/--
Structural correctness of the public executable finite-store
translator.
-/
theorem translateStore_wellFormed
    {model : DTR.StoreModel}
    {program : LF.StoreProgram}
    (hModel :
      DTR.StoreModel.WellFormed
        model)
    (hTranslate :
      Translation.translateStore model =
        .ok program) :
    LF.StoreProgram.WellFormed
      program := by

  simp [
    Translation.translateStore
  ] at hTranslate

  subst program

  exact
    translateStoreCore_wellFormed
      hModel

end Correctness
end Relico
