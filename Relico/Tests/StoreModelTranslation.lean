import Relico.Correctness.StoreModelStructural

set_option autoImplicit false

namespace Relico
namespace Tests

def twoStateX :
    VarName :=
  ⟨"x"⟩

def twoStateY :
    VarName :=
  ⟨"y"⟩

def twoStateClassName :
    ClassName :=
  ⟨"TwoStateController"⟩

def twoStateActorName :
    ActorName :=
  ⟨"controller"⟩

def twoStateMessageName :
    MsgName :=
  ⟨"tick"⟩

def twoStateDeclarations :
    List DTR.StateVariableDecl := [
  {
    name :=
      twoStateX

    initialValue :=
      1
  },
  {
    name :=
      twoStateY

    initialValue :=
      2
  }
]

def twoStateConstructor :
    DTR.Constructor where

  body := [
    DTR.Stmt.assign
      twoStateX
      (.intLiteral 1),

    DTR.Stmt.assign
      twoStateY
      (.intLiteral 2),

    DTR.Stmt.selfSend
      twoStateMessageName
      { value := 1 }
  ]

def twoStateMessageServer :
    DTR.MessageServer where

  name :=
    twoStateMessageName

  body := [
    DTR.Stmt.assign
      twoStateY
      (.stateVar twoStateX),

    DTR.Stmt.selfSend
      twoStateMessageName
      { value := 1 }
  ]

def twoStateReactiveClass :
    DTR.StoreReactiveClass where

  name :=
    twoStateClassName

  stateVariables :=
    twoStateDeclarations

  constructor :=
    twoStateConstructor

  messageServer :=
    twoStateMessageServer

def twoStateActor :
    DTR.ActorInstance where

  name :=
    twoStateActorName

  className :=
    twoStateClassName

def twoStateModel :
    DTR.StoreModel where

  reactiveClass :=
    twoStateReactiveClass

  actor :=
    twoStateActor

theorem twoStateModel_wellFormed :
    DTR.StoreModel.WellFormed
      twoStateModel := by

  refine {
    classNameValid := ?_
    actorNameValid := ?_
    stateVariableNamesValid := ?_
    stateVariableNamesUnique := ?_
    messageServerNameValid := ?_
    actorClassMatches := ?_
    constructorBodyWellFormed := ?_
    messageServerBodyWellFormed := ?_
  }

  · simp [
      twoStateModel,
      twoStateReactiveClass,
      twoStateClassName,
      ClassName.isValid
    ]

  · simp [
      twoStateModel,
      twoStateActor,
      twoStateActorName,
      ActorName.isValid
    ]

  · intro declaration hDeclaration

    simp [
      twoStateModel,
      twoStateReactiveClass,
      twoStateDeclarations
    ] at hDeclaration

    rcases hDeclaration with
      rfl | rfl <;>
      simp [
        twoStateX,
        twoStateY,
        VarName.isValid
      ]

  · simp [
      twoStateModel,
      twoStateReactiveClass,
      twoStateDeclarations,
      DTR.stateVariableNames,
      twoStateX,
      twoStateY
    ]

  · simp [
      twoStateModel,
      twoStateReactiveClass,
      twoStateMessageServer,
      twoStateMessageName,
      MsgName.isValid
    ]

  · rfl

  · simp [
      twoStateModel,
      twoStateReactiveClass,
      twoStateDeclarations,
      twoStateConstructor,
      twoStateMessageServer,
      DTR.stateVariableNames,
      DTR.Body.StoreWellFormed,
      DTR.Stmt.StoreWellFormed,
      DTR.Expr.StoreWellFormed
    ]

  · simp [
      twoStateModel,
      twoStateReactiveClass,
      twoStateDeclarations,
      twoStateMessageServer,
      DTR.stateVariableNames,
      DTR.Body.StoreWellFormed,
      DTR.Stmt.StoreWellFormed,
      DTR.Expr.StoreWellFormed
    ]

/--
The executable translator preserves both state declarations, their
order, and their initial values.
-/
theorem twoState_translation_preserves_declarations :
    (Translation.translateStoreCore
      twoStateModel).reactor.stateVariables = [
        {
          name :=
            twoStateX

          initialValue :=
            1
        },
        {
          name :=
            twoStateY

          initialValue :=
            2
        }
      ] := by
  rfl

/--
The cross-variable message-server assignment is present in the
generated LF reaction body.
-/
theorem twoState_translation_preserves_cross_variable_assignment :
    (Translation.translateStoreCore
      twoStateModel).reactor.messageReaction.body = [
        LF.Stmt.assign
          twoStateY
          (.stateVar twoStateX),

        LF.Stmt.schedule
          (Translation.actionNameFor
            twoStateMessageName)
          { value := 1 }
      ] := by
  rfl

theorem twoState_translation_succeeds :
    ∃ program,
      Translation.translateStore
          twoStateModel =
        .ok program := by
  exact
    Translation.translateStore_succeeds
      twoStateModel

theorem twoState_translated_program_wellFormed :
    LF.StoreProgram.WellFormed
      (Translation.translateStoreCore
        twoStateModel) := by
  exact
    Correctness.translateStoreCore_wellFormed
      twoStateModel_wellFormed

/--
The new translation remains an exact conservative extension of the
existing singleton-state translator.
-/
example
    (model : DTR.Model)
    (initialValue : Int) :
    Translation.translateStoreCore
        (DTR.Model.toStoreModel
          model
          initialValue) =
      LF.Program.toStoreProgram
        (Translation.translateCore model)
        initialValue := by

  exact
    Translation.translateStoreCore_singleton
      model
      initialValue

end Tests
end Relico
