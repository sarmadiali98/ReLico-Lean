import Relico.DTR.StoreSyntax
import Relico.LF.StoreSyntax
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Compile one DTR state-variable declaration into an LF reactor-state
declaration.
-/
def compileStateVariableDecl
    (declaration : DTR.StateVariableDecl) :
    LF.StateVariableDecl where

  name :=
    declaration.name

  initialValue :=
    declaration.initialValue

/--
Compile every state-variable declaration in source order.
-/
def compileStateVariableDecls
    (declarations : List DTR.StateVariableDecl) :
    List LF.StateVariableDecl :=
  declarations.map
    compileStateVariableDecl

@[simp]
theorem compileStateVariableDecl_name
    (declaration : DTR.StateVariableDecl) :
    (compileStateVariableDecl declaration).name =
      declaration.name := by
  rfl

@[simp]
theorem compileStateVariableDecl_initialValue
    (declaration : DTR.StateVariableDecl) :
    (compileStateVariableDecl declaration).initialValue =
      declaration.initialValue := by
  rfl

@[simp]
theorem compileStateVariableDecls_names
    (declarations : List DTR.StateVariableDecl) :
    LF.stateVariableNames
        (compileStateVariableDecls declarations) =
      DTR.stateVariableNames
        declarations := by

  induction declarations with

  | nil =>
      rfl

  | cons declaration remaining inductionHypothesis =>
      simp [
        compileStateVariableDecls,
        DTR.stateVariableNames,
        LF.stateVariableNames
      ]

/--
Compile a finite-store DTR reactive class into a finite-store LF
reactor.
-/
def compileStoreReactor
    (reactiveClass : DTR.StoreReactiveClass) :
    LF.StoreReactor where

  name :=
    reactorNameFor
      reactiveClass.name

  stateVariables :=
    compileStateVariableDecls
      reactiveClass.stateVariables

  logicalAction :=
    actionNameFor
      reactiveClass.messageServer.name

  startupReaction :=
    compileStartupReaction {
      name :=
        reactiveClass.name

      stateVar :=
        match reactiveClass.stateVariables with
        | [] =>
            default
        | declaration :: _ =>
            declaration.name

      constructor :=
        reactiveClass.constructor

      messageServer :=
        reactiveClass.messageServer
    }

  messageReaction :=
    compileMessageReaction
      reactiveClass.messageServer

/--
Executable core translation from a finite-store DTR model to a
finite-store LF program.
-/
def translateStoreCore
    (model : DTR.StoreModel) :
    LF.StoreProgram where

  reactor :=
    compileStoreReactor
      model.reactiveClass

  reactorInstance :=
    compileReactorInstance
      model.actor

/--
Public executable translation entry point for finite-store models.
-/
def translateStore
    (model : DTR.StoreModel) :
    Except TranslationError LF.StoreProgram :=
  .ok
    (translateStoreCore model)

@[simp]
theorem translateStore_eq_ok
    (model : DTR.StoreModel) :
    translateStore model =
      .ok (translateStoreCore model) := by
  rfl

theorem translateStore_succeeds
    (model : DTR.StoreModel) :
    ∃ program,
      translateStore model =
        .ok program := by
  exact
    ⟨translateStoreCore model,
     rfl⟩

/--
The generalized translator agrees exactly with the existing v0
translator on embedded singleton-state models.
-/
theorem translateStoreCore_singleton
    (model : DTR.Model)
    (initialValue : Int) :
    translateStoreCore
        (DTR.Model.toStoreModel
          model
          initialValue) =
      LF.Program.toStoreProgram
        (translateCore model)
        initialValue := by
  rfl

end Translation
end Relico
