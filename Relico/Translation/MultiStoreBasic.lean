import Relico.DTR.MultiStoreSyntax
import Relico.LF.MultiStoreSyntax
import Relico.Translation.StoreBasic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Generate one LF logical-action name for each source message server,
preserving source declaration order.
-/
def compileLogicalActions
    (messageServers : List DTR.MessageServer) :
    List ActionName :=
  messageServers.map
    (fun messageServer =>
      actionNameFor
        messageServer.name)

/--
Generate one LF reaction for each source message server, preserving
source declaration order.
-/
def compileMessageReactions
    (messageServers : List DTR.MessageServer) :
    List LF.Reaction :=
  messageServers.map
    compileMessageReaction

@[simp]
theorem compileLogicalActions_names
    (messageServers : List DTR.MessageServer) :
    compileLogicalActions
        messageServers =
      (DTR.messageServerNames
        messageServers).map
          actionNameFor := by

  induction messageServers with

  | nil =>
      rfl

  | cons messageServer remaining inductionHypothesis =>
      simp [
        compileLogicalActions,
        DTR.messageServerNames
      ]

@[simp]
theorem compileMessageReactions_length
    (messageServers : List DTR.MessageServer) :
    (compileMessageReactions
      messageServers).length =
      messageServers.length := by

  simp [
    compileMessageReactions
  ]

/--
Compile the constructor into the generated startup reaction.

Unlike the earlier finite-store implementation, this definition does
not construct an artificial single-server reactive class.
-/
def compileMultiStoreStartupReaction
    (constructor : DTR.Constructor) :
    LF.Reaction where

  name :=
    startupReactionName

  trigger :=
    .startup

  body :=
    compileBody
      constructor.body

/--
Compile a finite-state, multiple-message-server DTR class into one LF
reactor.
-/
def compileMultiStoreReactor
    (reactiveClass : DTR.MultiStoreReactiveClass) :
    LF.MultiStoreReactor where

  name :=
    reactorNameFor
      reactiveClass.name

  stateVariables :=
    compileStateVariableDecls
      reactiveClass.stateVariables

  logicalActions :=
    compileLogicalActions
      reactiveClass.messageServers

  startupReaction :=
    compileMultiStoreStartupReaction
      reactiveClass.constructor

  messageReactions :=
    compileMessageReactions
      reactiveClass.messageServers

/--
Executable core translation for the one-actor, multiple-message-server
finite-store model.
-/
def translateMultiStoreCore
    (model : DTR.MultiStoreModel) :
    LF.MultiStoreProgram where

  reactor :=
    compileMultiStoreReactor
      model.reactiveClass

  reactorInstance :=
    compileReactorInstance
      model.actor

/--
Public executable translation entry point for multiple-message-server
finite-store models.
-/
def translateMultiStore
    (model : DTR.MultiStoreModel) :
    Except TranslationError LF.MultiStoreProgram :=
  .ok
    (translateMultiStoreCore
      model)

@[simp]
theorem translateMultiStore_eq_ok
    (model : DTR.MultiStoreModel) :
    translateMultiStore model =
      .ok
        (translateMultiStoreCore
          model) := by
  rfl

theorem translateMultiStore_succeeds
    (model : DTR.MultiStoreModel) :
    ∃ program,
      translateMultiStore model =
        .ok program := by

  exact
    ⟨translateMultiStoreCore model,
     rfl⟩

/--
The multi-server translator is an exact conservative extension of the
verified finite-store translator for singleton server lists.
-/
theorem translateMultiStoreCore_singleton
    (model : DTR.StoreModel) :
    translateMultiStoreCore
        (DTR.StoreModel.toMultiStoreModel
          model) =
      LF.StoreProgram.toMultiStoreProgram
        (translateStoreCore
          model) := by
  rfl

end Translation
end Relico
