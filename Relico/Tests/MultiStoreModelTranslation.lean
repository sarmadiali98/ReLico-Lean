import Relico.Correctness.MultiStoreStructural
import Relico.Tests.StoreModelTranslation
import Relico.Translation.MultiStoreBasic

set_option autoImplicit false

namespace Relico
namespace Tests

def resetMessageName :
    MsgName :=
  ⟨"reset"⟩

def twoMessageConstructor :
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
      { value := 1 },

    DTR.Stmt.selfSend
      resetMessageName
      { value := 2 }
  ]

def tickMessageServer :
    DTR.MessageServer where

  name :=
    twoStateMessageName

  body := [
    DTR.Stmt.assign
      twoStateY
      (.stateVar twoStateX),

    DTR.Stmt.selfSend
      resetMessageName
      { value := 1 }
  ]

def resetMessageServer :
    DTR.MessageServer where

  name :=
    resetMessageName

  body := [
    DTR.Stmt.assign
      twoStateX
      (.intLiteral 0),

    DTR.Stmt.assign
      twoStateY
      (.intLiteral 0)
  ]

def twoMessageServers :
    List DTR.MessageServer := [
  tickMessageServer,
  resetMessageServer
]

def twoMessageReactiveClass :
    DTR.MultiStoreReactiveClass where

  name :=
    twoStateClassName

  stateVariables :=
    twoStateDeclarations

  constructor :=
    twoMessageConstructor

  messageServers :=
    twoMessageServers

def twoMessageModel :
    DTR.MultiStoreModel where

  reactiveClass :=
    twoMessageReactiveClass

  actor :=
    twoStateActor

theorem twoMessage_translation_preserves_declarations :
    (Translation.translateMultiStoreCore
      twoMessageModel).reactor.stateVariables = [
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

theorem twoMessage_translation_preserves_action_order :
    (Translation.translateMultiStoreCore
      twoMessageModel).reactor.logicalActions = [
        Translation.actionNameFor
          twoStateMessageName,

        Translation.actionNameFor
          resetMessageName
      ] := by
  rfl

theorem twoMessage_translation_preserves_reaction_order :
    (Translation.translateMultiStoreCore
      twoMessageModel).reactor.messageReactions = [
        Translation.compileMessageReaction
          tickMessageServer,

        Translation.compileMessageReaction
          resetMessageServer
      ] := by
  rfl

theorem twoMessage_translation_preserves_reaction_bodies :
    List.map
        (fun reaction =>
          reaction.body)
        (Translation.translateMultiStoreCore
          twoMessageModel).reactor.messageReactions = [
      [
        LF.Stmt.assign
          twoStateY
          (.stateVar twoStateX),

        LF.Stmt.schedule
          (Translation.actionNameFor
            resetMessageName)
          { value := 1 }
      ],
      [
        LF.Stmt.assign
          twoStateX
          (.intLiteral 0),

        LF.Stmt.assign
          twoStateY
          (.intLiteral 0)
      ]
    ] := by
  rfl

theorem twoMessage_translation_succeeds :
    ∃ program,
      Translation.translateMultiStore
          twoMessageModel =
        .ok program := by

  exact
    Translation.translateMultiStore_succeeds
      twoMessageModel

theorem existing_store_translation_embeds_exactly :
    Translation.translateMultiStoreCore
        (DTR.StoreModel.toMultiStoreModel
          twoStateModel) =
      LF.StoreProgram.toMultiStoreProgram
        (Translation.translateStoreCore
          twoStateModel) := by

  exact
    Translation.translateMultiStoreCore_singleton
      twoStateModel

end Tests
end Relico

namespace Relico
namespace Tests

theorem twoMessageModel_wellFormed :
    DTR.MultiStoreModel.WellFormed
      twoMessageModel := by

  refine {
    classNameValid := ?_
    actorNameValid := ?_
    stateVariableNamesValid := ?_
    stateVariableNamesUnique := ?_
    messageServersNonempty := ?_
    messageServerNamesValid := ?_
    messageServerNamesUnique := ?_
    actorClassMatches := ?_
    constructorBodyWellFormed := ?_
    messageServerBodiesWellFormed := ?_
  }

  · simp [
      twoMessageModel,
      twoMessageReactiveClass,
      twoStateClassName,
      ClassName.isValid
    ]

  · simp [
      twoMessageModel,
      twoStateActor,
      twoStateActorName,
      ActorName.isValid
    ]

  · intro declaration hDeclaration

    simp [
      twoMessageModel,
      twoMessageReactiveClass,
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
      twoMessageModel,
      twoMessageReactiveClass,
      twoStateDeclarations,
      DTR.stateVariableNames,
      twoStateX,
      twoStateY
    ]

  · simp [
      twoMessageModel,
      twoMessageReactiveClass,
      twoMessageServers
    ]

  · intro messageServer hMessageServer

    simp [
      twoMessageModel,
      twoMessageReactiveClass,
      twoMessageServers
    ] at hMessageServer

    rcases hMessageServer with
      rfl | rfl <;>
      simp [
        tickMessageServer,
        resetMessageServer,
        twoStateMessageName,
        resetMessageName,
        MsgName.isValid
      ]

  · simp [
      twoMessageModel,
      twoMessageReactiveClass,
      twoMessageServers,
      DTR.messageServerNames,
      tickMessageServer,
      resetMessageServer,
      twoStateMessageName,
      resetMessageName
    ]

  · rfl

  · simp [
      twoMessageModel,
      twoMessageReactiveClass,
      twoStateDeclarations,
      twoMessageServers,
      twoMessageConstructor,
      tickMessageServer,
      resetMessageServer,
      DTR.stateVariableNames,
      DTR.messageServerNames,
      DTR.Body.MultiStoreWellFormed,
      DTR.Stmt.MultiStoreWellFormed,
      DTR.Expr.StoreWellFormed
    ]

  · intro messageServer hMessageServer

    simp [
      twoMessageModel,
      twoMessageReactiveClass,
      twoMessageServers
    ] at hMessageServer

    rcases hMessageServer with
      rfl | rfl <;>
      simp [
        twoMessageModel,
        twoMessageReactiveClass,
        twoStateDeclarations,
        twoMessageServers,
        tickMessageServer,
        resetMessageServer,
        DTR.stateVariableNames,
        DTR.messageServerNames,
        DTR.Body.MultiStoreWellFormed,
        DTR.Stmt.MultiStoreWellFormed,
        DTR.Expr.StoreWellFormed
      ]

theorem twoMessage_translated_program_wellFormed :
    LF.MultiStoreProgram.WellFormed
      (Translation.translateMultiStoreCore
        twoMessageModel) := by

  exact
    Correctness.translateMultiStoreCore_wellFormed
      twoMessageModel_wellFormed

theorem twoMessage_public_translation_wellFormed :
    LF.MultiStoreProgram.WellFormed
      (Translation.translateMultiStoreCore
        twoMessageModel) := by

  exact
    Correctness.translateMultiStore_wellFormed
      twoMessageModel_wellFormed
      (by rfl)

theorem existing_store_model_wellFormed_embedding :
    DTR.MultiStoreModel.WellFormed
      (DTR.StoreModel.toMultiStoreModel
        twoStateModel) := by

  exact
    DTR.StoreModel.wellFormed_toMultiStoreModel
      twoStateModel_wellFormed

theorem existing_store_program_wellFormed_embedding :
    LF.MultiStoreProgram.WellFormed
      (LF.StoreProgram.toMultiStoreProgram
        (Translation.translateStoreCore
          twoStateModel)) := by

  exact
    LF.StoreProgram.wellFormed_toMultiStoreProgram
      (Correctness.translateStoreCore_wellFormed
        twoStateModel_wellFormed)

end Tests
end Relico
