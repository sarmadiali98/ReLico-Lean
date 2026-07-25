import Relico.DTR.MultiStoreWellFormed
import Relico.DTR.StoreModelWellFormed

set_option autoImplicit false

namespace Relico
namespace DTR
namespace MultiStoreModel

/--
Structural validity of a one-actor finite-store DTR model with multiple
message servers.
-/
structure WellFormed
    (model : DTR.MultiStoreModel) :
    Prop where

  classNameValid :
    ClassName.isValid
      model.reactiveClass.name

  actorNameValid :
    ActorName.isValid
      model.actor.name

  stateVariableNamesValid :
    ∀ declaration,
      declaration ∈
        model.reactiveClass.stateVariables →
      VarName.isValid
        declaration.name

  stateVariableNamesUnique :
    (DTR.stateVariableNames
      model.reactiveClass.stateVariables).Nodup

  messageServersNonempty :
    model.reactiveClass.messageServers ≠
      []

  messageServerNamesValid :
    ∀ messageServer,
      messageServer ∈
        model.reactiveClass.messageServers →
      MsgName.isValid
        messageServer.name

  messageServerNamesUnique :
    (DTR.messageServerNames
      model.reactiveClass.messageServers).Nodup

  actorClassMatches :
    model.actor.className =
      model.reactiveClass.name

  constructorBodyWellFormed :
    DTR.Body.MultiStoreWellFormed
      (DTR.stateVariableNames
        model.reactiveClass.stateVariables)
      (DTR.messageServerNames
        model.reactiveClass.messageServers)
      model.reactiveClass.constructor.body

  messageServerBodiesWellFormed :
    ∀ messageServer,
      messageServer ∈
        model.reactiveClass.messageServers →
      DTR.Body.MultiStoreWellFormed
        (DTR.stateVariableNames
          model.reactiveClass.stateVariables)
        (DTR.messageServerNames
          model.reactiveClass.messageServers)
        messageServer.body

end MultiStoreModel

namespace StoreModel

/--
Every well-formed one-server finite-store model embeds as a well-formed
multi-server model.
-/
theorem wellFormed_toMultiStoreModel
    {model : DTR.StoreModel}
    (hModel :
      DTR.StoreModel.WellFormed
        model) :
    DTR.MultiStoreModel.WellFormed
      (DTR.StoreModel.toMultiStoreModel
        model) := by

  refine {
    classNameValid :=
      hModel.classNameValid

    actorNameValid :=
      hModel.actorNameValid

    stateVariableNamesValid :=
      hModel.stateVariableNamesValid

    stateVariableNamesUnique :=
      hModel.stateVariableNamesUnique

    messageServersNonempty := ?_

    messageServerNamesValid := ?_

    messageServerNamesUnique := ?_

    actorClassMatches :=
      hModel.actorClassMatches

    constructorBodyWellFormed := ?_

    messageServerBodiesWellFormed := ?_
  }

  · simp [
      DTR.StoreModel.toMultiStoreModel
    ]

  · intro messageServer hMember

    simp [
      DTR.StoreModel.toMultiStoreModel
    ] at hMember

    subst messageServer

    exact
      hModel.messageServerNameValid

  · simp [
      DTR.StoreModel.toMultiStoreModel,
      DTR.messageServerNames
    ]

  · simpa [
      DTR.StoreModel.toMultiStoreModel,
      DTR.messageServerNames,
      DTR.Body.multiStoreWellFormed_singleton_iff
    ] using
      hModel.constructorBodyWellFormed

  · intro messageServer hMember

    simp [
      DTR.StoreModel.toMultiStoreModel
    ] at hMember

    subst messageServer

    simpa [
      DTR.StoreModel.toMultiStoreModel,
      DTR.messageServerNames,
      DTR.Body.multiStoreWellFormed_singleton_iff
    ] using
      hModel.messageServerBodyWellFormed

end StoreModel
end DTR
end Relico
