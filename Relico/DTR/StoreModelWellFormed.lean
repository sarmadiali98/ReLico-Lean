import Relico.DTR.StoreSyntax
import Relico.DTR.StoreWellFormed

set_option autoImplicit false

namespace Relico
namespace DTR
namespace StoreModel

/--
Structural validity of a finite-store DTR model.

State-variable names must be valid and unique. Constructor and
message-server bodies are checked against the entire declaration list.
-/
structure WellFormed
    (model : DTR.StoreModel) :
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

  messageServerNameValid :
    MsgName.isValid
      model.reactiveClass.messageServer.name

  actorClassMatches :
    model.actor.className =
      model.reactiveClass.name

  constructorBodyWellFormed :
    DTR.Body.StoreWellFormed
      (DTR.stateVariableNames
        model.reactiveClass.stateVariables)
      model.reactiveClass.messageServer.name
      model.reactiveClass.constructor.body

  messageServerBodyWellFormed :
    DTR.Body.StoreWellFormed
      (DTR.stateVariableNames
        model.reactiveClass.stateVariables)
      model.reactiveClass.messageServer.name
      model.reactiveClass.messageServer.body

end StoreModel
end DTR
end Relico
