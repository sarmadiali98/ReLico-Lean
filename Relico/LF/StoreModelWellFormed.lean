import Relico.LF.StoreSyntax
import Relico.LF.StoreWellFormed

set_option autoImplicit false

namespace Relico
namespace LF
namespace StoreReactor

/--
Structural validity of a generated finite-store LF reactor.
-/
structure WellFormed
    (reactor : LF.StoreReactor) :
    Prop where

  reactorNameValid :
    ReactorName.isValid
      reactor.name

  stateVariableNamesValid :
    ∀ declaration,
      declaration ∈
        reactor.stateVariables →
      VarName.isValid
        declaration.name

  stateVariableNamesUnique :
    (LF.stateVariableNames
      reactor.stateVariables).Nodup

  actionNameValid :
    ActionName.isValid
      reactor.logicalAction

  startupReactionNameValid :
    ReactionName.isValid
      reactor.startupReaction.name

  startupTriggerCorrect :
    reactor.startupReaction.trigger =
      LF.Trigger.startup

  startupBodyWellFormed :
    LF.Body.StoreWellFormed
      (LF.stateVariableNames
        reactor.stateVariables)
      reactor.logicalAction
      reactor.startupReaction.body

  messageReactionNameValid :
    ReactionName.isValid
      reactor.messageReaction.name

  messageTriggerCorrect :
    reactor.messageReaction.trigger =
      LF.Trigger.logicalAction
        reactor.logicalAction

  messageBodyWellFormed :
    LF.Body.StoreWellFormed
      (LF.stateVariableNames
        reactor.stateVariables)
      reactor.logicalAction
      reactor.messageReaction.body

end StoreReactor

namespace StoreProgram

/--
Structural validity of a complete generated finite-store LF program.
-/
structure WellFormed
    (program : LF.StoreProgram) :
    Prop where

  reactorWellFormed :
    LF.StoreReactor.WellFormed
      program.reactor

  instanceNameValid :
    ActorName.isValid
      program.reactorInstance.name

  instanceReactorMatches :
    program.reactorInstance.reactorName =
      program.reactor.name

end StoreProgram
end LF
end Relico
