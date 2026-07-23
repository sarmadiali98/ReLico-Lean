import Relico.LF.Syntax

set_option autoImplicit false

namespace Relico
namespace LF

namespace Expr

/--
An LF expression is well formed when every state-variable reference
refers to the state variable declared by the generated reactor.
-/
def WellFormed
    (declaredStateVar : VarName) :
    Expr → Prop
  | .intLiteral _ =>
      True
  | .stateVar referencedStateVar =>
      referencedStateVar = declaredStateVar

end Expr

namespace Stmt

/--
An LF statement is well formed when:

- an assignment targets the reactor's state variable and contains a
  well-formed expression;
- a schedule statement targets the reactor's logical action.
-/
def WellFormed
    (declaredStateVar : VarName)
    (declaredAction : ActionName) :
    Stmt → Prop
  | .assign target expression =>
      target = declaredStateVar ∧
      expression.WellFormed declaredStateVar
  | .schedule target _ =>
      target = declaredAction

end Stmt

namespace Body

/--
Every statement in a generated reaction body must be well formed
relative to the reactor's state variable and logical action.
-/
def WellFormed
    (declaredStateVar : VarName)
    (declaredAction : ActionName)
    (body : Body) : Prop :=
  ∀ statement ∈ body,
    statement.WellFormed
      declaredStateVar
      declaredAction

end Body

namespace Reactor

/--
Structural well-formedness of a reactor in the generated LF subset.
-/
structure WellFormed
    (reactor : LF.Reactor) : Prop where
  reactorNameValid :
    ReactorName.isValid reactor.name

  stateVarNameValid :
    VarName.isValid reactor.stateVar

  actionNameValid :
    ActionName.isValid reactor.logicalAction

  startupReactionNameValid :
    ReactionName.isValid reactor.startupReaction.name

  startupTriggerCorrect :
    reactor.startupReaction.trigger =
      LF.Trigger.startup

  startupBodyWellFormed :
    reactor.startupReaction.body.WellFormed
      reactor.stateVar
      reactor.logicalAction

  messageReactionNameValid :
    ReactionName.isValid reactor.messageReaction.name

  messageTriggerCorrect :
    reactor.messageReaction.trigger =
      LF.Trigger.logicalAction reactor.logicalAction

  messageBodyWellFormed :
    reactor.messageReaction.body.WellFormed
      reactor.stateVar
      reactor.logicalAction

end Reactor

namespace Program

/--
Structural well-formedness of a complete generated LF program.
-/
structure WellFormed
    (program : LF.Program) : Prop where
  reactorWellFormed :
    LF.Reactor.WellFormed program.reactor

  instanceNameValid :
    ActorName.isValid program.reactorInstance.name

  instanceReactorMatches :
    program.reactorInstance.reactorName =
      program.reactor.name

end Program

end LF
end Relico
