import Relico.DTR.Syntax

set_option autoImplicit false

namespace Relico
namespace DTR

namespace Expr

/--
An expression is well formed when every state-variable reference
refers to the variable declared by the reactive class.
-/
def WellFormed
    (declaredStateVar : VarName) :
    Expr → Prop
  | .intLiteral _ =>
      True
  | .stateVar referencedStateVar =>
      referencedStateVar = declaredStateVar

@[simp]
theorem wellFormed_intLiteral
    (declaredStateVar : VarName)
    (value : Int) :
    WellFormed declaredStateVar (.intLiteral value) := by
  trivial

@[simp]
theorem wellFormed_stateVar
    (declaredStateVar referencedStateVar : VarName) :
    WellFormed declaredStateVar (.stateVar referencedStateVar) ↔
      referencedStateVar = declaredStateVar := by
  rfl

end Expr

namespace Stmt

/--
A statement is well formed when:

- an assignment targets the declared state variable and its expression
  is well formed;
- a self-send targets the declared message server.
-/
def WellFormed
    (declaredStateVar : VarName)
    (declaredMessageServer : MsgName) :
    Stmt → Prop
  | .assign target expression =>
      target = declaredStateVar ∧
      expression.WellFormed declaredStateVar
  | .selfSend target _ =>
      target = declaredMessageServer

@[simp]
theorem wellFormed_assign
    (declaredStateVar target : VarName)
    (declaredMessageServer : MsgName)
    (expression : Expr) :
    WellFormed
        declaredStateVar
        declaredMessageServer
        (.assign target expression) ↔
      target = declaredStateVar ∧
      expression.WellFormed declaredStateVar := by
  rfl

@[simp]
theorem wellFormed_selfSend
    (declaredStateVar : VarName)
    (declaredMessageServer target : MsgName)
    (delay : Delay) :
    WellFormed
        declaredStateVar
        declaredMessageServer
        (.selfSend target delay) ↔
      target = declaredMessageServer := by
  rfl

end Stmt

namespace Body

/--
Every statement in a constructor or message-server body must be
well formed relative to the declarations of its reactive class.
-/
def WellFormed
    (declaredStateVar : VarName)
    (declaredMessageServer : MsgName)
    (body : Body) : Prop :=
  ∀ statement ∈ body,
    statement.WellFormed
      declaredStateVar
      declaredMessageServer

@[simp]
theorem wellFormed_nil
    (declaredStateVar : VarName)
    (declaredMessageServer : MsgName) :
    WellFormed declaredStateVar declaredMessageServer [] := by
  intro statement membership
  cases membership

@[simp]
theorem wellFormed_cons
    (declaredStateVar : VarName)
    (declaredMessageServer : MsgName)
    (statement : Stmt)
    (remaining : Body) :
    WellFormed
        declaredStateVar
        declaredMessageServer
        (statement :: remaining) ↔
      statement.WellFormed
          declaredStateVar
          declaredMessageServer ∧
      WellFormed
          declaredStateVar
          declaredMessageServer
          remaining := by
  constructor
  · intro h
    constructor
    · exact h statement (by simp)
    · intro next membership
      exact h next (by simp [membership])
  · intro h next membership
    rcases h with ⟨headWellFormed, tailWellFormed⟩
    simp only [List.mem_cons] at membership
    rcases membership with rfl | membership
    · exact headWellFormed
    · exact tailWellFormed next membership

end Body

namespace Model

/--
A DTR model in vertical slice v0 is well formed when all names are
nonempty, the actor instantiates the declared class, and both executable
bodies refer only to the declarations provided by that class.
-/
structure WellFormed
    (model : DTR.Model) : Prop where
  classNameValid :
    ClassName.isValid model.reactiveClass.name

  actorNameValid :
    ActorName.isValid model.actor.name

  stateVarNameValid :
    VarName.isValid model.reactiveClass.stateVar

  messageServerNameValid :
    MsgName.isValid model.reactiveClass.messageServer.name

  actorClassMatches :
    model.actor.className =
      model.reactiveClass.name

  constructorBodyWellFormed :
    model.reactiveClass.constructor.body.WellFormed
      model.reactiveClass.stateVar
      model.reactiveClass.messageServer.name

  messageServerBodyWellFormed :
    model.reactiveClass.messageServer.body.WellFormed
      model.reactiveClass.stateVar
      model.reactiveClass.messageServer.name

end Model

end DTR
end Relico
