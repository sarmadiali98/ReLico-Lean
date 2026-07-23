import Relico.Common.StateStoreCoverage
import Relico.DTR.StoreEvaluation
import Relico.DTR.WellFormed

set_option autoImplicit false

namespace Relico
namespace DTR

namespace Expr

/--
An expression is well formed for a declaration list when every
state-variable reference occurs in that list.
-/
def StoreWellFormed
    (declaredVariables : List VarName) :
    DTR.Expr →
    Prop

  | .intLiteral _ =>
      True

  | .stateVar referencedVariable =>
      referencedVariable ∈ declaredVariables

@[simp]
theorem storeWellFormed_intLiteral
    (declaredVariables : List VarName)
    (value : Int) :
    StoreWellFormed
      declaredVariables
      (.intLiteral value) := by
  trivial

@[simp]
theorem storeWellFormed_stateVar
    (declaredVariables : List VarName)
    (referencedVariable : VarName) :
    StoreWellFormed
        declaredVariables
        (.stateVar referencedVariable) ↔
      referencedVariable ∈ declaredVariables := by
  rfl

/--
A well-formed expression evaluates successfully in every store that
covers its declaration list.
-/
theorem evaluateStore_defined
    {declaredVariables : List VarName}
    {store : StateStore}
    {expression : DTR.Expr}
    (hExpression :
      StoreWellFormed
        declaredVariables
        expression)
    (hCoverage :
      StateStore.Covers
        declaredVariables
        store) :
    ∃ value,
      evaluateStore
          store
          expression =
        some value := by

  cases expression with

  | intLiteral value =>
      exact
        ⟨value, rfl⟩

  | stateVar referencedVariable =>
      exact
        hCoverage
          referencedVariable
          hExpression

/--
The declaration-list predicate specializes to the original v0
expression predicate on a singleton declaration list.
-/
theorem storeWellFormed_singleton_iff
    (declaredVariable : VarName)
    (expression : DTR.Expr) :
    StoreWellFormed
        [declaredVariable]
        expression ↔
      DTR.Expr.WellFormed
        declaredVariable
        expression := by

  cases expression <;>
    simp [
      StoreWellFormed,
      DTR.Expr.WellFormed
    ]

end Expr

namespace Stmt

/--
A statement is well formed for multiple declarations when:

- an assignment target is declared;
- its expression references only declared variables;
- a self-send targets the declared message server.
-/
def StoreWellFormed
    (declaredVariables : List VarName)
    (declaredMessageServer : MsgName) :
    DTR.Stmt →
    Prop

  | .assign target expression =>
      target ∈ declaredVariables ∧
      DTR.Expr.StoreWellFormed
        declaredVariables
        expression

  | .selfSend targetMessage _ =>
      targetMessage =
        declaredMessageServer

@[simp]
theorem storeWellFormed_assign
    (declaredVariables : List VarName)
    (declaredMessageServer : MsgName)
    (target : VarName)
    (expression : DTR.Expr) :
    StoreWellFormed
        declaredVariables
        declaredMessageServer
        (.assign target expression) ↔
      target ∈ declaredVariables ∧
      DTR.Expr.StoreWellFormed
        declaredVariables
        expression := by
  rfl

@[simp]
theorem storeWellFormed_selfSend
    (declaredVariables : List VarName)
    (declaredMessageServer targetMessage : MsgName)
    (delay : Delay) :
    StoreWellFormed
        declaredVariables
        declaredMessageServer
        (.selfSend targetMessage delay) ↔
      targetMessage =
        declaredMessageServer := by
  rfl

/--
The declaration-list predicate specializes to the original v0
statement predicate on a singleton declaration list.
-/
theorem storeWellFormed_singleton_iff
    (declaredVariable : VarName)
    (declaredMessageServer : MsgName)
    (statement : DTR.Stmt) :
    StoreWellFormed
        [declaredVariable]
        declaredMessageServer
        statement ↔
      DTR.Stmt.WellFormed
        declaredVariable
        declaredMessageServer
        statement := by

  cases statement <;>
    simp [
      StoreWellFormed,
      DTR.Stmt.WellFormed,
      DTR.Expr.storeWellFormed_singleton_iff
    ]

end Stmt

namespace Body

/--
Every statement in a body must be well formed for the complete
state-variable declaration list and the declared message server.
-/
def StoreWellFormed
    (declaredVariables : List VarName)
    (declaredMessageServer : MsgName)
    (body : DTR.Body) :
    Prop :=
  ∀ statement,
    statement ∈ body →
    DTR.Stmt.StoreWellFormed
      declaredVariables
      declaredMessageServer
      statement

@[simp]
theorem storeWellFormed_nil
    (declaredVariables : List VarName)
    (declaredMessageServer : MsgName) :
    StoreWellFormed
      declaredVariables
      declaredMessageServer
      [] := by

  intro statement hMember
  cases hMember

@[simp]
theorem storeWellFormed_cons
    (declaredVariables : List VarName)
    (declaredMessageServer : MsgName)
    (statement : DTR.Stmt)
    (remaining : DTR.Body) :
    StoreWellFormed
        declaredVariables
        declaredMessageServer
        (statement :: remaining) ↔
      DTR.Stmt.StoreWellFormed
          declaredVariables
          declaredMessageServer
          statement ∧
        StoreWellFormed
          declaredVariables
          declaredMessageServer
          remaining := by

  constructor

  · intro hBody

    constructor

    · exact
        hBody
          statement
          (by simp)

    · intro nextStatement hMember

      exact
        hBody
          nextStatement
          (by simp [hMember])

  · intro hParts
    rcases hParts with
      ⟨hHead, hTail⟩

    intro nextStatement hMember

    simp only [List.mem_cons] at hMember

    rcases hMember with
      rfl | hRemaining

    · exact hHead

    · exact
        hTail
          nextStatement
          hRemaining

/--
The declaration-list predicate specializes to the original v0 body
predicate on a singleton declaration list.
-/
theorem storeWellFormed_singleton_iff
    (declaredVariable : VarName)
    (declaredMessageServer : MsgName)
    (body : DTR.Body) :
    StoreWellFormed
        [declaredVariable]
        declaredMessageServer
        body ↔
      DTR.Body.WellFormed
        declaredVariable
        declaredMessageServer
        body := by

  constructor

  · intro hBody statement hMember

    exact
      (DTR.Stmt.storeWellFormed_singleton_iff
        declaredVariable
        declaredMessageServer
        statement).mp
        (hBody
          statement
          hMember)

  · intro hBody statement hMember

    exact
      (DTR.Stmt.storeWellFormed_singleton_iff
        declaredVariable
        declaredMessageServer
        statement).mpr
        (hBody
          statement
          hMember)

end Body
end DTR
end Relico
