import Relico.Common.StateStoreCoverage
import Relico.LF.StoreEvaluation
import Relico.LF.WellFormed

set_option autoImplicit false

namespace Relico
namespace LF

namespace Expr

/--
A generated LF expression is well formed for a declaration list when
every reactor-state reference occurs in that list.
-/
def StoreWellFormed
    (declaredVariables : List VarName) :
    LF.Expr →
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
A well-formed generated LF expression evaluates successfully in every
store covering its declaration list.
-/
theorem evaluateStore_defined
    {declaredVariables : List VarName}
    {store : StateStore}
    {expression : LF.Expr}
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
The declaration-list predicate specializes to the original generated
v0 expression predicate on a singleton declaration list.
-/
theorem storeWellFormed_singleton_iff
    (declaredVariable : VarName)
    (expression : LF.Expr) :
    StoreWellFormed
        [declaredVariable]
        expression ↔
      LF.Expr.WellFormed
        declaredVariable
        expression := by

  cases expression <;>
    simp [
      StoreWellFormed,
      LF.Expr.WellFormed
    ]

end Expr

namespace Stmt

/--
A generated LF statement is well formed for multiple reactor-state
declarations when:

- an assignment target is declared;
- its expression references only declared variables;
- a schedule statement targets the declared logical action.
-/
def StoreWellFormed
    (declaredVariables : List VarName)
    (declaredAction : ActionName) :
    LF.Stmt →
    Prop

  | .assign target expression =>
      target ∈ declaredVariables ∧
      LF.Expr.StoreWellFormed
        declaredVariables
        expression

  | .schedule targetAction _ =>
      targetAction =
        declaredAction

@[simp]
theorem storeWellFormed_assign
    (declaredVariables : List VarName)
    (declaredAction : ActionName)
    (target : VarName)
    (expression : LF.Expr) :
    StoreWellFormed
        declaredVariables
        declaredAction
        (.assign target expression) ↔
      target ∈ declaredVariables ∧
      LF.Expr.StoreWellFormed
        declaredVariables
        expression := by
  rfl

@[simp]
theorem storeWellFormed_schedule
    (declaredVariables : List VarName)
    (declaredAction targetAction : ActionName)
    (delay : Delay) :
    StoreWellFormed
        declaredVariables
        declaredAction
        (.schedule targetAction delay) ↔
      targetAction =
        declaredAction := by
  rfl

/--
The declaration-list predicate specializes to the original generated
v0 statement predicate on a singleton declaration list.
-/
theorem storeWellFormed_singleton_iff
    (declaredVariable : VarName)
    (declaredAction : ActionName)
    (statement : LF.Stmt) :
    StoreWellFormed
        [declaredVariable]
        declaredAction
        statement ↔
      LF.Stmt.WellFormed
        declaredVariable
        declaredAction
        statement := by

  cases statement <;>
    simp [
      StoreWellFormed,
      LF.Stmt.WellFormed,
      LF.Expr.storeWellFormed_singleton_iff
    ]

end Stmt

namespace Body

/--
Every generated statement must be well formed for the complete reactor
state declaration list and the generated logical action.
-/
def StoreWellFormed
    (declaredVariables : List VarName)
    (declaredAction : ActionName)
    (body : LF.Body) :
    Prop :=
  ∀ statement,
    statement ∈ body →
    LF.Stmt.StoreWellFormed
      declaredVariables
      declaredAction
      statement

@[simp]
theorem storeWellFormed_nil
    (declaredVariables : List VarName)
    (declaredAction : ActionName) :
    StoreWellFormed
      declaredVariables
      declaredAction
      [] := by

  intro statement hMember
  cases hMember

@[simp]
theorem storeWellFormed_cons
    (declaredVariables : List VarName)
    (declaredAction : ActionName)
    (statement : LF.Stmt)
    (remaining : LF.Body) :
    StoreWellFormed
        declaredVariables
        declaredAction
        (statement :: remaining) ↔
      LF.Stmt.StoreWellFormed
          declaredVariables
          declaredAction
          statement ∧
        StoreWellFormed
          declaredVariables
          declaredAction
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
The declaration-list predicate specializes to the original generated
v0 body predicate on a singleton declaration list.
-/
theorem storeWellFormed_singleton_iff
    (declaredVariable : VarName)
    (declaredAction : ActionName)
    (body : LF.Body) :
    StoreWellFormed
        [declaredVariable]
        declaredAction
        body ↔
      LF.Body.WellFormed
        declaredVariable
        declaredAction
        body := by

  constructor

  · intro hBody statement hMember

    exact
      (LF.Stmt.storeWellFormed_singleton_iff
        declaredVariable
        declaredAction
        statement).mp
        (hBody
          statement
          hMember)

  · intro hBody statement hMember

    exact
      (LF.Stmt.storeWellFormed_singleton_iff
        declaredVariable
        declaredAction
        statement).mpr
        (hBody
          statement
          hMember)

end Body
end LF
end Relico
