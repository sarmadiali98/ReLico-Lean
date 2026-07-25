import Relico.LF.MultiStoreSyntax
import Relico.LF.StoreWellFormed

set_option autoImplicit false

namespace Relico
namespace LF

def reactionNames
    (reactions : List LF.Reaction) :
    List ReactionName :=
  reactions.map
    (fun reaction =>
      reaction.name)

def reactionTriggers
    (reactions : List LF.Reaction) :
    List LF.Trigger :=
  reactions.map
    (fun reaction =>
      reaction.trigger)

namespace Stmt

/--
Structural validity of a generated LF statement for finite reactor
state and multiple declared logical actions.
-/
def MultiStoreWellFormed
    (declaredVariables : List VarName)
    (declaredActions : List ActionName) :
    LF.Stmt →
    Prop

  | .assign target expression =>
      target ∈ declaredVariables ∧
      LF.Expr.StoreWellFormed
        declaredVariables
        expression

  | .schedule targetAction _ =>
      targetAction ∈
        declaredActions

@[simp]
theorem multiStoreWellFormed_assign
    (declaredVariables : List VarName)
    (declaredActions : List ActionName)
    (target : VarName)
    (expression : LF.Expr) :
    MultiStoreWellFormed
        declaredVariables
        declaredActions
        (.assign target expression) ↔
      target ∈ declaredVariables ∧
      LF.Expr.StoreWellFormed
        declaredVariables
        expression := by
  rfl

@[simp]
theorem multiStoreWellFormed_schedule
    (declaredVariables : List VarName)
    (declaredActions : List ActionName)
    (targetAction : ActionName)
    (delay : Delay) :
    MultiStoreWellFormed
        declaredVariables
        declaredActions
        (.schedule targetAction delay) ↔
      targetAction ∈
        declaredActions := by
  rfl

theorem multiStoreWellFormed_singleton_iff
    (declaredVariables : List VarName)
    (declaredAction : ActionName)
    (statement : LF.Stmt) :
    MultiStoreWellFormed
        declaredVariables
        [declaredAction]
        statement ↔
      LF.Stmt.StoreWellFormed
        declaredVariables
        declaredAction
        statement := by

  cases statement <;>
    simp [
      MultiStoreWellFormed,
      LF.Stmt.StoreWellFormed
    ]

end Stmt

namespace Body

def MultiStoreWellFormed
    (declaredVariables : List VarName)
    (declaredActions : List ActionName)
    (body : LF.Body) :
    Prop :=
  ∀ statement,
    statement ∈ body →
    LF.Stmt.MultiStoreWellFormed
      declaredVariables
      declaredActions
      statement

@[simp]
theorem multiStoreWellFormed_nil
    (declaredVariables : List VarName)
    (declaredActions : List ActionName) :
    MultiStoreWellFormed
      declaredVariables
      declaredActions
      [] := by

  intro statement hMember
  cases hMember

@[simp]
theorem multiStoreWellFormed_cons
    (declaredVariables : List VarName)
    (declaredActions : List ActionName)
    (statement : LF.Stmt)
    (remaining : LF.Body) :
    MultiStoreWellFormed
        declaredVariables
        declaredActions
        (statement :: remaining) ↔
      LF.Stmt.MultiStoreWellFormed
          declaredVariables
          declaredActions
          statement ∧
        MultiStoreWellFormed
          declaredVariables
          declaredActions
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

theorem multiStoreWellFormed_singleton_iff
    (declaredVariables : List VarName)
    (declaredAction : ActionName)
    (body : LF.Body) :
    MultiStoreWellFormed
        declaredVariables
        [declaredAction]
        body ↔
      LF.Body.StoreWellFormed
        declaredVariables
        declaredAction
        body := by

  constructor

  · intro hBody statement hMember

    exact
      (LF.Stmt.multiStoreWellFormed_singleton_iff
        declaredVariables
        declaredAction
        statement).mp
        (hBody statement hMember)

  · intro hBody statement hMember

    exact
      (LF.Stmt.multiStoreWellFormed_singleton_iff
        declaredVariables
        declaredAction
        statement).mpr
        (hBody statement hMember)

end Body
end LF
end Relico
