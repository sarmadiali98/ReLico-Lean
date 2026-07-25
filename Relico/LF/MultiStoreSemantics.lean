import Relico.LF.MultiStoreWellFormed
import Relico.LF.StoreEvaluation
import Relico.LF.StoreState
import Relico.LF.Semantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
Small-step generated-LF semantics over a finite state store with
multiple declared logical actions.
-/
inductive MultiStoreStep
    (declaredVariables : List VarName)
    (declaredActions : List ActionName) :
    LF.StoreState →
    LF.Label →
    LF.StoreState →
    Prop where

  | assign
      (currentTag : LF.Tag)
      (stateStore : StateStore)
      (pendingActions : LF.ActionQueue)
      (target : VarName)
      (expression : LF.Expr)
      (evaluatedValue : Int)
      (remaining : LF.Body)
      (hTarget :
        target ∈ declaredVariables)
      (hEvaluate :
        LF.Expr.evaluateStore
            stateStore
            expression =
          some evaluatedValue) :

      MultiStoreStep
        declaredVariables
        declaredActions
        {
          currentTag :=
            currentTag

          stateStore :=
            stateStore

          pendingActions :=
            pendingActions

          activeBody :=
            LF.Stmt.assign
              target
              expression ::
            remaining
        }
        LF.Label.internal
        {
          currentTag :=
            currentTag

          stateStore :=
            StateStore.update
              stateStore
              target
              evaluatedValue

          pendingActions :=
            pendingActions

          activeBody :=
            remaining
        }

  | schedule
      (currentTag : LF.Tag)
      (stateStore : StateStore)
      (pendingActions : LF.ActionQueue)
      (targetAction : ActionName)
      (delay : Delay)
      (remaining : LF.Body)
      (hTarget :
        targetAction ∈
          declaredActions) :

      MultiStoreStep
        declaredVariables
        declaredActions
        {
          currentTag :=
            currentTag

          stateStore :=
            stateStore

          pendingActions :=
            pendingActions

          activeBody :=
            LF.Stmt.schedule
              targetAction
              delay ::
            remaining
        }
        (LF.Label.schedule
          targetAction
          (LF.Tag.schedule
            currentTag
            delay))
        {
          currentTag :=
            currentTag

          stateStore :=
            stateStore

          pendingActions :=
            pendingActions ++ [
              {
                name :=
                  targetAction

                tag :=
                  LF.Tag.schedule
                    currentTag
                    delay
              }
            ]

          activeBody :=
            remaining
        }

namespace MultiStoreStep

/--
Every generated multi-action statement step preserves state-store
coverage.
-/
theorem preserves_coverage
    {declaredVariables : List VarName}
    {declaredActions : List ActionName}
    {before after : LF.StoreState}
    {label : LF.Label}
    (hStep :
      LF.MultiStoreStep
        declaredVariables
        declaredActions
        before
        label
        after)
    (hCoverage :
      LF.StoreState.Covers
        declaredVariables
        before) :
    LF.StoreState.Covers
      declaredVariables
      after := by

  cases hStep with

  | assign
      currentTag
      stateStore
      pendingActions
      target
      expression
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      exact
        StateStore.covers_update
          declaredVariables
          stateStore
          target
          evaluatedValue
          hCoverage

  | schedule
      currentTag
      stateStore
      pendingActions
      targetAction
      delay
      remaining
      hTarget =>

      exact hCoverage

/--
A generated statement step preserves well-formedness of the remaining
active body.
-/
theorem preserves_body_multiStoreWellFormed
    {declaredVariables : List VarName}
    {declaredActions : List ActionName}
    {before after : LF.StoreState}
    {label : LF.Label}
    (hStep :
      LF.MultiStoreStep
        declaredVariables
        declaredActions
        before
        label
        after)
    (hBefore :
      LF.Body.MultiStoreWellFormed
        declaredVariables
        declaredActions
        before.activeBody) :
    LF.Body.MultiStoreWellFormed
      declaredVariables
      declaredActions
      after.activeBody := by

  cases hStep with

  | assign
      currentTag
      stateStore
      pendingActions
      target
      expression
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      exact
        ((LF.Body.multiStoreWellFormed_cons
          declaredVariables
          declaredActions
          (LF.Stmt.assign
            target
            expression)
          remaining).mp
          hBefore).2

  | schedule
      currentTag
      stateStore
      pendingActions
      targetAction
      delay
      remaining
      hTarget =>

      exact
        ((LF.Body.multiStoreWellFormed_cons
          declaredVariables
          declaredActions
          (LF.Stmt.schedule
            targetAction
            delay)
          remaining).mp
          hBefore).2

end MultiStoreStep
end LF
end Relico
