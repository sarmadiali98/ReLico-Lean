import Relico.LF.Semantics
import Relico.LF.StoreEvaluation
import Relico.LF.StoreState

set_option autoImplicit false

namespace Relico
namespace LF

/--
Small-step generated-LF semantics over a finite reactor-state store.

The declaration list may contain multiple reactor state variables.
Assignment is enabled when the target is declared and the expression
evaluates successfully.

The logical-action parameter identifies the generated action supported
by the current semantic fragment.
-/
inductive StoreStep
    (declaredVariables : List VarName)
    (logicalAction : ActionName) :
    LF.StoreState →
    LF.Label →
    LF.StoreState →
    Prop where

  | assign
      (currentTag : Tag)
      (stateStore : StateStore)
      (pendingActions : ActionQueue)
      (target : VarName)
      (expression : Expr)
      (evaluatedValue : Int)
      (remaining : Body)
      (hTarget :
        target ∈ declaredVariables)
      (hEvaluate :
        Expr.evaluateStore
            stateStore
            expression =
          some evaluatedValue) :

      StoreStep
        declaredVariables
        logicalAction
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
      (currentTag : Tag)
      (stateStore : StateStore)
      (pendingActions : ActionQueue)
      (targetAction : ActionName)
      (delay : Delay)
      (remaining : Body)
      (hTarget :
        targetAction =
          logicalAction) :

      StoreStep
        declaredVariables
        logicalAction
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
          (Tag.schedule
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
                  Tag.schedule
                    currentTag
                    delay
              }
            ]

          activeBody :=
            remaining
        }

namespace StoreStep

/--
Every generated-LF store step preserves coverage of the declared
reactor state variables.

Assignment preserves coverage through `StateStore.covers_update`.
Scheduling leaves the state store unchanged.
-/
theorem preserves_coverage
    {declaredVariables : List VarName}
    {logicalAction : ActionName}
    {before after : LF.StoreState}
    {label : LF.Label}
    (hStep :
      LF.StoreStep
        declaredVariables
        logicalAction
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

      change
        StateStore.Covers
          declaredVariables
          (StateStore.update
            stateStore
            target
            evaluatedValue)

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

      change
        StateStore.Covers
          declaredVariables
          stateStore

      exact hCoverage

end StoreStep
end LF
end Relico
