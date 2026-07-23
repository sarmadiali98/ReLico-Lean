import Relico.LF.StoreSemantics
import Relico.LF.StoreWellFormed

set_option autoImplicit false

namespace Relico
namespace LF

/--
A finite execution of the generated-LF store statement semantics.

The label list records the transition labels in execution order.
-/
inductive StoreTrace
    (declaredVariables : List VarName)
    (logicalAction : ActionName) :
    LF.StoreState →
    List LF.Label →
    LF.StoreState →
    Prop where

  | refl
      (state : LF.StoreState) :

      StoreTrace
        declaredVariables
        logicalAction
        state
        []
        state

  | step
      {before middle after : LF.StoreState}
      {label : LF.Label}
      {remainingLabels : List LF.Label}
      (hStep :
        LF.StoreStep
          declaredVariables
          logicalAction
          before
          label
          middle)
      (hTrace :
        StoreTrace
          declaredVariables
          logicalAction
          middle
          remainingLabels
          after) :

      StoreTrace
        declaredVariables
        logicalAction
        before
        (label :: remainingLabels)
        after

namespace StoreStep

/--
An LF store statement step preserves structural well-formedness of the
remaining active body.
-/
theorem preserves_body_storeWellFormed
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
    (hBefore :
      LF.Body.StoreWellFormed
        declaredVariables
        logicalAction
        before.activeBody) :
    LF.Body.StoreWellFormed
      declaredVariables
      logicalAction
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
        ((LF.Body.storeWellFormed_cons
          declaredVariables
          logicalAction
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
        ((LF.Body.storeWellFormed_cons
          declaredVariables
          logicalAction
          (LF.Stmt.schedule
            targetAction
            delay)
          remaining).mp
          hBefore).2

end StoreStep
end LF
end Relico
