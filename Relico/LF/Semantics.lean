import Relico.LF.Evaluation

set_option autoImplicit false

namespace Relico
namespace LF

/--
Labels for the first generated-LF transition rules.

Assignments are internal transitions. Scheduling records the logical
action and its target tag.
-/
inductive Label where
  | internal
  | schedule :
      ActionName →
      Tag →
      Label
deriving Repr, DecidableEq, BEq, Inhabited

/--
Small-step operational semantics for reaction statements in the
generated LF subset.
-/
inductive Step
    (program : LF.Program) :
    LF.State →
    LF.Label →
    LF.State →
    Prop where

  | assign
      (currentTag : Tag)
      (stateValue : Int)
      (pendingActions : ActionQueue)
      (target : VarName)
      (expression : Expr)
      (remaining : Body)
      (hTarget :
        target =
          program.reactor.stateVar) :
      Step
        program
        {
          currentTag := currentTag
          stateValue := stateValue
          pendingActions := pendingActions
          activeBody :=
            LF.Stmt.assign
              target
              expression ::
            remaining
        }
        LF.Label.internal
        {
          currentTag := currentTag
          stateValue :=
            LF.Expr.evaluate
              stateValue
              expression
          pendingActions := pendingActions
          activeBody := remaining
        }

  | schedule
      (currentTag : Tag)
      (stateValue : Int)
      (pendingActions : ActionQueue)
      (targetAction : ActionName)
      (delay : Delay)
      (remaining : Body)
      (hTarget :
        targetAction =
          program.reactor.logicalAction) :
      Step
        program
        {
          currentTag := currentTag
          stateValue := stateValue
          pendingActions := pendingActions
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
          currentTag := currentTag
          stateValue := stateValue
          pendingActions :=
            pendingActions ++
              [{
                name := targetAction
                tag :=
                  Tag.schedule
                    currentTag
                    delay
              }]
          activeBody := remaining
        }

end LF
end Relico
