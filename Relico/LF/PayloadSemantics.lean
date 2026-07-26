import Relico.LF.Evaluation
import Relico.LF.PayloadSyntax
import Relico.LF.State

set_option autoImplicit false

namespace Relico
namespace LF

/--
Runtime state for the additive generated integer-payload fragment.

This state is separate from `LF.State` because its active body contains
`LF.PayloadStmt`.
-/
structure PayloadState where

  currentTag :
    LF.Tag

  stateValue :
    Int

  pendingActions :
    LF.ActionQueue

  activeBody :
    LF.PayloadBody

deriving Repr, DecidableEq, BEq, Inhabited

/--
Observable scheduling label for one evaluated integer logical-action
payload.
-/
inductive PayloadLabel where

  | scheduleInt :
      ActionName →
      LF.Tag →
      Int →
      PayloadLabel

deriving Repr, DecidableEq, BEq, Inhabited

/--
Small-step generated-LF semantics for integer-payload scheduling.

The translated payload expression is evaluated in the current reactor
state. Its result is stored as a singleton ordered action payload.
-/
inductive PayloadStep
    (declaredAction : ActionName) :
    LF.PayloadState →
    LF.PayloadLabel →
    LF.PayloadState →
    Prop where

  | scheduleInt
      (currentTag : LF.Tag)
      (stateValue : Int)
      (pendingActions : LF.ActionQueue)
      (targetAction : ActionName)
      (payloadExpression : LF.Expr)
      (delay : Delay)
      (evaluatedValue : Int)
      (remaining : LF.PayloadBody)
      (hTarget :
        targetAction =
          declaredAction)
      (hEvaluate :
        LF.Expr.evaluate
            stateValue
            payloadExpression =
          evaluatedValue) :

      PayloadStep
        declaredAction
        {
          currentTag :=
            currentTag

          stateValue :=
            stateValue

          pendingActions :=
            pendingActions

          activeBody :=
            LF.PayloadStmt.scheduleInt
                targetAction
                payloadExpression
                delay ::
              remaining
        }
        (LF.PayloadLabel.scheduleInt
          targetAction
          (LF.Tag.schedule
            currentTag
            delay)
          evaluatedValue)
        {
          currentTag :=
            currentTag

          stateValue :=
            stateValue

          pendingActions :=
            pendingActions ++ [
              LF.PendingAction.scheduleWithPayload
                currentTag
                targetAction
                [
                  evaluatedValue
                ]
                delay
            ]

          activeBody :=
            remaining
        }

end LF
end Relico
