import Relico.LF.BoundPayloadState

set_option autoImplicit false

namespace Relico
namespace LF

/--
Observable label for one generated parameter-aware payload schedule.
-/
inductive BoundPayloadLabel where

  | scheduleInt :
      ActionName →
      LF.Tag →
      Int →
      BoundPayloadLabel

deriving Repr, DecidableEq, BEq, Inhabited

/--
Small-step generated-LF semantics for parameter-aware payload
scheduling.

The translated expression is evaluated using the persistent reactor
state and the semantic environment obtained from the triggering typed
logical action.
-/
inductive BoundPayloadStep
    (declaredAction : ActionName) :
    LF.BoundPayloadState →
    LF.BoundPayloadLabel →
    LF.BoundPayloadState →
    Prop where

  | scheduleInt
      (currentTag : LF.Tag)
      (stateValue : Int)
      (parameters : ParameterStore)
      (pendingActions : LF.ActionQueue)
      (targetAction : ActionName)
      (payloadExpression : LF.PayloadExpr)
      (delay : Delay)
      (evaluatedValue : Int)
      (remaining : LF.BoundPayloadBody)
      (hTarget :
        targetAction =
          declaredAction)
      (hEvaluate :
        LF.PayloadExpr.evaluate
            stateValue
            parameters
            payloadExpression =
          some evaluatedValue) :

      BoundPayloadStep
        declaredAction
        {
          currentTag :=
            currentTag

          stateValue :=
            stateValue

          parameters :=
            parameters

          pendingActions :=
            pendingActions

          activeBody :=
            LF.BoundPayloadStmt.scheduleInt
                targetAction
                payloadExpression
                delay ::
              remaining
        }
        (LF.BoundPayloadLabel.scheduleInt
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

          parameters :=
            parameters

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

namespace BoundPayloadStep

theorem preserves_stateValue
    {declaredAction : ActionName}
    {before after : LF.BoundPayloadState}
    {label : LF.BoundPayloadLabel}
    (hStep :
      LF.BoundPayloadStep
        declaredAction
        before
        label
        after) :
    after.stateValue =
      before.stateValue := by

  cases hStep
  rfl

theorem preserves_parameters
    {declaredAction : ActionName}
    {before after : LF.BoundPayloadState}
    {label : LF.BoundPayloadLabel}
    (hStep :
      LF.BoundPayloadStep
        declaredAction
        before
        label
        after) :
    after.parameters =
      before.parameters := by

  cases hStep
  rfl

end BoundPayloadStep
end LF
end Relico
