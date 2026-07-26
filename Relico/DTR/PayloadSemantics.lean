import Relico.DTR.Evaluation
import Relico.DTR.PayloadSyntax
import Relico.DTR.State

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Runtime state for the additive single-integer payload fragment.

This state is separate from `DTR.State` because its active body contains
`DTR.PayloadStmt` rather than the established parameterless statements.
-/
structure PayloadState where

  currentTime :
    LogicalTime

  stateValue :
    Int

  pendingMessages :
    DTR.MessageBag

  activeBody :
    DTR.PayloadBody

deriving Repr, DecidableEq, BEq, Inhabited

/--
Observable scheduling label for one evaluated integer payload.
-/
inductive PayloadLabel where

  | sendInt :
      MsgName →
      LogicalTime →
      Int →
      PayloadLabel

deriving Repr, DecidableEq, BEq, Inhabited

/--
Small-step semantics for the additive integer-payload source statement.

The payload expression is evaluated in the current source state. Its
result is stored as a singleton ordered payload in the new pending
message occurrence.
-/
inductive PayloadStep
    (declaredMessageServer : MsgName) :
    DTR.PayloadState →
    DTR.PayloadLabel →
    DTR.PayloadState →
    Prop where

  | selfSendInt
      (currentTime : LogicalTime)
      (stateValue : Int)
      (pendingMessages : DTR.MessageBag)
      (targetMessage : MsgName)
      (payloadExpression : DTR.Expr)
      (delay : Delay)
      (evaluatedValue : Int)
      (remaining : DTR.PayloadBody)
      (hTarget :
        targetMessage =
          declaredMessageServer)
      (hEvaluate :
        DTR.Expr.evaluate
            stateValue
            payloadExpression =
          evaluatedValue) :

      PayloadStep
        declaredMessageServer
        {
          currentTime :=
            currentTime

          stateValue :=
            stateValue

          pendingMessages :=
            pendingMessages

          activeBody :=
            DTR.PayloadStmt.selfSendInt
                targetMessage
                payloadExpression
                delay ::
              remaining
        }
        (DTR.PayloadLabel.sendInt
          targetMessage
          (LogicalTime.after
            currentTime
            delay)
          evaluatedValue)
        {
          currentTime :=
            currentTime

          stateValue :=
            stateValue

          pendingMessages :=
            pendingMessages ++ [
              DTR.PendingMessage.scheduleWithPayload
                currentTime
                targetMessage
                [
                  evaluatedValue
                ]
                delay
            ]

          activeBody :=
            remaining
        }

end DTR
end Relico
