import Relico.DTR.BoundPayloadState

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Observable label for execution of one parameter-aware payload send.
-/
inductive BoundPayloadLabel where

  | sendInt :
      MsgName →
      LogicalTime →
      Int →
      BoundPayloadLabel

deriving Repr, DecidableEq, BEq, Inhabited

/--
Small-step semantics for parameter-aware payload statements.

The payload expression is evaluated using both persistent actor state and
the activation-local parameter environment installed by dispatch.
The evaluated integer is scheduled as a singleton ordered payload.
-/
inductive BoundPayloadStep
    (declaredMessageServer : MsgName) :
    DTR.BoundPayloadState →
    DTR.BoundPayloadLabel →
    DTR.BoundPayloadState →
    Prop where

  | selfSendInt
      (currentTime : LogicalTime)
      (stateValue : Int)
      (parameters : ParameterStore)
      (pendingMessages : DTR.MessageBag)
      (targetMessage : MsgName)
      (payloadExpression : DTR.PayloadExpr)
      (delay : Delay)
      (evaluatedValue : Int)
      (remaining : DTR.BoundPayloadBody)
      (hTarget :
        targetMessage =
          declaredMessageServer)
      (hEvaluate :
        DTR.PayloadExpr.evaluate
            stateValue
            parameters
            payloadExpression =
          some evaluatedValue) :

      BoundPayloadStep
        declaredMessageServer
        {
          currentTime :=
            currentTime

          stateValue :=
            stateValue

          parameters :=
            parameters

          pendingMessages :=
            pendingMessages

          activeBody :=
            DTR.BoundPayloadStmt.selfSendInt
                targetMessage
                payloadExpression
                delay ::
              remaining
        }
        (DTR.BoundPayloadLabel.sendInt
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

          parameters :=
            parameters

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

namespace BoundPayloadStep

theorem preserves_stateValue
    {declaredMessageServer : MsgName}
    {before after : DTR.BoundPayloadState}
    {label : DTR.BoundPayloadLabel}
    (hStep :
      DTR.BoundPayloadStep
        declaredMessageServer
        before
        label
        after) :
    after.stateValue =
      before.stateValue := by

  cases hStep
  rfl

theorem preserves_parameters
    {declaredMessageServer : MsgName}
    {before after : DTR.BoundPayloadState}
    {label : DTR.BoundPayloadLabel}
    (hStep :
      DTR.BoundPayloadStep
        declaredMessageServer
        before
        label
        after) :
    after.parameters =
      before.parameters := by

  cases hStep
  rfl

end BoundPayloadStep
end DTR
end Relico
