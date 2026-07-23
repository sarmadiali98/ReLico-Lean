import Relico.DTR.Evaluation

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Labels for the first DTR transition rules.

Assignments are internal transitions. A self-send records the message
name and its computed arrival time.
-/
inductive Label where
  | internal
  | send :
      MsgName →
      LogicalTime →
      Label
deriving Repr, DecidableEq, BEq, Inhabited

/--
Small-step operational semantics for the executable statements in
vertical slice v0.
-/
inductive Step
    (model : DTR.Model) :
    DTR.State →
    DTR.Label →
    DTR.State →
    Prop where

  | assign
      (currentTime : LogicalTime)
      (stateValue : Int)
      (pendingMessages : MessageBag)
      (target : VarName)
      (expression : Expr)
      (remaining : Body)
      (hTarget :
        target =
          model.reactiveClass.stateVar) :
      Step
        model
        {
          currentTime := currentTime
          stateValue := stateValue
          pendingMessages := pendingMessages
          activeBody :=
            DTR.Stmt.assign
              target
              expression ::
            remaining
        }
        DTR.Label.internal
        {
          currentTime := currentTime
          stateValue :=
            DTR.Expr.evaluate
              stateValue
              expression
          pendingMessages := pendingMessages
          activeBody := remaining
        }

  | selfSend
      (currentTime : LogicalTime)
      (stateValue : Int)
      (pendingMessages : MessageBag)
      (targetMessage : MsgName)
      (delay : Delay)
      (remaining : Body)
      (hTarget :
        targetMessage =
          model.reactiveClass.messageServer.name) :
      Step
        model
        {
          currentTime := currentTime
          stateValue := stateValue
          pendingMessages := pendingMessages
          activeBody :=
            DTR.Stmt.selfSend
              targetMessage
              delay ::
            remaining
        }
        (DTR.Label.send
          targetMessage
          (LogicalTime.after
            currentTime
            delay))
        {
          currentTime := currentTime
          stateValue := stateValue
          pendingMessages :=
            pendingMessages ++
              [{
                name := targetMessage
                arrivalTime :=
                  LogicalTime.after
                    currentTime
                    delay
              }]
          activeBody := remaining
        }

end DTR
end Relico
