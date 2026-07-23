import Relico.DTR.StoreDispatchSemantics
import Relico.DTR.StoreSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Labels for the combined store-based DTR machine semantics.

A transition is either execution of one active-body statement or
dispatch of one pending message occurrence.
-/
inductive StoreMachineLabel where

  | statement :
      DTR.Label →
      StoreMachineLabel

  | dispatch :
      DTR.PendingMessage →
      StoreMachineLabel

deriving Repr, DecidableEq, BEq, Inhabited

/--
Combined one-step DTR semantics over a finite state-variable store.
-/
inductive StoreMachineStep
    (declaredVariables : List VarName)
    (messageServer : MsgName)
    (messageBody : DTR.Body) :
    DTR.StoreState →
    DTR.StoreMachineLabel →
    DTR.StoreState →
    Prop where

  | statement
      {stateBefore stateAfter : DTR.StoreState}
      {label : DTR.Label}
      (hStep :
        DTR.StoreStep
          declaredVariables
          messageServer
          stateBefore
          label
          stateAfter) :

      StoreMachineStep
        declaredVariables
        messageServer
        messageBody
        stateBefore
        (DTR.StoreMachineLabel.statement
          label)
        stateAfter

  | dispatch
      {stateBefore stateAfter : DTR.StoreState}
      {selectedMessage : DTR.PendingMessage}
      (hDispatch :
        DTR.StoreDispatchStep
          messageServer
          messageBody
          stateBefore
          selectedMessage
          stateAfter) :

      StoreMachineStep
        declaredVariables
        messageServer
        messageBody
        stateBefore
        (DTR.StoreMachineLabel.dispatch
          selectedMessage)
        stateAfter

end DTR
end Relico
