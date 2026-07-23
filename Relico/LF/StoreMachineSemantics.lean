import Relico.LF.StoreDispatchSemantics
import Relico.LF.StoreSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
Labels for the combined generated-LF store machine semantics.

A transition is either execution of one generated reaction statement
or dispatch of one pending logical-action occurrence.
-/
inductive StoreMachineLabel where

  | statement :
      LF.Label →
      StoreMachineLabel

  | dispatch :
      LF.PendingAction →
      StoreMachineLabel

deriving Repr, DecidableEq, BEq, Inhabited

/--
Combined one-step generated-LF semantics over a finite reactor-state
store.
-/
inductive StoreMachineStep
    (declaredVariables : List VarName)
    (logicalAction : ActionName)
    (messageReactionBody : LF.Body) :
    LF.StoreState →
    LF.StoreMachineLabel →
    LF.StoreState →
    Prop where

  | statement
      {stateBefore stateAfter : LF.StoreState}
      {label : LF.Label}
      (hStep :
        LF.StoreStep
          declaredVariables
          logicalAction
          stateBefore
          label
          stateAfter) :

      StoreMachineStep
        declaredVariables
        logicalAction
        messageReactionBody
        stateBefore
        (LF.StoreMachineLabel.statement
          label)
        stateAfter

  | dispatch
      {stateBefore stateAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      (hDispatch :
        LF.StoreDispatchStep
          logicalAction
          messageReactionBody
          stateBefore
          selectedAction
          stateAfter) :

      StoreMachineStep
        declaredVariables
        logicalAction
        messageReactionBody
        stateBefore
        (LF.StoreMachineLabel.dispatch
          selectedAction)
        stateAfter

end LF
end Relico
