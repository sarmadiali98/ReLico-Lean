import Relico.LF.MultiStoreDispatchSemantics
import Relico.LF.MultiStoreSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
Labels for the combined finite-store generated-LF machine with
multiple logical actions and message reactions.

A dispatch label retains both the selected action occurrence and the
generated reaction whose body is loaded.
-/
inductive MultiStoreMachineLabel where

  | statement :
      LF.Label →
      MultiStoreMachineLabel

  | dispatch :
      LF.PendingAction →
      LF.Reaction →
      MultiStoreMachineLabel

deriving Repr, DecidableEq, BEq, Inhabited

/--
Combined one-step generated-LF semantics for finite state, multiple
logical actions, and multiple message reactions.
-/
inductive MultiStoreMachineStep
    (declaredVariables : List VarName)
    (logicalActions : List ActionName)
    (messageReactions : List LF.Reaction) :
    LF.StoreState →
    LF.MultiStoreMachineLabel →
    LF.StoreState →
    Prop where

  | statement
      {stateBefore stateAfter : LF.StoreState}
      {label : LF.Label}
      (hStep :
        LF.MultiStoreStep
          declaredVariables
          logicalActions
          stateBefore
          label
          stateAfter) :

      MultiStoreMachineStep
        declaredVariables
        logicalActions
        messageReactions
        stateBefore
        (LF.MultiStoreMachineLabel.statement
          label)
        stateAfter

  | dispatch
      {stateBefore stateAfter : LF.StoreState}
      {selectedAction : LF.PendingAction}
      {selectedReaction : LF.Reaction}
      (hDispatch :
        LF.MultiStoreDispatchStep
          messageReactions
          stateBefore
          selectedAction
          selectedReaction
          stateAfter) :

      MultiStoreMachineStep
        declaredVariables
        logicalActions
        messageReactions
        stateBefore
        (LF.MultiStoreMachineLabel.dispatch
          selectedAction
          selectedReaction)
        stateAfter

end LF
end Relico
