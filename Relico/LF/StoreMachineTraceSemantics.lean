import Relico.LF.StoreMachineSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
A finite execution of the combined generated-LF store machine.

Machine labels are recorded in execution order.
-/
inductive StoreMachineSteps
    (declaredVariables : List VarName)
    (logicalAction : ActionName)
    (messageReactionBody : LF.Body) :
    LF.StoreState →
    List LF.StoreMachineLabel →
    LF.StoreState →
    Prop where

  | refl
      (state : LF.StoreState) :

      StoreMachineSteps
        declaredVariables
        logicalAction
        messageReactionBody
        state
        []
        state

  | cons
      {before middle after : LF.StoreState}
      {label : LF.StoreMachineLabel}
      {remainingLabels : List LF.StoreMachineLabel}
      (hStep :
        LF.StoreMachineStep
          declaredVariables
          logicalAction
          messageReactionBody
          before
          label
          middle)
      (hSteps :
        StoreMachineSteps
          declaredVariables
          logicalAction
          messageReactionBody
          middle
          remainingLabels
          after) :

      StoreMachineSteps
        declaredVariables
        logicalAction
        messageReactionBody
        before
        (label :: remainingLabels)
        after

end LF
end Relico
