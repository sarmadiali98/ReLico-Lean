import Relico.LF.MultiStoreMachineSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
A finite execution of the combined generated-LF machine with multiple
logical actions and message reactions.

Machine labels are recorded in execution order.
-/
inductive MultiStoreMachineSteps
    (declaredVariables : List VarName)
    (logicalActions : List ActionName)
    (messageReactions : List LF.Reaction) :
    LF.StoreState →
    List LF.MultiStoreMachineLabel →
    LF.StoreState →
    Prop where

  | refl
      (state : LF.StoreState) :

      MultiStoreMachineSteps
        declaredVariables
        logicalActions
        messageReactions
        state
        []
        state

  | cons
      {before middle after : LF.StoreState}
      {label : LF.MultiStoreMachineLabel}
      {remainingLabels :
        List LF.MultiStoreMachineLabel}
      (hStep :
        LF.MultiStoreMachineStep
          declaredVariables
          logicalActions
          messageReactions
          before
          label
          middle)
      (hSteps :
        MultiStoreMachineSteps
          declaredVariables
          logicalActions
          messageReactions
          middle
          remainingLabels
          after) :

      MultiStoreMachineSteps
        declaredVariables
        logicalActions
        messageReactions
        before
        (label :: remainingLabels)
        after

end LF
end Relico
