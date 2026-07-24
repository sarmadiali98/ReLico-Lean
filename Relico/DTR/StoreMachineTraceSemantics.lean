import Relico.DTR.StoreMachineSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
A finite execution of the combined DTR store machine.

Machine labels are recorded in execution order.
-/
inductive StoreMachineSteps
    (declaredVariables : List VarName)
    (messageServer : MsgName)
    (messageBody : DTR.Body) :
    DTR.StoreState →
    List DTR.StoreMachineLabel →
    DTR.StoreState →
    Prop where

  | refl
      (state : DTR.StoreState) :

      StoreMachineSteps
        declaredVariables
        messageServer
        messageBody
        state
        []
        state

  | cons
      {before middle after : DTR.StoreState}
      {label : DTR.StoreMachineLabel}
      {remainingLabels : List DTR.StoreMachineLabel}
      (hStep :
        DTR.StoreMachineStep
          declaredVariables
          messageServer
          messageBody
          before
          label
          middle)
      (hSteps :
        StoreMachineSteps
          declaredVariables
          messageServer
          messageBody
          middle
          remainingLabels
          after) :

      StoreMachineSteps
        declaredVariables
        messageServer
        messageBody
        before
        (label :: remainingLabels)
        after

end DTR
end Relico
