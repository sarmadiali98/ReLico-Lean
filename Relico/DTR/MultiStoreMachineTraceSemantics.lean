import Relico.DTR.MultiStoreMachineSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
A finite execution of the combined finite-store, multiple-message-
server DTR machine.

Machine labels are recorded in execution order.
-/
inductive MultiStoreMachineSteps
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer) :
    DTR.StoreState →
    List DTR.MultiStoreMachineLabel →
    DTR.StoreState →
    Prop where

  | refl
      (state : DTR.StoreState) :

      MultiStoreMachineSteps
        declaredVariables
        messageServers
        state
        []
        state

  | cons
      {before middle after : DTR.StoreState}
      {label : DTR.MultiStoreMachineLabel}
      {remainingLabels :
        List DTR.MultiStoreMachineLabel}
      (hStep :
        DTR.MultiStoreMachineStep
          declaredVariables
          messageServers
          before
          label
          middle)
      (hSteps :
        MultiStoreMachineSteps
          declaredVariables
          messageServers
          middle
          remainingLabels
          after) :

      MultiStoreMachineSteps
        declaredVariables
        messageServers
        before
        (label :: remainingLabels)
        after

end DTR
end Relico
