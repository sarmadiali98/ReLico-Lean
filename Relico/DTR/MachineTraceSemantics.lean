import Relico.DTR.MachineSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
A finite execution of the combined DTR machine semantics.

The machine-label list records statement and dispatch transitions in
execution order.
-/
inductive MachineSteps
    (model : DTR.Model) :
    DTR.State →
    List DTR.MachineLabel →
    DTR.State →
    Prop where

  | refl
      (state : DTR.State) :
      MachineSteps
        model
        state
        []
        state

  | cons
      {stateBefore stateMiddle stateAfter : DTR.State}
      {label : DTR.MachineLabel}
      {remainingLabels : List DTR.MachineLabel}
      (headStep :
        DTR.MachineStep
          model
          stateBefore
          label
          stateMiddle)
      (remainingSteps :
        MachineSteps
          model
          stateMiddle
          remainingLabels
          stateAfter) :
      MachineSteps
        model
        stateBefore
        (label :: remainingLabels)
        stateAfter

end DTR
end Relico
