import Relico.DTR.Semantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
A finite sequence of DTR statement-level transitions.

The label list records the transition labels in execution order.
-/
inductive Steps
    (model : DTR.Model) :
    DTR.State →
    List DTR.Label →
    DTR.State →
    Prop where

  | refl
      (state : DTR.State) :
      Steps
        model
        state
        []
        state

  | cons
      {stateBefore stateMiddle stateAfter : DTR.State}
      {label : DTR.Label}
      {remainingLabels : List DTR.Label}
      (headStep :
        DTR.Step
          model
          stateBefore
          label
          stateMiddle)
      (remainingSteps :
        Steps
          model
          stateMiddle
          remainingLabels
          stateAfter) :
      Steps
        model
        stateBefore
        (label :: remainingLabels)
        stateAfter

end DTR
end Relico
