import Relico.LF.Semantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
A finite sequence of generated-LF statement-level transitions.

The label list records the transition labels in execution order.
-/
inductive Steps
    (program : LF.Program) :
    LF.State →
    List LF.Label →
    LF.State →
    Prop where

  | refl
      (state : LF.State) :
      Steps
        program
        state
        []
        state

  | cons
      {stateBefore stateMiddle stateAfter : LF.State}
      {label : LF.Label}
      {remainingLabels : List LF.Label}
      (headStep :
        LF.Step
          program
          stateBefore
          label
          stateMiddle)
      (remainingSteps :
        Steps
          program
          stateMiddle
          remainingLabels
          stateAfter) :
      Steps
        program
        stateBefore
        (label :: remainingLabels)
        stateAfter

end LF
end Relico
