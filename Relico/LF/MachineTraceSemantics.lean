import Relico.LF.MachineSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
A finite execution of the combined generated-LF machine semantics.

The machine-label list records statement and dispatch transitions in
execution order.
-/
inductive MachineSteps
    (program : LF.Program) :
    LF.State →
    List LF.MachineLabel →
    LF.State →
    Prop where

  | refl
      (state : LF.State) :
      MachineSteps
        program
        state
        []
        state

  | cons
      {stateBefore stateMiddle stateAfter : LF.State}
      {label : LF.MachineLabel}
      {remainingLabels : List LF.MachineLabel}
      (headStep :
        LF.MachineStep
          program
          stateBefore
          label
          stateMiddle)
      (remainingSteps :
        MachineSteps
          program
          stateMiddle
          remainingLabels
          stateAfter) :
      MachineSteps
        program
        stateBefore
        (label :: remainingLabels)
        stateAfter

end LF
end Relico
