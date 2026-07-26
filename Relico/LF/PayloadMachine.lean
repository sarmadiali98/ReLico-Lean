import Relico.LF.PayloadSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
A finite execution of the additive generated-LF payload-scheduling
semantics.

The label list records typed logical-action scheduling transitions in
execution order. Payload dispatch is outside this fragment.
-/
inductive PayloadSteps
    (declaredAction : ActionName) :
    LF.PayloadState →
    List LF.PayloadLabel →
    LF.PayloadState →
    Prop where

  | refl
      (state : LF.PayloadState) :

      PayloadSteps
        declaredAction
        state
        []
        state

  | cons
      {before middle after : LF.PayloadState}
      {label : LF.PayloadLabel}
      {remainingLabels : List LF.PayloadLabel}
      (headStep :
        LF.PayloadStep
          declaredAction
          before
          label
          middle)
      (remainingSteps :
        PayloadSteps
          declaredAction
          middle
          remainingLabels
          after) :

      PayloadSteps
        declaredAction
        before
        (label :: remainingLabels)
        after

end LF
end Relico
