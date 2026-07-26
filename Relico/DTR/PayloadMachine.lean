import Relico.DTR.PayloadSemantics
import Relico.DTR.PayloadWellFormed

set_option autoImplicit false

namespace Relico
namespace DTR

/--
A finite execution of the additive source payload-scheduling semantics.

The label list records payload-send transitions in execution order.
This relation currently covers statement execution only. Payload dispatch
is outside this fragment.
-/
inductive PayloadSteps
    (declaredMessageServer : MsgName) :
    DTR.PayloadState →
    List DTR.PayloadLabel →
    DTR.PayloadState →
    Prop where

  | refl
      (state : DTR.PayloadState) :

      PayloadSteps
        declaredMessageServer
        state
        []
        state

  | cons
      {before middle after : DTR.PayloadState}
      {label : DTR.PayloadLabel}
      {remainingLabels : List DTR.PayloadLabel}
      (headStep :
        DTR.PayloadStep
          declaredMessageServer
          before
          label
          middle)
      (remainingSteps :
        PayloadSteps
          declaredMessageServer
          middle
          remainingLabels
          after) :

      PayloadSteps
        declaredMessageServer
        before
        (label :: remainingLabels)
        after

/--
Executing one well-formed source payload statement preserves
well-formedness of the remaining active body.
-/
theorem payloadStep_preserves_bodyWellFormed
    {declaredMessageServer : MsgName}
    {before after : DTR.PayloadState}
    {label : DTR.PayloadLabel}
    (hStep :
      DTR.PayloadStep
        declaredMessageServer
        before
        label
        after)
    (hBefore :
      DTR.PayloadBody.WellFormed
        declaredMessageServer
        before.activeBody) :
    DTR.PayloadBody.WellFormed
      declaredMessageServer
      after.activeBody := by

  cases hStep with

  | selfSendInt
      currentTime
      stateValue
      pendingMessages
      targetMessage
      payloadExpression
      delay
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      have hCons :
          DTR.PayloadBody.WellFormed
            declaredMessageServer
            (DTR.PayloadStmt.selfSendInt
                targetMessage
                payloadExpression
                delay ::
              remaining) := by

        simpa using
          hBefore

      exact
        ((DTR.PayloadBody.wellFormed_cons
            declaredMessageServer
            (DTR.PayloadStmt.selfSendInt
              targetMessage
              payloadExpression
              delay)
            remaining).mp
          hCons).2

/--
Every finite source payload execution preserves active-body
well-formedness.
-/
theorem payloadSteps_preserve_bodyWellFormed
    {declaredMessageServer : MsgName}
    {before after : DTR.PayloadState}
    {labels : List DTR.PayloadLabel}
    (hSteps :
      DTR.PayloadSteps
        declaredMessageServer
        before
        labels
        after)
    (hBefore :
      DTR.PayloadBody.WellFormed
        declaredMessageServer
        before.activeBody) :
    DTR.PayloadBody.WellFormed
      declaredMessageServer
      after.activeBody := by

  induction hSteps with

  | refl state =>
      exact
        hBefore

  | cons headStep remainingSteps inductionHypothesis =>

      apply
        inductionHypothesis

      exact
        payloadStep_preserves_bodyWellFormed
          headStep
          hBefore

end DTR
end Relico
