import Relico.Correctness.PayloadStep
import Relico.DTR.PayloadMachine
import Relico.LF.PayloadMachine

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Pointwise correspondence between finite source and generated-LF
payload-scheduling traces.
-/
inductive PayloadTraceCorresponds :
    List DTR.PayloadLabel →
    List LF.PayloadLabel →
    Prop where

  | nil :
      PayloadTraceCorresponds
        []
        []

  | cons
      {sourceLabel : DTR.PayloadLabel}
      {targetLabel : LF.PayloadLabel}
      {sourceRemaining : List DTR.PayloadLabel}
      {targetRemaining : List LF.PayloadLabel}
      (headCorresponds :
        PayloadLabelCorresponds
          sourceLabel
          targetLabel)
      (tailCorresponds :
        PayloadTraceCorresponds
          sourceRemaining
          targetRemaining) :

      PayloadTraceCorresponds
        (sourceLabel :: sourceRemaining)
        (targetLabel :: targetRemaining)

/--
Corresponding payload traces have equal lengths.
-/
theorem PayloadTraceCorresponds.length_eq
    {sourceLabels : List DTR.PayloadLabel}
    {targetLabels : List LF.PayloadLabel}
    (hCorresponds :
      PayloadTraceCorresponds
        sourceLabels
        targetLabels) :
    sourceLabels.length =
      targetLabels.length := by

  induction hCorresponds with

  | nil =>
      rfl

  | cons headCorresponds tailCorresponds inductionHypothesis =>
      simp [
        inductionHypothesis
      ]

/--
Every finite source payload-scheduling execution has a matching
generated-LF execution with corresponding labels and final states.
-/
theorem payloadSteps_forward
    {declaredMessageServer : MsgName}
    {sourceBefore sourceAfter : DTR.PayloadState}
    {sourceLabels : List DTR.PayloadLabel}
    {targetBefore : LF.PayloadState}
    (hSourceSteps :
      DTR.PayloadSteps
        declaredMessageServer
        sourceBefore
        sourceLabels
        sourceAfter)
    (hStates :
      PayloadStateCorresponds
        sourceBefore
        targetBefore) :
    ∃ targetLabels targetAfter,
      LF.PayloadSteps
          (Translation.actionNameFor
            declaredMessageServer)
          targetBefore
          targetLabels
          targetAfter ∧
        PayloadTraceCorresponds
          sourceLabels
          targetLabels ∧
        PayloadStateCorresponds
          sourceAfter
          targetAfter := by

  induction hSourceSteps generalizing targetBefore with

  | refl sourceState =>

      exact
        ⟨[],
         targetBefore,
         LF.PayloadSteps.refl
           targetBefore,
         PayloadTraceCorresponds.nil,
         hStates⟩

  | cons headStep remainingSteps inductionHypothesis =>

      rcases
          payloadStep_forward
            hStates
            headStep
        with
          ⟨targetHeadLabel,
           targetMiddle,
           hTargetHead,
           hHeadLabels,
           hMiddleStates⟩

      rcases
          inductionHypothesis
            hMiddleStates
        with
          ⟨targetRemainingLabels,
           targetAfter,
           hTargetRemaining,
           hRemainingLabels,
           hFinalStates⟩

      exact
        ⟨targetHeadLabel :: targetRemainingLabels,
         targetAfter,
         LF.PayloadSteps.cons
           hTargetHead
           hTargetRemaining,
         PayloadTraceCorresponds.cons
           hHeadLabels
           hRemainingLabels,
         hFinalStates⟩

/--
Every finite generated-LF payload-scheduling execution beginning in
corresponding states can be reconstructed as a finite source execution.

Source payload-body well-formedness is preserved at every intermediate
state and is returned for the final source state.
-/
theorem payloadSteps_backward
    {declaredMessageServer : MsgName}
    {sourceBefore : DTR.PayloadState}
    {targetBefore targetAfter : LF.PayloadState}
    {targetLabels : List LF.PayloadLabel}
    (hTargetSteps :
      LF.PayloadSteps
        (Translation.actionNameFor
          declaredMessageServer)
        targetBefore
        targetLabels
        targetAfter)
    (hStates :
      PayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSourceWellFormed :
      DTR.PayloadBody.WellFormed
        declaredMessageServer
        sourceBefore.activeBody) :
    ∃ sourceLabels sourceAfter,
      DTR.PayloadSteps
          declaredMessageServer
          sourceBefore
          sourceLabels
          sourceAfter ∧
        PayloadTraceCorresponds
          sourceLabels
          targetLabels ∧
        PayloadStateCorresponds
          sourceAfter
          targetAfter ∧
        DTR.PayloadBody.WellFormed
          declaredMessageServer
          sourceAfter.activeBody := by

  induction hTargetSteps generalizing sourceBefore with

  | refl targetState =>

      exact
        ⟨[],
         sourceBefore,
         DTR.PayloadSteps.refl
           sourceBefore,
         PayloadTraceCorresponds.nil,
         hStates,
         hSourceWellFormed⟩

  | cons headStep remainingSteps inductionHypothesis =>

      rcases
          payloadStep_backward
            hSourceWellFormed
            hStates
            headStep
        with
          ⟨sourceHeadLabel,
           sourceMiddle,
           hSourceHead,
           hHeadLabels,
           hMiddleStates⟩

      have hMiddleWellFormed :
          DTR.PayloadBody.WellFormed
            declaredMessageServer
            sourceMiddle.activeBody :=

        DTR.payloadStep_preserves_bodyWellFormed
          hSourceHead
          hSourceWellFormed

      rcases
          inductionHypothesis
            hMiddleStates
            hMiddleWellFormed
        with
          ⟨sourceRemainingLabels,
           sourceAfter,
           hSourceRemaining,
           hRemainingLabels,
           hFinalStates,
           hFinalWellFormed⟩

      exact
        ⟨sourceHeadLabel :: sourceRemainingLabels,
         sourceAfter,
         DTR.PayloadSteps.cons
           hSourceHead
           hSourceRemaining,
         PayloadTraceCorresponds.cons
           hHeadLabels
           hRemainingLabels,
         hFinalStates,
         hFinalWellFormed⟩

end Correctness
end Relico
