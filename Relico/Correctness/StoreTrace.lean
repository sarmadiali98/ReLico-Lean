import Relico.Correctness.StoreBackward
import Relico.Correctness.StoreForward
import Relico.DTR.StoreTrace
import Relico.LF.StoreTrace

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Pointwise correspondence between source and target transition-label
sequences.
-/
inductive LabelTraceCorresponds :
    List DTR.Label →
    List LF.Label →
    Prop where

  | nil :
      LabelTraceCorresponds
        []
        []

  | cons
      {sourceLabel : DTR.Label}
      {targetLabel : LF.Label}
      {sourceLabels : List DTR.Label}
      {targetLabels : List LF.Label}
      (hHead :
        LabelCorresponds
          sourceLabel
          targetLabel)
      (hTail :
        LabelTraceCorresponds
          sourceLabels
          targetLabels) :

      LabelTraceCorresponds
        (sourceLabel :: sourceLabels)
        (targetLabel :: targetLabels)

/--
Forward simulation of arbitrary finite DTR store statement traces.

Every source trace has a generated-LF trace with pointwise
corresponding labels and a corresponding final runtime state.
-/
theorem store_trace_forward
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {sourceInitial sourceFinal : DTR.StoreState}
    {sourceLabels : List DTR.Label}
    {targetInitial : LF.StoreState}
    (hSourceTrace :
      DTR.StoreTrace
        declaredVariables
        messageServer
        sourceInitial
        sourceLabels
        sourceFinal)
    (hInitialStates :
      StoreStateCorresponds
        sourceInitial
        targetInitial) :
    ∃ targetLabels targetFinal,
      LF.StoreTrace
          declaredVariables
          (Translation.actionNameFor
            messageServer)
          targetInitial
          targetLabels
          targetFinal ∧
      LabelTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceFinal
        targetFinal := by

  induction hSourceTrace generalizing targetInitial with

  | refl state =>
      exact
        ⟨[],
         targetInitial,
         LF.StoreTrace.refl
           targetInitial,
         LabelTraceCorresponds.nil,
         hInitialStates⟩

  | step hFirstStep hRemainingTrace inductionHypothesis =>
      rcases
          store_step_forward
            hFirstStep
            hInitialStates
        with
          ⟨targetLabel,
           targetMiddle,
           hTargetStep,
           hFirstLabel,
           hMiddleStates⟩

      rcases
          inductionHypothesis
            hMiddleStates
        with
          ⟨targetRemainingLabels,
           targetFinal,
           hTargetRemainingTrace,
           hRemainingLabels,
           hFinalStates⟩

      exact
        ⟨targetLabel :: targetRemainingLabels,
         targetFinal,
         LF.StoreTrace.step
           hTargetStep
           hTargetRemainingTrace,
         LabelTraceCorresponds.cons
           hFirstLabel
           hRemainingLabels,
         hFinalStates⟩

/--
Backward simulation of arbitrary finite generated-LF store statement
traces.

Source-body well-formedness is propagated through each recovered DTR
step, allowing the one-step backward theorem to be applied repeatedly.
-/
theorem store_trace_backward
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {targetInitial targetFinal : LF.StoreState}
    {targetLabels : List LF.Label}
    {sourceInitial : DTR.StoreState}
    (hTargetTrace :
      LF.StoreTrace
        declaredVariables
        (Translation.actionNameFor
          messageServer)
        targetInitial
        targetLabels
        targetFinal)
    (hInitialStates :
      StoreStateCorresponds
        sourceInitial
        targetInitial)
    (hInitialBodyWellFormed :
      DTR.Body.StoreWellFormed
        declaredVariables
        messageServer
        sourceInitial.activeBody) :
    ∃ sourceLabels sourceFinal,
      DTR.StoreTrace
          declaredVariables
          messageServer
          sourceInitial
          sourceLabels
          sourceFinal ∧
      LabelTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceFinal
        targetFinal := by

  induction hTargetTrace generalizing sourceInitial with

  | refl state =>
      exact
        ⟨[],
         sourceInitial,
         DTR.StoreTrace.refl
           sourceInitial,
         LabelTraceCorresponds.nil,
         hInitialStates⟩

  | step hFirstStep hRemainingTrace inductionHypothesis =>
      rcases
          store_step_backward
            hFirstStep
            hInitialStates
            hInitialBodyWellFormed
        with
          ⟨sourceLabel,
           sourceMiddle,
           hSourceStep,
           hFirstLabel,
           hMiddleStates⟩

      have hMiddleBodyWellFormed :
          DTR.Body.StoreWellFormed
            declaredVariables
            messageServer
            sourceMiddle.activeBody :=

        DTR.StoreStep.preserves_body_storeWellFormed
          hSourceStep
          hInitialBodyWellFormed

      rcases
          inductionHypothesis
            hMiddleStates
            hMiddleBodyWellFormed
        with
          ⟨sourceRemainingLabels,
           sourceFinal,
           hSourceRemainingTrace,
           hRemainingLabels,
           hFinalStates⟩

      exact
        ⟨sourceLabel :: sourceRemainingLabels,
         sourceFinal,
         DTR.StoreTrace.step
           hSourceStep
           hSourceRemainingTrace,
         LabelTraceCorresponds.cons
           hFirstLabel
           hRemainingLabels,
         hFinalStates⟩

end Correctness
end Relico
