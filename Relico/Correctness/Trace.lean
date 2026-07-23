import Relico.Correctness.Forward
import Relico.Correctness.Backward
import Relico.Correctness.RuntimeInvariant
import Relico.DTR.TraceSemantics
import Relico.LF.TraceSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Pointwise correspondence between finite DTR and generated-LF traces.
-/
inductive TraceCorresponds :
    List DTR.Label →
    List LF.Label →
    Prop where

  | nil :
      TraceCorresponds [] []

  | cons
      {sourceLabel : DTR.Label}
      {targetLabel : LF.Label}
      {sourceRemaining : List DTR.Label}
      {targetRemaining : List LF.Label}
      (headCorresponds :
        LabelCorresponds
          sourceLabel
          targetLabel)
      (tailCorresponds :
        TraceCorresponds
          sourceRemaining
          targetRemaining) :
      TraceCorresponds
        (sourceLabel :: sourceRemaining)
        (targetLabel :: targetRemaining)

/--
Finite-execution forward simulation.

Every finite DTR execution beginning in corresponding states has a
finite generated-LF execution with corresponding labels and a
corresponding final state.
-/
theorem steps_forward
    {model : DTR.Model}
    {sourceState sourceStateAfter : DTR.State}
    {sourceLabels : List DTR.Label}
    {targetState : LF.State}
    (hSourceSteps :
      DTR.Steps
        model
        sourceState
        sourceLabels
        sourceStateAfter)
    (hStates :
      StateCorresponds
        sourceState
        targetState) :
    ∃ targetLabels targetStateAfter,
      LF.Steps
          (Translation.translateCore model)
          targetState
          targetLabels
          targetStateAfter ∧
      TraceCorresponds
          sourceLabels
          targetLabels ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by

  induction hSourceSteps generalizing targetState with

  | refl sourceState =>
      exact
        ⟨[],
         targetState,
         LF.Steps.refl targetState,
         TraceCorresponds.nil,
         hStates⟩

  | cons headStep remainingSteps inductionHypothesis =>
      rcases
          step_forward
            headStep
            hStates
        with
          ⟨targetLabel,
           targetStateMiddle,
           hTargetStep,
           hLabel,
           hMiddleStates⟩

      rcases
          inductionHypothesis
            hMiddleStates
        with
          ⟨targetRemainingLabels,
           targetStateAfter,
           hTargetRemainingSteps,
           hRemainingLabels,
           hFinalStates⟩

      exact
        ⟨targetLabel :: targetRemainingLabels,
         targetStateAfter,
         LF.Steps.cons
           hTargetStep
           hTargetRemainingSteps,
         TraceCorresponds.cons
           hLabel
           hRemainingLabels,
         hFinalStates⟩

/--
Finite-execution backward simulation.

Every finite execution of the generated LF statement subset beginning
in corresponding states has a matching finite DTR execution. The final
states correspond, and DTR runtime well-formedness is preserved.
-/
theorem steps_backward
    {model : DTR.Model}
    {sourceState : DTR.State}
    {targetState targetStateAfter : LF.State}
    {targetLabels : List LF.Label}
    (hTargetSteps :
      LF.Steps
        (Translation.translateCore model)
        targetState
        targetLabels
        targetStateAfter)
    (hStates :
      StateCorresponds
        sourceState
        targetState)
    (hSourceWellFormed :
      DTR.State.WellFormed
        model
        sourceState) :
    ∃ sourceLabels sourceStateAfter,
      DTR.Steps
          model
          sourceState
          sourceLabels
          sourceStateAfter ∧
      TraceCorresponds
          sourceLabels
          targetLabels ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter ∧
      DTR.State.WellFormed
          model
          sourceStateAfter := by

  induction hTargetSteps generalizing sourceState with

  | refl targetState =>
      exact
        ⟨[],
         sourceState,
         DTR.Steps.refl sourceState,
         TraceCorresponds.nil,
         hStates,
         hSourceWellFormed⟩

  | cons headStep remainingSteps inductionHypothesis =>
      rcases
          step_backward
            headStep
            hStates
            hSourceWellFormed
        with
          ⟨sourceLabel,
           sourceStateMiddle,
           hSourceStep,
           hLabel,
           hMiddleStates⟩

      have hMiddleWellFormed :
          DTR.State.WellFormed
            model
            sourceStateMiddle :=
        dtrStep_preserves_runtimeWellFormed
          hSourceStep
          hSourceWellFormed

      rcases
          inductionHypothesis
            hMiddleStates
            hMiddleWellFormed
        with
          ⟨sourceRemainingLabels,
           sourceStateAfter,
           hSourceRemainingSteps,
           hRemainingLabels,
           hFinalStates,
           hFinalWellFormed⟩

      exact
        ⟨sourceLabel :: sourceRemainingLabels,
         sourceStateAfter,
         DTR.Steps.cons
           hSourceStep
           hSourceRemainingSteps,
         TraceCorresponds.cons
           hLabel
           hRemainingLabels,
         hFinalStates,
         hFinalWellFormed⟩

end Correctness
end Relico
