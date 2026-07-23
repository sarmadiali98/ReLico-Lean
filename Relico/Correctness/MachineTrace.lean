import Relico.Correctness.Machine
import Relico.Correctness.MachineInvariant
import Relico.DTR.MachineTraceSemantics
import Relico.LF.MachineTraceSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Pointwise correspondence between finite DTR and generated-LF machine
traces.
-/
inductive MachineTraceCorresponds :
    List DTR.MachineLabel →
    List LF.MachineLabel →
    Prop where

  | nil :
      MachineTraceCorresponds [] []

  | cons
      {sourceLabel : DTR.MachineLabel}
      {targetLabel : LF.MachineLabel}
      {sourceRemaining : List DTR.MachineLabel}
      {targetRemaining : List LF.MachineLabel}
      (headCorresponds :
        MachineLabelCorresponds
          sourceLabel
          targetLabel)
      (tailCorresponds :
        MachineTraceCorresponds
          sourceRemaining
          targetRemaining) :
      MachineTraceCorresponds
        (sourceLabel :: sourceRemaining)
        (targetLabel :: targetRemaining)

/--
Finite DTR machine executions preserve runtime well-formedness for a
well-formed model.
-/
theorem dtrMachineSteps_preserve_runtimeWellFormed
    {model : DTR.Model}
    {stateBefore stateAfter : DTR.State}
    {labels : List DTR.MachineLabel}
    (hSteps :
      DTR.MachineSteps
        model
        stateBefore
        labels
        stateAfter)
    (hModel :
      DTR.Model.WellFormed model)
    (hState :
      DTR.State.WellFormed
        model
        stateBefore) :
    DTR.State.WellFormed
      model
      stateAfter := by

  induction hSteps with

  | refl state =>
      exact hState

  | cons headStep remainingSteps inductionHypothesis =>
      have hMiddleWellFormed :
          DTR.State.WellFormed
            model
            _ :=
        dtrMachineStep_preserves_runtimeWellFormed
          headStep
          hModel
          hState

      exact
        inductionHypothesis
          hMiddleWellFormed

/--
Unconditional backward simulation for finite combined-machine
executions.

Every finite generated-LF execution beginning in corresponding states
has a finite DTR execution with corresponding machine labels and final
states. Source runtime well-formedness is preserved throughout.
-/
theorem machineSteps_backward
    {model : DTR.Model}
    {sourceState : DTR.State}
    {targetState targetStateAfter : LF.State}
    {targetLabels : List LF.MachineLabel}
    (hTargetSteps :
      LF.MachineSteps
        (Translation.translateCore model)
        targetState
        targetLabels
        targetStateAfter)
    (hStates :
      StateCorresponds
        sourceState
        targetState)
    (hModel :
      DTR.Model.WellFormed model)
    (hSourceWellFormed :
      DTR.State.WellFormed
        model
        sourceState) :
    ∃ sourceLabels sourceStateAfter,
      DTR.MachineSteps
          model
          sourceState
          sourceLabels
          sourceStateAfter ∧
      MachineTraceCorresponds
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
         DTR.MachineSteps.refl sourceState,
         MachineTraceCorresponds.nil,
         hStates,
         hSourceWellFormed⟩

  | cons headStep remainingSteps inductionHypothesis =>
      rcases
          machineStep_backward
            headStep
            hStates
            hSourceWellFormed
        with
          ⟨sourceLabel,
           sourceStateMiddle,
           hSourceStep,
           hLabelCorresponds,
           hMiddleStates⟩

      have hMiddleWellFormed :
          DTR.State.WellFormed
            model
            sourceStateMiddle :=
        dtrMachineStep_preserves_runtimeWellFormed
          hSourceStep
          hModel
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
         DTR.MachineSteps.cons
           hSourceStep
           hSourceRemainingSteps,
         MachineTraceCorresponds.cons
           hLabelCorresponds
           hRemainingLabels,
         hFinalStates,
         hFinalWellFormed⟩

end Correctness
end Relico
