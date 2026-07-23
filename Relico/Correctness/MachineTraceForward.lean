import Relico.Correctness.MachineTrace

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compatibility evidence for a finite forward machine execution.

At every source step, the evidence records:

- correspondence of the states before the step;
- the required local forward-compatibility premise;
- a matching generated-LF transition;
- correspondence of the labels and resulting states;
- compatibility evidence for the remaining execution.

This is proposition-valued because it is used only to establish
execution correspondence.
-/
inductive ForwardMachineExecutionCompatible
    (model : DTR.Model) :
    DTR.State →
    List DTR.MachineLabel →
    DTR.State →
    LF.State →
    Prop where

  | refl
      (sourceState : DTR.State)
      (targetState : LF.State)
      (hStates :
        StateCorresponds
          sourceState
          targetState) :
      ForwardMachineExecutionCompatible
        model
        sourceState
        []
        sourceState
        targetState

  | cons
      {sourceState sourceStateMiddle sourceStateAfter : DTR.State}
      {sourceLabel : DTR.MachineLabel}
      {sourceRemainingLabels : List DTR.MachineLabel}
      {targetState targetStateMiddle : LF.State}
      (hSourceStep :
        DTR.MachineStep
          model
          sourceState
          sourceLabel
          sourceStateMiddle)
      (hStates :
        StateCorresponds
          sourceState
          targetState)
      (hCompatible :
        ForwardMachineCompatible
          sourceLabel
          sourceStateMiddle
          targetState)
      (targetLabel : LF.MachineLabel)
      (hTargetStep :
        LF.MachineStep
          (Translation.translateCore model)
          targetState
          targetLabel
          targetStateMiddle)
      (hLabels :
        MachineLabelCorresponds
          sourceLabel
          targetLabel)
      (hMiddleStates :
        StateCorresponds
          sourceStateMiddle
          targetStateMiddle)
      (hRemaining :
        ForwardMachineExecutionCompatible
          model
          sourceStateMiddle
          sourceRemainingLabels
          sourceStateAfter
          targetStateMiddle) :
      ForwardMachineExecutionCompatible
        model
        sourceState
        (sourceLabel :: sourceRemainingLabels)
        sourceStateAfter
        targetState

namespace ForwardMachineExecutionCompatible

/--
Construct compatibility evidence for one source machine transition.

The matching target transition is supplied by the established
machine-level forward-simulation theorem.
-/
theorem oneStep
    {model : DTR.Model}
    {sourceState sourceStateAfter : DTR.State}
    {sourceLabel : DTR.MachineLabel}
    {targetState : LF.State}
    (hSourceStep :
      DTR.MachineStep
        model
        sourceState
        sourceLabel
        sourceStateAfter)
    (hStates :
      StateCorresponds
        sourceState
        targetState)
    (hCompatible :
      ForwardMachineCompatible
        sourceLabel
        sourceStateAfter
        targetState) :
    ForwardMachineExecutionCompatible
      model
      sourceState
      [sourceLabel]
      sourceStateAfter
      targetState := by

  rcases
      machineStep_forward
        hSourceStep
        hStates
        hCompatible
    with
      ⟨targetLabel,
       targetStateAfter,
       hTargetStep,
       hLabels,
       hFinalStates⟩

  exact
    ForwardMachineExecutionCompatible.cons
      hSourceStep
      hStates
      hCompatible
      targetLabel
      hTargetStep
      hLabels
      hFinalStates
      (ForwardMachineExecutionCompatible.refl
        sourceStateAfter
        targetStateAfter
        hFinalStates)

end ForwardMachineExecutionCompatible

/--
Conditional finite forward machine simulation.

Finite compatibility evidence yields finite DTR and generated-LF
executions with pointwise-corresponding machine labels and
corresponding final states.
-/
theorem machineSteps_forward_of_compatible
    {model : DTR.Model}
    {sourceState sourceStateAfter : DTR.State}
    {sourceLabels : List DTR.MachineLabel}
    {targetState : LF.State}
    (hCompatible :
      ForwardMachineExecutionCompatible
        model
        sourceState
        sourceLabels
        sourceStateAfter
        targetState) :
    ∃ targetLabels targetStateAfter,
      DTR.MachineSteps
          model
          sourceState
          sourceLabels
          sourceStateAfter ∧
      LF.MachineSteps
          (Translation.translateCore model)
          targetState
          targetLabels
          targetStateAfter ∧
      MachineTraceCorresponds
          sourceLabels
          targetLabels ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by

  induction hCompatible with

  | refl sourceState targetState hStates =>
      exact
        ⟨[],
         targetState,
         DTR.MachineSteps.refl
           sourceState,
         LF.MachineSteps.refl
           targetState,
         MachineTraceCorresponds.nil,
         hStates⟩

  | cons
      hSourceStep
      hStates
      hStepCompatible
      targetLabel
      hTargetStep
      hLabels
      hMiddleStates
      hRemaining
      inductionHypothesis =>

      rcases inductionHypothesis with
        ⟨targetRemainingLabels,
         targetStateAfter,
         hSourceRemainingSteps,
         hTargetRemainingSteps,
         hRemainingLabels,
         hFinalStates⟩

      exact
        ⟨targetLabel :: targetRemainingLabels,
         targetStateAfter,
         DTR.MachineSteps.cons
           hSourceStep
           hSourceRemainingSteps,
         LF.MachineSteps.cons
           hTargetStep
           hTargetRemainingSteps,
         MachineTraceCorresponds.cons
           hLabels
           hRemainingLabels,
         hFinalStates⟩

end Correctness
end Relico
