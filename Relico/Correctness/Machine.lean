import Relico.Correctness.Forward
import Relico.Correctness.Backward
import Relico.Correctness.DispatchForward
import Relico.DTR.MachineSemantics
import Relico.LF.MachineSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between combined machine labels.

Statement labels use the existing statement-label relation. Dispatch
labels use pending-message/action correspondence.
-/
inductive MachineLabelCorresponds :
    DTR.MachineLabel →
    LF.MachineLabel →
    Prop where

  | statement
      {sourceLabel : DTR.Label}
      {targetLabel : LF.Label}
      (hLabels :
        LabelCorresponds
          sourceLabel
          targetLabel) :
      MachineLabelCorresponds
        (DTR.MachineLabel.statement
          sourceLabel)
        (LF.MachineLabel.statement
          targetLabel)

  | dispatch
      {sourceMessage : DTR.PendingMessage}
      {targetAction : LF.PendingAction}
      (hPending :
        PendingCorresponds
          sourceMessage
          targetAction) :
      MachineLabelCorresponds
        (DTR.MachineLabel.dispatch
          sourceMessage)
        (LF.MachineLabel.dispatch
          targetAction)

/--
Compatibility required for forward machine simulation.

Statement execution requires no additional premise. Dispatch requires
the target occurrence aligned with the selected source message to be
eligible under the LF scheduler.
-/
def ForwardMachineCompatible
    (sourceLabel : DTR.MachineLabel)
    (sourceStateAfter : DTR.State)
    (targetState : LF.State) :
    Prop :=
  match sourceLabel with
  | DTR.MachineLabel.statement _ =>
      True
  | DTR.MachineLabel.dispatch selectedMessage =>
      ForwardDispatchCompatible
        selectedMessage
        sourceStateAfter.pendingMessages
        targetState

/--
Conditional forward simulation for one combined machine step.

Statement steps are always compatible. Dispatch steps require the
explicit LF scheduler-compatibility condition captured by
`ForwardMachineCompatible`.
-/
theorem machineStep_forward
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
    ∃ targetLabel targetStateAfter,
      LF.MachineStep
          (Translation.translateCore model)
          targetState
          targetLabel
          targetStateAfter ∧
      MachineLabelCorresponds
          sourceLabel
          targetLabel ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by

  cases hSourceStep with

  | statement hStatement =>
      rcases
          step_forward
            hStatement
            hStates
        with
          ⟨targetStatementLabel,
           targetStateAfter,
           hTargetStatement,
           hLabels,
           hFinalStates⟩

      exact
        ⟨LF.MachineLabel.statement
            targetStatementLabel,
         targetStateAfter,
         LF.MachineStep.statement
           hTargetStatement,
         MachineLabelCorresponds.statement
           hLabels,
         hFinalStates⟩

  | dispatch hDispatch =>
      have hDispatchCompatible := by
        simpa [ForwardMachineCompatible] using
          hCompatible

      rcases
          dispatch_forward_of_compatible
            hDispatch
            hStates
            hDispatchCompatible
        with
          ⟨selectedAction,
           targetStateAfter,
           hTargetDispatch,
           hPending,
           hFinalStates⟩

      exact
        ⟨LF.MachineLabel.dispatch
            selectedAction,
         targetStateAfter,
         LF.MachineStep.dispatch
           hTargetDispatch,
         MachineLabelCorresponds.dispatch
           hPending,
         hFinalStates⟩

/--
Unconditional backward simulation for one combined machine step.

Every generated-LF statement or dispatch transition from corresponding
states has a matching DTR machine transition.
-/
theorem machineStep_backward
    {model : DTR.Model}
    {sourceState : DTR.State}
    {targetState targetStateAfter : LF.State}
    {targetLabel : LF.MachineLabel}
    (hTargetStep :
      LF.MachineStep
        (Translation.translateCore model)
        targetState
        targetLabel
        targetStateAfter)
    (hStates :
      StateCorresponds
        sourceState
        targetState)
    (hSourceWellFormed :
      DTR.State.WellFormed
        model
        sourceState) :
    ∃ sourceLabel sourceStateAfter,
      DTR.MachineStep
          model
          sourceState
          sourceLabel
          sourceStateAfter ∧
      MachineLabelCorresponds
          sourceLabel
          targetLabel ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by

  cases hTargetStep with

  | statement hStatement =>
      rcases
          step_backward
            hStatement
            hStates
            hSourceWellFormed
        with
          ⟨sourceStatementLabel,
           sourceStateAfter,
           hSourceStatement,
           hLabels,
           hFinalStates⟩

      exact
        ⟨DTR.MachineLabel.statement
            sourceStatementLabel,
         sourceStateAfter,
         DTR.MachineStep.statement
           hSourceStatement,
         MachineLabelCorresponds.statement
           hLabels,
         hFinalStates⟩

  | dispatch hDispatch =>
      rcases
          dispatch_backward
            hDispatch
            hStates
            hSourceWellFormed
        with
          ⟨selectedMessage,
           sourceStateAfter,
           hSourceDispatch,
           hPending,
           hFinalStates⟩

      exact
        ⟨DTR.MachineLabel.dispatch
            selectedMessage,
         sourceStateAfter,
         DTR.MachineStep.dispatch
           hSourceDispatch,
         MachineLabelCorresponds.dispatch
           hPending,
         hFinalStates⟩

end Correctness
end Relico
