import Relico.Correctness.MachineInitialization
import Relico.Tests.Initialization
import Relico.Tests.MachineTraceForward

set_option autoImplicit false

namespace Relico
namespace Tests

def constructorAfterSend :
    DTR.State where
  currentTime := 0
  stateValue := 0
  pendingMessages := [
    {
      name := tickMessageName
      arrivalTime :=
        LogicalTime.after 0 ⟨1⟩
    }
  ]
  activeBody := []

def constructorMachineLabels :
    List DTR.MachineLabel := [
  DTR.MachineLabel.statement
    DTR.Label.internal,
  DTR.MachineLabel.statement
    (DTR.Label.send
      tickMessageName
      (LogicalTime.after 0 ⟨1⟩))
]

theorem constructorFirstMachineStep :
    DTR.MachineStep
      validModel
      (DTR.initialState validModel 0)
      (DTR.MachineLabel.statement
        DTR.Label.internal)
      constructorAfterAssignment := by
  exact
    DTR.MachineStep.statement
      constructorFirstStep

theorem constructorSecondStep :
    DTR.Step
      validModel
      constructorAfterAssignment
      (DTR.Label.send
        tickMessageName
        (LogicalTime.after 0 ⟨1⟩))
      constructorAfterSend := by
  simpa [
    constructorAfterAssignment,
    constructorAfterSend
  ] using
    (DTR.Step.selfSend
      (model := validModel)
      (currentTime := 0)
      (stateValue := 0)
      (pendingMessages := [])
      (targetMessage := tickMessageName)
      (delay := ⟨1⟩)
      (remaining := [])
      (hTarget := rfl))

theorem constructorSecondMachineStep :
    DTR.MachineStep
      validModel
      constructorAfterAssignment
      (DTR.MachineLabel.statement
        (DTR.Label.send
          tickMessageName
          (LogicalTime.after 0 ⟨1⟩)))
      constructorAfterSend := by
  exact
    DTR.MachineStep.statement
      constructorSecondStep

theorem constructorExecutionCompatible :
    Correctness.ForwardMachineExecutionCompatible
      validModel
      (DTR.initialState validModel 0)
      constructorMachineLabels
      constructorAfterSend
      (LF.initialState
        (Translation.translateCore validModel)
        0) := by

  have hInitialStates :
      Correctness.StateCorresponds
        (DTR.initialState validModel 0)
        (LF.initialState
          (Translation.translateCore validModel)
          0) :=
    Correctness.initialMachineStates_correspond
      validModel
      0

  have hFirstCompatible :
      Correctness.ForwardMachineCompatible
        (DTR.MachineLabel.statement
          DTR.Label.internal)
        constructorAfterAssignment
        (LF.initialState
          (Translation.translateCore validModel)
          0) := by
    simp [
      Correctness.ForwardMachineCompatible
    ]

  rcases
      Correctness.machineStep_forward
        constructorFirstMachineStep
        hInitialStates
        hFirstCompatible
    with
      ⟨firstTargetLabel,
       firstTargetState,
       hFirstTargetStep,
       hFirstLabels,
       hFirstStates⟩

  have hSecondCompatible :
      Correctness.ForwardMachineCompatible
        (DTR.MachineLabel.statement
          (DTR.Label.send
            tickMessageName
            (LogicalTime.after 0 ⟨1⟩)))
        constructorAfterSend
        firstTargetState := by
    simp [
      Correctness.ForwardMachineCompatible
    ]

  rcases
      Correctness.machineStep_forward
        constructorSecondMachineStep
        hFirstStates
        hSecondCompatible
    with
      ⟨secondTargetLabel,
       secondTargetState,
       hSecondTargetStep,
       hSecondLabels,
       hSecondStates⟩

  unfold constructorMachineLabels

  exact
    Correctness.ForwardMachineExecutionCompatible.cons
      constructorFirstMachineStep
      hInitialStates
      hFirstCompatible
      firstTargetLabel
      hFirstTargetStep
      hFirstLabels
      hFirstStates
      (Correctness.ForwardMachineExecutionCompatible.cons
        constructorSecondMachineStep
        hFirstStates
        hSecondCompatible
        secondTargetLabel
        hSecondTargetStep
        hSecondLabels
        hSecondStates
        (Correctness.ForwardMachineExecutionCompatible.refl
          constructorAfterSend
          secondTargetState
          hSecondStates))

theorem constructor_machine_execution_forward :
    ∃ targetLabels targetStateAfter,
      DTR.MachineSteps
          validModel
          (DTR.initialState validModel 0)
          constructorMachineLabels
          constructorAfterSend ∧
      LF.MachineSteps
          (Translation.translateCore validModel)
          (LF.initialState
            (Translation.translateCore validModel)
            0)
          targetLabels
          targetStateAfter ∧
      Correctness.MachineTraceCorresponds
          constructorMachineLabels
          targetLabels ∧
      Correctness.StateCorresponds
          constructorAfterSend
          targetStateAfter := by
  exact
    Correctness.initialMachineSteps_forward_of_compatible
      constructorExecutionCompatible

theorem generated_startup_execution_has_source_execution :
    ∃ targetLabels targetStateAfter sourceLabels sourceStateAfter,
      LF.MachineSteps
          (Translation.translateCore validModel)
          (LF.initialState
            (Translation.translateCore validModel)
            0)
          targetLabels
          targetStateAfter ∧
      DTR.MachineSteps
          validModel
          (DTR.initialState validModel 0)
          sourceLabels
          sourceStateAfter ∧
      Correctness.MachineTraceCorresponds
          sourceLabels
          targetLabels ∧
      Correctness.StateCorresponds
          sourceStateAfter
          targetStateAfter ∧
      DTR.State.WellFormed
          validModel
          sourceStateAfter := by

  rcases constructor_machine_execution_forward with
    ⟨targetLabels,
     targetStateAfter,
     hSourceForward,
     hTargetSteps,
     hForwardLabels,
     hForwardStates⟩

  rcases
      Correctness.initialMachineSteps_backward
        hTargetSteps
        validModel_wellFormed
    with
      ⟨sourceLabels,
       sourceStateAfter,
       hSourceSteps,
       hLabels,
       hStates,
       hWellFormed⟩

  exact
    ⟨targetLabels,
     targetStateAfter,
     sourceLabels,
     sourceStateAfter,
     hTargetSteps,
     hSourceSteps,
     hLabels,
     hStates,
     hWellFormed⟩

end Tests
end Relico
