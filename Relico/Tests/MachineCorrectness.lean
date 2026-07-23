import Relico.Correctness.Machine
import Relico.Tests.BackwardSimulation
import Relico.Tests.DispatchForward
import Relico.Tests.MachineSemantics

set_option autoImplicit false

namespace Relico
namespace Tests

theorem assignmentTargetMachineStep :
    LF.MachineStep
      (Translation.translateCore validModel)
      lfAssignmentSource
      (LF.MachineLabel.statement
        LF.Label.internal)
      lfAssignmentTarget := by
  exact
    LF.MachineStep.statement
      assignmentTargetStep

theorem assignment_machine_step_forward :
    ∃ targetLabel targetStateAfter,
      LF.MachineStep
          (Translation.translateCore validModel)
          lfAssignmentSource
          targetLabel
          targetStateAfter ∧
      Correctness.MachineLabelCorresponds
          (DTR.MachineLabel.statement
            DTR.Label.internal)
          targetLabel ∧
      Correctness.StateCorresponds
          dtrAssignmentTarget
          targetStateAfter := by

  apply
    Correctness.machineStep_forward
      dtrAssignmentMachineStep
      assignmentSourceStateCorresponds

  simp [
    Correctness.ForwardMachineCompatible
  ]

theorem assignment_machine_step_backward :
    ∃ sourceLabel sourceStateAfter,
      DTR.MachineStep
          validModel
          dtrAssignmentSource
          sourceLabel
          sourceStateAfter ∧
      Correctness.MachineLabelCorresponds
          sourceLabel
          (LF.MachineLabel.statement
            LF.Label.internal) ∧
      Correctness.StateCorresponds
          sourceStateAfter
          lfAssignmentTarget := by

  exact
    Correctness.machineStep_backward
      assignmentTargetMachineStep
      assignmentSourceStateCorresponds
      dtrAssignmentSource_runtimeWellFormed

theorem dispatch_machine_step_forward :
    ∃ targetLabel targetStateAfter,
      LF.MachineStep
          (Translation.translateCore validModel)
          lfDispatchSource
          targetLabel
          targetStateAfter ∧
      Correctness.MachineLabelCorresponds
          (DTR.MachineLabel.dispatch
            dtrDispatchMessage)
          targetLabel ∧
      Correctness.StateCorresponds
          dtrDispatchTarget
          targetStateAfter := by

  apply
    Correctness.machineStep_forward
      dtrDispatchMachineStep
      dispatchSourceStatesCorrespond

  simpa [
    Correctness.ForwardMachineCompatible,
    dtrDispatchTarget
  ] using
    singleDispatchForwardCompatible

theorem generatedLFDispatchMachineStep :
    LF.MachineStep
      (Translation.translateCore validModel)
      lfDispatchSource
      (LF.MachineLabel.dispatch
        lfDispatchAction)
      generatedLFDispatchTarget := by

  exact
    LF.MachineStep.dispatch
      generatedLFDispatchStep

theorem dispatch_machine_step_backward :
    ∃ sourceLabel sourceStateAfter,
      DTR.MachineStep
          validModel
          dtrDispatchSource
          sourceLabel
          sourceStateAfter ∧
      Correctness.MachineLabelCorresponds
          sourceLabel
          (LF.MachineLabel.dispatch
            lfDispatchAction) ∧
      Correctness.StateCorresponds
          sourceStateAfter
          generatedLFDispatchTarget := by

  exact
    Correctness.machineStep_backward
      generatedLFDispatchMachineStep
      dispatchSourceStatesCorrespond
      dtrDispatchSource_runtimeWellFormed

end Tests
end Relico
