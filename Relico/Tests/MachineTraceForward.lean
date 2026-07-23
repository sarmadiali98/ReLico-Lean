import Relico.Correctness.MachineTraceForward
import Relico.Tests.MachineTrace

set_option autoImplicit false

namespace Relico
namespace Tests

theorem assignmentForwardExecutionCompatible :
    Correctness.ForwardMachineExecutionCompatible
      validModel
      dtrAssignmentSource
      [
        DTR.MachineLabel.statement
          DTR.Label.internal
      ]
      dtrAssignmentTarget
      lfAssignmentSource := by

  apply
    Correctness.ForwardMachineExecutionCompatible.oneStep
      dtrAssignmentMachineStep
      assignmentSourceStateCorresponds

  simp [
    Correctness.ForwardMachineCompatible
  ]

theorem assignment_machine_trace_forward :
    ∃ targetLabels targetStateAfter,
      DTR.MachineSteps
          validModel
          dtrAssignmentSource
          [
            DTR.MachineLabel.statement
              DTR.Label.internal
          ]
          dtrAssignmentTarget ∧
      LF.MachineSteps
          (Translation.translateCore validModel)
          lfAssignmentSource
          targetLabels
          targetStateAfter ∧
      Correctness.MachineTraceCorresponds
          [
            DTR.MachineLabel.statement
              DTR.Label.internal
          ]
          targetLabels ∧
      Correctness.StateCorresponds
          dtrAssignmentTarget
          targetStateAfter := by

  exact
    Correctness.machineSteps_forward_of_compatible
      assignmentForwardExecutionCompatible

theorem dispatchForwardExecutionCompatible :
    Correctness.ForwardMachineExecutionCompatible
      validModel
      dtrDispatchSource
      [
        DTR.MachineLabel.dispatch
          dtrDispatchMessage
      ]
      dtrDispatchTarget
      lfDispatchSource := by

  apply
    Correctness.ForwardMachineExecutionCompatible.oneStep
      dtrDispatchMachineStep
      dispatchSourceStatesCorrespond

  simpa [
    Correctness.ForwardMachineCompatible,
    dtrDispatchTarget
  ] using
    singleDispatchForwardCompatible

theorem dispatch_machine_trace_forward :
    ∃ targetLabels targetStateAfter,
      DTR.MachineSteps
          validModel
          dtrDispatchSource
          [
            DTR.MachineLabel.dispatch
              dtrDispatchMessage
          ]
          dtrDispatchTarget ∧
      LF.MachineSteps
          (Translation.translateCore validModel)
          lfDispatchSource
          targetLabels
          targetStateAfter ∧
      Correctness.MachineTraceCorresponds
          [
            DTR.MachineLabel.dispatch
              dtrDispatchMessage
          ]
          targetLabels ∧
      Correctness.StateCorresponds
          dtrDispatchTarget
          targetStateAfter := by

  exact
    Correctness.machineSteps_forward_of_compatible
      dispatchForwardExecutionCompatible

end Tests
end Relico
