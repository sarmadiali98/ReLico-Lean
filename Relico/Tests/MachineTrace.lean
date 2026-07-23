import Relico.Correctness.MachineTrace
import Relico.Tests.MachineInvariant

set_option autoImplicit false

namespace Relico
namespace Tests

theorem assignmentTargetMachineTrace :
    LF.MachineSteps
      (Translation.translateCore validModel)
      lfAssignmentSource
      [
        LF.MachineLabel.statement
          LF.Label.internal
      ]
      lfAssignmentTarget := by

  exact
    LF.MachineSteps.cons
      assignmentTargetMachineStep
      (LF.MachineSteps.refl
        lfAssignmentTarget)

theorem assignment_machine_trace_backward :
    ∃ sourceLabels sourceStateAfter,
      DTR.MachineSteps
          validModel
          dtrAssignmentSource
          sourceLabels
          sourceStateAfter ∧
      Correctness.MachineTraceCorresponds
          sourceLabels
          [
            LF.MachineLabel.statement
              LF.Label.internal
          ] ∧
      Correctness.StateCorresponds
          sourceStateAfter
          lfAssignmentTarget ∧
      DTR.State.WellFormed
          validModel
          sourceStateAfter := by

  exact
    Correctness.machineSteps_backward
      assignmentTargetMachineTrace
      assignmentSourceStateCorresponds
      validModel_wellFormed
      dtrAssignmentSource_runtimeWellFormed

theorem dispatchTargetMachineTrace :
    LF.MachineSteps
      (Translation.translateCore validModel)
      lfDispatchSource
      [
        LF.MachineLabel.dispatch
          lfDispatchAction
      ]
      generatedLFDispatchTarget := by

  exact
    LF.MachineSteps.cons
      generatedLFDispatchMachineStep
      (LF.MachineSteps.refl
        generatedLFDispatchTarget)

theorem dispatch_machine_trace_backward :
    ∃ sourceLabels sourceStateAfter,
      DTR.MachineSteps
          validModel
          dtrDispatchSource
          sourceLabels
          sourceStateAfter ∧
      Correctness.MachineTraceCorresponds
          sourceLabels
          [
            LF.MachineLabel.dispatch
              lfDispatchAction
          ] ∧
      Correctness.StateCorresponds
          sourceStateAfter
          generatedLFDispatchTarget ∧
      DTR.State.WellFormed
          validModel
          sourceStateAfter := by

  exact
    Correctness.machineSteps_backward
      dispatchTargetMachineTrace
      dispatchSourceStatesCorrespond
      validModel_wellFormed
      dtrDispatchSource_runtimeWellFormed

end Tests
end Relico
