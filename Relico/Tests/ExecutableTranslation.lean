import Relico.Correctness.ExecutableTranslation
import Relico.Tests.MachineInitialization
import Relico.Tests.Translation

set_option autoImplicit false

namespace Relico
namespace Tests

theorem validExecutableTranslation :
    Translation.translate validModel =
      Except.ok expectedProgram := by
  rfl

theorem returnedProgramIsWellFormed :
    LF.Program.WellFormed
      expectedProgram := by
  exact
    Correctness.executableTranslation_wellFormed
      validModel_wellFormed
      validExecutableTranslation

theorem expectedProgramStartupRefl :
    LF.MachineSteps
      expectedProgram
      (LF.initialState
        expectedProgram
        0)
      []
      (LF.initialState
        expectedProgram
        0) := by
  exact
    LF.MachineSteps.refl
      (LF.initialState
        expectedProgram
        0)

theorem executable_program_refl_execution_backward :
    ∃ sourceLabels sourceStateAfter,
      DTR.MachineSteps
          validModel
          (DTR.initialState
            validModel
            0)
          sourceLabels
          sourceStateAfter ∧
      Correctness.MachineTraceCorresponds
          sourceLabels
          [] ∧
      Correctness.StateCorresponds
          sourceStateAfter
          (LF.initialState
            expectedProgram
            0) ∧
      DTR.State.WellFormed
          validModel
          sourceStateAfter := by

  exact
    Correctness.executableTranslation_initialMachineSteps_backward
      validExecutableTranslation
      expectedProgramStartupRefl
      validModel_wellFormed

theorem validCoreExecutableTranslation :
    Translation.translate validModel =
      Except.ok
        (Translation.translateCore validModel) := by
  rfl

theorem executable_constructor_execution_forward :
    ∃ targetLabels targetStateAfter,
      DTR.MachineSteps
          validModel
          (DTR.initialState
            validModel
            0)
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
    Correctness.executableTranslation_initialMachineSteps_forward
      validCoreExecutableTranslation
      constructorExecutionCompatible

end Tests
end Relico
