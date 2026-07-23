import Relico.DTR.MachineSemantics
import Relico.LF.MachineSemantics
import Relico.Tests.SmallStep
import Relico.Tests.DispatchSemantics

set_option autoImplicit false

namespace Relico
namespace Tests

theorem dtrAssignmentMachineStep :
    DTR.MachineStep
      validModel
      dtrAssignmentSource
      (DTR.MachineLabel.statement
        DTR.Label.internal)
      dtrAssignmentTarget := by

  apply DTR.MachineStep.statement

  exact
    DTR.Step.assign
      (model := validModel)
      (currentTime := 2)
      (stateValue := 5)
      (pendingMessages := [])
      (target := stateVariableName)
      (expression := .intLiteral 7)
      (remaining := [])
      (hTarget := rfl)

theorem dtrDispatchMachineStep :
    DTR.MachineStep
      validModel
      dtrDispatchSource
      (DTR.MachineLabel.dispatch
        dtrDispatchMessage)
      dtrDispatchTarget := by

  exact
    DTR.MachineStep.dispatch
      dtrMessageDispatch

theorem lfAssignmentMachineStep :
    LF.MachineStep
      expectedProgram
      lfAssignmentSource
      (LF.MachineLabel.statement
        LF.Label.internal)
      lfAssignmentTarget := by

  apply LF.MachineStep.statement

  exact
    LF.Step.assign
      (program := expectedProgram)
      (currentTag := initialLFTag)
      (stateValue := 5)
      (pendingActions := [])
      (target := stateVariableName)
      (expression := .intLiteral 7)
      (remaining := [])
      (hTarget := rfl)

theorem lfDispatchMachineStep :
    LF.MachineStep
      expectedProgram
      lfDispatchSource
      (LF.MachineLabel.dispatch
        lfDispatchAction)
      lfDispatchTarget := by

  exact
    LF.MachineStep.dispatch
      lfActionDispatch

end Tests
end Relico
