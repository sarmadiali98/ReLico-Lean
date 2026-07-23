import Relico.Correctness.MachineInvariant
import Relico.Tests.MachineCorrectness

set_option autoImplicit false

namespace Relico
namespace Tests

theorem dtrDispatchTarget_runtimeWellFormed :
    DTR.State.WellFormed
      validModel
      dtrDispatchTarget := by

  exact
    Correctness.dtrDispatch_preserves_runtimeWellFormed
      dtrMessageDispatch
      validModel_wellFormed
      dtrDispatchSource_runtimeWellFormed

theorem assignmentMachineStep_preserves_runtimeWellFormed :
    DTR.State.WellFormed
      validModel
      dtrAssignmentTarget := by

  exact
    Correctness.dtrMachineStep_preserves_runtimeWellFormed
      dtrAssignmentMachineStep
      validModel_wellFormed
      dtrAssignmentSource_runtimeWellFormed

theorem dispatchMachineStep_preserves_runtimeWellFormed :
    DTR.State.WellFormed
      validModel
      dtrDispatchTarget := by

  exact
    Correctness.dtrMachineStep_preserves_runtimeWellFormed
      dtrDispatchMachineStep
      validModel_wellFormed
      dtrDispatchSource_runtimeWellFormed

end Tests
end Relico
