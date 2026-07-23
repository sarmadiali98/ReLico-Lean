import Relico.Correctness.DispatchInvariant
import Relico.DTR.MachineSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Every combined DTR machine step preserves runtime well-formedness for a
well-formed source model.
-/
theorem dtrMachineStep_preserves_runtimeWellFormed
    {model : DTR.Model}
    {stateBefore stateAfter : DTR.State}
    {label : DTR.MachineLabel}
    (hStep :
      DTR.MachineStep
        model
        stateBefore
        label
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

  cases hStep with

  | statement hStatement =>
      exact
        dtrStep_preserves_runtimeWellFormed
          hStatement
          hState

  | dispatch hDispatch =>
      exact
        dtrDispatch_preserves_runtimeWellFormed
          hDispatch
          hModel
          hState

end Correctness
end Relico
