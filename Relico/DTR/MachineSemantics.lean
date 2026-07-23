import Relico.DTR.Semantics
import Relico.DTR.DispatchSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Labels for the combined DTR machine semantics.

A machine step is either an active-body statement step or a pending
message dispatch.
-/
inductive MachineLabel where
  | statement :
      DTR.Label →
      MachineLabel

  | dispatch :
      DTR.PendingMessage →
      MachineLabel
deriving Repr, DecidableEq, BEq, Inhabited

/--
Combined one-step DTR semantics.

Statement execution and message dispatch remain separate rules, but
both are exposed through one machine-level transition relation.
-/
inductive MachineStep
    (model : DTR.Model) :
    DTR.State →
    DTR.MachineLabel →
    DTR.State →
    Prop where

  | statement
      {stateBefore stateAfter : DTR.State}
      {label : DTR.Label}
      (hStep :
        DTR.Step
          model
          stateBefore
          label
          stateAfter) :
      MachineStep
        model
        stateBefore
        (DTR.MachineLabel.statement label)
        stateAfter

  | dispatch
      {stateBefore stateAfter : DTR.State}
      {selectedMessage : DTR.PendingMessage}
      (hDispatch :
        DTR.DispatchStep
          model
          stateBefore
          selectedMessage
          stateAfter) :
      MachineStep
        model
        stateBefore
        (DTR.MachineLabel.dispatch selectedMessage)
        stateAfter

end DTR
end Relico
