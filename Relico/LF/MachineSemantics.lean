import Relico.LF.Semantics
import Relico.LF.DispatchSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
Labels for the combined generated-LF machine semantics.

A machine step is either reaction-body statement execution or logical
action dispatch.
-/
inductive MachineLabel where
  | statement :
      LF.Label →
      MachineLabel

  | dispatch :
      LF.PendingAction →
      MachineLabel
deriving Repr, DecidableEq, BEq, Inhabited

/--
Combined one-step semantics for the generated LF subset.
-/
inductive MachineStep
    (program : LF.Program) :
    LF.State →
    LF.MachineLabel →
    LF.State →
    Prop where

  | statement
      {stateBefore stateAfter : LF.State}
      {label : LF.Label}
      (hStep :
        LF.Step
          program
          stateBefore
          label
          stateAfter) :
      MachineStep
        program
        stateBefore
        (LF.MachineLabel.statement label)
        stateAfter

  | dispatch
      {stateBefore stateAfter : LF.State}
      {selectedAction : LF.PendingAction}
      (hDispatch :
        LF.DispatchStep
          program
          stateBefore
          selectedAction
          stateAfter) :
      MachineStep
        program
        stateBefore
        (LF.MachineLabel.dispatch selectedAction)
        stateAfter

end LF
end Relico
