import Relico.LF.Scheduling
import Relico.LF.Syntax

set_option autoImplicit false

namespace Relico
namespace LF

/--
Dispatch transition for a pending generated-LF logical action.

Dispatch is enabled only when the currently active body is empty. The
rule removes one concrete earliest action occurrence, advances to its
complete LF tag, and loads the generated message-reaction body.
-/
inductive DispatchStep
    (program : LF.Program) :
    LF.State →
    LF.PendingAction →
    LF.State →
    Prop where

  | fire
      (currentTag : Tag)
      (stateValue : Int)
      (pendingActions remainingActions : ActionQueue)
      (selectedAction : PendingAction)
      (hRemoved :
        Occurrence.RemovesOne
          selectedAction
          pendingActions
          remainingActions)
      (hEarliest :
        LF.IsEarliest
          selectedAction
          pendingActions)
      (hNotPast :
        LF.Tag.PrecedesOrEqual
          currentTag
          selectedAction.tag)
      (hTarget :
        selectedAction.name =
          program.reactor.logicalAction) :
      DispatchStep
        program
        {
          currentTag := currentTag
          stateValue := stateValue
          pendingActions := pendingActions
          activeBody := []
        }
        selectedAction
        {
          currentTag :=
            selectedAction.tag
          stateValue := stateValue
          pendingActions := remainingActions
          activeBody :=
            program.reactor.messageReaction.body
        }

end LF
end Relico
