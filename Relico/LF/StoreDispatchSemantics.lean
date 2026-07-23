import Relico.LF.Scheduling
import Relico.LF.StoreState

set_option autoImplicit false

namespace Relico
namespace LF

/--
Dispatch semantics for a pending generated-LF logical action over a
finite reactor-state store.

Dispatch removes one concrete earliest action occurrence, advances to
its complete LF tag, and loads the generated message-reaction body.
-/
inductive StoreDispatchStep
    (logicalAction : ActionName)
    (messageReactionBody : LF.Body) :
    LF.StoreState →
    LF.PendingAction →
    LF.StoreState →
    Prop where

  | fire
      (currentTag : Tag)
      (stateStore : StateStore)
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
          logicalAction) :

      StoreDispatchStep
        logicalAction
        messageReactionBody
        {
          currentTag :=
            currentTag

          stateStore :=
            stateStore

          pendingActions :=
            pendingActions

          activeBody :=
            []
        }
        selectedAction
        {
          currentTag :=
            selectedAction.tag

          stateStore :=
            stateStore

          pendingActions :=
            remainingActions

          activeBody :=
            messageReactionBody
        }

namespace StoreDispatchStep

/--
Dispatch preserves coverage because it leaves the complete reactor
state store unchanged.
-/
theorem preserves_coverage
    {logicalAction : ActionName}
    {messageReactionBody : LF.Body}
    {declaredVariables : List VarName}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.StoreDispatchStep
        logicalAction
        messageReactionBody
        before
        selectedAction
        after)
    (hCoverage :
      LF.StoreState.Covers
        declaredVariables
        before) :
    LF.StoreState.Covers
      declaredVariables
      after := by

  cases hDispatch

  exact hCoverage

end StoreDispatchStep
end LF
end Relico
