import Relico.LF.MultiStoreSyntax
import Relico.LF.Scheduling
import Relico.LF.StoreState

set_option autoImplicit false

namespace Relico
namespace LF

/--
Dispatch semantics for generated finite-store LF reactors with
multiple message reactions.

The selected reaction must belong to the generated reaction list and
must be triggered by the selected logical-action occurrence.
-/
inductive MultiStoreDispatchStep
    (messageReactions : List LF.Reaction) :
    LF.StoreState →
    LF.PendingAction →
    LF.Reaction →
    LF.StoreState →
    Prop where

  | fire
      (currentTag : LF.Tag)
      (stateStore : StateStore)
      (pendingActions remainingActions : LF.ActionQueue)
      (selectedAction : LF.PendingAction)
      (selectedReaction : LF.Reaction)
      (hReactionDeclared :
        selectedReaction ∈
          messageReactions)
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
      (hTrigger :
        selectedReaction.trigger =
          LF.Trigger.logicalAction
            selectedAction.name) :

      MultiStoreDispatchStep
        messageReactions
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
        selectedReaction
        {
          currentTag :=
            selectedAction.tag

          stateStore :=
            stateStore

          pendingActions :=
            remainingActions

          activeBody :=
            selectedReaction.body
        }

namespace MultiStoreDispatchStep

/--
Multi-reaction dispatch preserves reactor-state declaration coverage.
-/
theorem preserves_coverage
    {messageReactions : List LF.Reaction}
    {declaredVariables : List VarName}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hDispatch :
      LF.MultiStoreDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
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

/--
The reaction selected by a dispatch transition belongs to the
generated message-reaction list.
-/
theorem selectedReaction_mem
    {messageReactions : List LF.Reaction}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hDispatch :
      LF.MultiStoreDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    selectedReaction ∈
      messageReactions := by

  cases hDispatch with
  | fire _ _ _ _ _ _ hReactionDeclared =>
      exact hReactionDeclared

end MultiStoreDispatchStep
end LF
end Relico
