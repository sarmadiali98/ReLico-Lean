import Relico.LF.BoundPayloadState
import Relico.LF.Scheduling

set_option autoImplicit false

namespace Relico
namespace LF

/--
Dispatch semantics for one generated parameter-aware payload reaction.

The triggering action payload is bound to the translated formal list.
The resulting environment represents the values read from the typed
logical action when the reaction activates.
-/
inductive BoundPayloadDispatchStep
    (reaction : LF.PayloadReaction) :
    LF.BoundPayloadState →
    LF.PendingAction →
    LF.BoundPayloadState →
    Prop where

  | fire
      (currentTag : LF.Tag)
      (stateValue : Int)
      (parameters : ParameterStore)
      (pendingActions remainingActions : LF.ActionQueue)
      (selectedAction : LF.PendingAction)
      (boundParameters : ParameterStore)
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
        selectedAction.name =
          reaction.logicalAction)
      (hBind :
        ParameterStore.bindPayload
            reaction.parameters
            selectedAction.payload =
          some boundParameters) :

      BoundPayloadDispatchStep
        reaction
        {
          currentTag :=
            currentTag

          stateValue :=
            stateValue

          parameters :=
            parameters

          pendingActions :=
            pendingActions

          activeBody :=
            []
        }
        selectedAction
        {
          currentTag :=
            selectedAction.tag

          stateValue :=
            stateValue

          parameters :=
            boundParameters

          pendingActions :=
            remainingActions

          activeBody :=
            reaction.body
        }

namespace BoundPayloadDispatchStep

theorem selected_mem
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.BoundPayloadDispatchStep
        reaction
        before
        selectedAction
        after) :
    selectedAction ∈
      before.pendingActions := by

  cases hDispatch with
  | fire _ _ _ _ _ _ _ hRemoved =>
      exact
        Occurrence.RemovesOne.selected_mem
          hRemoved

theorem preserves_stateValue
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.BoundPayloadDispatchStep
        reaction
        before
        selectedAction
        after) :
    after.stateValue =
      before.stateValue := by

  cases hDispatch
  rfl

theorem activates_reaction_body
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.BoundPayloadDispatchStep
        reaction
        before
        selectedAction
        after) :
    after.activeBody =
      reaction.body := by

  cases hDispatch
  rfl

end BoundPayloadDispatchStep
end LF
end Relico
