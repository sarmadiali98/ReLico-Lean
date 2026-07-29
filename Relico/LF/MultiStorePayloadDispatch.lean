import Relico.Common.Occurrence
import Relico.LF.MultiStorePayloadSemantics
import Relico.LF.Scheduling

set_option autoImplicit false

namespace Relico
namespace LF

/--
Scan an ordered generated reaction list for logical-action trigger
order. Startup reactions do not participate in message dispatch.
-/
private def multiStorePayloadReactionActionPrecedesOrEqualBool
    (left right :
      ActionName) :
    List LF.MultiStorePayloadReaction →
    Bool

  | [] =>
      false

  | reaction :: remaining =>
      match reaction.trigger with

      | .startup =>
          multiStorePayloadReactionActionPrecedesOrEqualBool
            left
            right
            remaining

      | .logicalAction actionName =>
          if actionName = left then
            true
          else if actionName = right then
            false
          else
            multiStorePayloadReactionActionPrecedesOrEqualBool
              left
              right
              remaining

/--
Generated reaction order for two logical-action names.
-/
def MultiStorePayloadReactionActionPrecedesOrEqual
    (left right :
      ActionName)
    (messageReactions :
      List LF.MultiStorePayloadReaction) :
    Prop :=
  multiStorePayloadReactionActionPrecedesOrEqualBool
      left
      right
      messageReactions =
    true

instance
    (left right :
      ActionName)
    (messageReactions :
      List LF.MultiStorePayloadReaction) :
    Decidable
      (MultiStorePayloadReactionActionPrecedesOrEqual
        left
        right
        messageReactions) := by

  unfold MultiStorePayloadReactionActionPrecedesOrEqual
  infer_instance

/--
Priority-aware LF eligibility for one pending logical-action
occurrence.

LF complete-tag order is applied first. Generated reaction order is
consulted only among occurrences at the same complete superdense tag.
-/
def MultiStorePayloadIsReactionPriorityEligible
    (messageReactions :
      List LF.MultiStorePayloadReaction)
    (selected :
      LF.PendingAction)
    (pendingActions :
      LF.ActionQueue) :
    Prop :=
  LF.IsEarliest
      selected
      pendingActions ∧
    ∀ candidate,
      candidate ∈
          pendingActions →
      candidate.tag =
          selected.tag →
      LF.MultiStorePayloadReactionActionPrecedesOrEqual
        selected.name
        candidate.name
        messageReactions

namespace MultiStorePayloadIsReactionPriorityEligible

theorem isEarliest
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {selected :
      LF.PendingAction}
    {pendingActions :
      LF.ActionQueue}
    (hEligible :
      LF.MultiStorePayloadIsReactionPriorityEligible
        messageReactions
        selected
        pendingActions) :
    LF.IsEarliest
      selected
      pendingActions :=
  hEligible.1

theorem precedes_same_tag
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {selected candidate :
      LF.PendingAction}
    {pendingActions :
      LF.ActionQueue}
    (hEligible :
      LF.MultiStorePayloadIsReactionPriorityEligible
        messageReactions
        selected
        pendingActions)
    (hCandidate :
      candidate ∈
        pendingActions)
    (hSameTag :
      candidate.tag =
        selected.tag) :
    LF.MultiStorePayloadReactionActionPrecedesOrEqual
      selected.name
      candidate.name
      messageReactions :=
  hEligible.2
    candidate
    hCandidate
    hSameTag

end MultiStorePayloadIsReactionPriorityEligible

/--
Payload-aware generated LF multi-reaction dispatch.

Exactly one action occurrence is removed. Its ordered payload is bound
to the selected reaction's ordered parameter list, and that reaction's
body becomes active.
-/
inductive MultiStorePayloadDispatchStep
    (messageReactions :
      List LF.MultiStorePayloadReaction) :
    LF.MultiStorePayloadState →
    LF.PendingAction →
    LF.MultiStorePayloadReaction →
    LF.MultiStorePayloadState →
    Prop where

  | fire
      (currentTag :
        LF.Tag)
      (stateStore :
        StateStore)
      (parameters :
        ParameterStore)
      (pendingActions remainingActions :
        LF.ActionQueue)
      (selectedAction :
        LF.PendingAction)
      (selectedReaction :
        LF.MultiStorePayloadReaction)
      (boundParameters :
        ParameterStore)
      (hReactionDeclared :
        selectedReaction ∈
          messageReactions)
      (hRemoved :
        Occurrence.RemovesOne
          selectedAction
          pendingActions
          remainingActions)
      (hPriorityEligible :
        LF.MultiStorePayloadIsReactionPriorityEligible
          messageReactions
          selectedAction
          pendingActions)
      (hNotPast :
        LF.Tag.PrecedesOrEqual
          currentTag
          selectedAction.tag)
      (hTrigger :
        selectedReaction.trigger =
          LF.MultiStorePayloadTrigger.logicalAction
            selectedAction.name)
      (hBind :
        ParameterStore.bindPayload
            selectedReaction.parameters
            selectedAction.payload =
          some boundParameters) :

      MultiStorePayloadDispatchStep
        messageReactions
        {
          currentTag :=
            currentTag

          stateStore :=
            stateStore

          parameters :=
            parameters

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

          parameters :=
            boundParameters

          pendingActions :=
            remainingActions

          activeBody :=
            selectedReaction.body
        }

namespace MultiStorePayloadDispatchStep

theorem selected_mem
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hDispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    selectedAction ∈
      before.pendingActions := by

  cases hDispatch with

  | fire
      _currentTag
      _stateStore
      _parameters
      _pendingActions
      _remainingActions
      _selectedAction
      _selectedReaction
      _boundParameters
      _hReactionDeclared
      hRemoved
      _hPriorityEligible
      _hNotPast
      _hTrigger
      _hBind =>

      exact
        Occurrence.RemovesOne.selected_mem
          hRemoved

theorem selectedReaction_mem
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hDispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    selectedReaction ∈
      messageReactions := by

  cases hDispatch with

  | fire
      _currentTag
      _stateStore
      _parameters
      _pendingActions
      _remainingActions
      _selectedAction
      _selectedReaction
      _boundParameters
      hReactionDeclared
      _hRemoved
      _hPriorityEligible
      _hNotPast
      _hTrigger
      _hBind =>

      exact hReactionDeclared

theorem preserves_stateStore
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hDispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    after.stateStore =
      before.stateStore := by

  cases hDispatch
  rfl

theorem activates_reaction_body
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hDispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    after.activeBody =
      selectedReaction.body := by

  cases hDispatch
  rfl

theorem binds_selected_payload
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hDispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    ParameterStore.bindPayload
        selectedReaction.parameters
        selectedAction.payload =
      some after.parameters := by

  cases hDispatch with

  | fire
      _currentTag
      _stateStore
      _parameters
      _pendingActions
      _remainingActions
      _selectedAction
      _selectedReaction
      _boundParameters
      _hReactionDeclared
      _hRemoved
      _hPriorityEligible
      _hNotPast
      _hTrigger
      hBind =>

      exact hBind

end MultiStorePayloadDispatchStep
end LF
end Relico
