import Relico.LF.MultiStoreSyntax
import Relico.LF.Scheduling

set_option autoImplicit false

namespace Relico
namespace LF

/--
Whether the reaction for action `left` occurs no later than the
reaction for action `right` in a generated reaction list.

Startup reactions are ignored. Multi-server dispatch receives the
message-reaction list, but skipping startup triggers makes this
relation explicit and reusable.
-/
private def reactionActionPrecedesOrEqualBool
    (left right : ActionName) :
    List LF.Reaction →
    Bool

  | [] =>
      false

  | reaction :: remaining =>
      match reaction.trigger with

      | LF.Trigger.startup =>
          reactionActionPrecedesOrEqualBool
            left
            right
            remaining

      | LF.Trigger.logicalAction action =>
          if action = left then
            true
          else if action = right then
            false
          else
            reactionActionPrecedesOrEqualBool
              left
              right
              remaining

/--
Whether the reaction for action `left` occurs no later than the
reaction for action `right` in a generated reaction list.

Startup reactions are ignored. Multi-server dispatch receives the
message-reaction list, but skipping startup triggers makes this
relation explicit and reusable.

The proposition is backed by a Boolean decision procedure so it can be
evaluated by `decide` and `native_decide`.
-/
def ReactionActionPrecedesOrEqual
    (left right : ActionName)
    (messageReactions :
      List LF.Reaction) :
    Prop :=
  reactionActionPrecedesOrEqualBool
      left
      right
      messageReactions =
    true


/--
The empty reaction list contains neither requested logical-action
trigger.
-/
@[simp]
theorem reactionActionPrecedesOrEqual_nil
    (left right : ActionName) :
    ¬ ReactionActionPrecedesOrEqual
        left
        right
        [] := by

  unfold ReactionActionPrecedesOrEqual

  simp [
    reactionActionPrecedesOrEqualBool
  ]

/--
Public recursive equation for a logical-action-triggered reaction at
the head of a generated reaction list.

The private Boolean scanner remains an implementation detail.
-/
@[simp]
theorem reactionActionPrecedesOrEqual_cons_logicalAction
    (left right action : ActionName)
    (reactionName : ReactionName)
    (body : LF.Body)
    (remaining :
      List LF.Reaction) :
    ReactionActionPrecedesOrEqual
        left
        right
        ({
          name :=
            reactionName

          trigger :=
            LF.Trigger.logicalAction
              action

          body :=
            body
        } :: remaining) ↔
      if action = left then
        True
      else if action = right then
        False
      else
        ReactionActionPrecedesOrEqual
          left
          right
          remaining := by

  by_cases hLeft :
      action =
        left

  · simp [
      ReactionActionPrecedesOrEqual,
      reactionActionPrecedesOrEqualBool,
      hLeft
    ]

  · by_cases hRight :
        action =
          right

    · simp [
        ReactionActionPrecedesOrEqual,
        reactionActionPrecedesOrEqualBool,
        hRight
      ]

    · simp [
        ReactionActionPrecedesOrEqual,
        reactionActionPrecedesOrEqualBool,
        hLeft,
        hRight
      ]


instance
    (left right : ActionName)
    (messageReactions :
      List LF.Reaction) :
    Decidable
      (ReactionActionPrecedesOrEqual
        left
        right
        messageReactions) := by
  unfold ReactionActionPrecedesOrEqual
  infer_instance

/--
Priority-aware eligibility for a pending LF logical-action occurrence.

The ordinary LF scheduler first selects an earliest complete tag.
Reaction declaration order then resolves action occurrences present at
that same complete tag.
-/
def IsReactionPriorityEligible
    (messageReactions :
      List LF.Reaction)
    (selected : LF.PendingAction)
    (queue : LF.ActionQueue) :
    Prop :=
  LF.IsEarliest
      selected
      queue ∧
    ∀ candidate,
      candidate ∈
          queue →
      candidate.tag =
          selected.tag →
      LF.ReactionActionPrecedesOrEqual
        selected.name
        candidate.name
        messageReactions

/--
Reaction-priority eligibility implies ordinary earliest-tag
eligibility.
-/
theorem IsReactionPriorityEligible.isEarliest
    {messageReactions :
      List LF.Reaction}
    {selected : LF.PendingAction}
    {queue : LF.ActionQueue}
    (hEligible :
      LF.IsReactionPriorityEligible
        messageReactions
        selected
        queue) :
    LF.IsEarliest
      selected
      queue :=
  hEligible.1

/--
Extract the same-tag reaction-order obligation from priority-aware LF
eligibility.
-/
theorem IsReactionPriorityEligible.precedes_same_tag
    {messageReactions :
      List LF.Reaction}
    {selected candidate :
      LF.PendingAction}
    {queue : LF.ActionQueue}
    (hEligible :
      LF.IsReactionPriorityEligible
        messageReactions
        selected
        queue)
    (hCandidate :
      candidate ∈
        queue)
    (hSameTag :
      candidate.tag =
        selected.tag) :
    LF.ReactionActionPrecedesOrEqual
      selected.name
      candidate.name
      messageReactions :=
  hEligible.2
    candidate
    hCandidate
    hSameTag

/--
A textually earlier reaction at a later microstep is not eligible while
an occurrence remains pending at an earlier microstep of the same
metric time.

Complete-tag order precedes reaction declaration order.
-/
theorem IsReactionPriorityEligible.not_of_earlier_microstep_candidate
    {messageReactions :
      List LF.Reaction}
    {selected candidate :
      LF.PendingAction}
    {queue :
      LF.ActionQueue}
    (hCandidate :
      candidate ∈
        queue)
    (hSameTime :
      candidate.tag.time =
        selected.tag.time)
    (hEarlierMicrostep :
      candidate.tag.microstep <
        selected.tag.microstep) :
    ¬ LF.IsReactionPriorityEligible
        messageReactions
        selected
        queue := by

  intro hEligible

  have hCompleteTagOrder :
      LF.Tag.PrecedesOrEqual
        selected.tag
        candidate.tag :=

    hEligible.1
      candidate
      hCandidate

  exact
    (LF.Tag.not_precedesOrEqual_same_time_of_microstep_lt
      hSameTime
      hEarlierMicrostep)
      hCompleteTagOrder

end LF
end Relico
