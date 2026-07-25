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

end LF
end Relico
