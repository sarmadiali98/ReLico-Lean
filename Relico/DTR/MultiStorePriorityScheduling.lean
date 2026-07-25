import Relico.DTR.MessageServerPriority
import Relico.DTR.Scheduling

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Whether `left` occurs no later than `right` in a message-server list.

The relation is name based because pending messages carry a
message-server name rather than the complete declaration. If the two
names are equal, the first matching declaration establishes the
relation immediately.
-/
private def serverNamePrecedesOrEqualBool
    (left right : MsgName) :
    List DTR.MessageServer →
    Bool

  | [] =>
      false

  | current :: remaining =>
      if current.name = left then
        true
      else if current.name = right then
        false
      else
        serverNamePrecedesOrEqualBool
          left
          right
          remaining

/--
Whether `left` occurs no later than `right` in a message-server list.

The relation is name based because pending messages carry a
message-server name rather than the complete declaration. If the two
names are equal, the first matching declaration establishes the
relation immediately.

The proposition is backed by a Boolean decision procedure so it can be
evaluated by `decide` and `native_decide`.
-/
def ServerNamePrecedesOrEqual
    (left right : MsgName)
    (messageServers :
      List DTR.MessageServer) :
    Prop :=
  serverNamePrecedesOrEqualBool
      left
      right
      messageServers =
    true

/--
Same-server-order relation after stable local-priority normalization.

Smaller explicit priorities occur first. Equal explicit priorities and
unannotated declarations retain source declaration order.
-/
def PriorityServerNamePrecedesOrEqual
    (left right : MsgName)
    (messageServers :
      List DTR.MessageServer) :
    Prop :=
  ServerNamePrecedesOrEqual
    left
    right
    (DTR.MessageServerPriority.normalize
      messageServers)


instance
    (left right : MsgName)
    (messageServers :
      List DTR.MessageServer) :
    Decidable
      (ServerNamePrecedesOrEqual
        left
        right
        messageServers) := by
  unfold ServerNamePrecedesOrEqual
  infer_instance

instance
    (left right : MsgName)
    (messageServers :
      List DTR.MessageServer) :
    Decidable
      (PriorityServerNamePrecedesOrEqual
        left
        right
        messageServers) := by
  unfold PriorityServerNamePrecedesOrEqual
  infer_instance

/--
Priority-aware eligibility for a pending DTR message.

A selected occurrence must:

1. have an earliest logical arrival time; and
2. target the first priority-ordered server represented among all
   occurrences with that same arrival time.

Priority does not allow a later message to overtake an earlier message.
-/
def IsPriorityEligible
    (messageServers :
      List DTR.MessageServer)
    (selected : DTR.PendingMessage)
    (queue : DTR.MessageBag) :
    Prop :=
  DTR.IsEarliest
      selected
      queue ∧
    ∀ candidate,
      candidate ∈
          queue →
      candidate.arrivalTime =
          selected.arrivalTime →
      PriorityServerNamePrecedesOrEqual
        selected.name
        candidate.name
        messageServers

/--
Priority-aware eligibility implies ordinary earliest-time eligibility.
-/
theorem IsPriorityEligible.isEarliest
    {messageServers :
      List DTR.MessageServer}
    {selected : DTR.PendingMessage}
    {queue : DTR.MessageBag}
    (hEligible :
      DTR.IsPriorityEligible
        messageServers
        selected
        queue) :
    DTR.IsEarliest
      selected
      queue :=
  hEligible.1

/--
Extract the same-time server-order obligation from priority-aware
eligibility.
-/
theorem IsPriorityEligible.precedes_same_time
    {messageServers :
      List DTR.MessageServer}
    {selected candidate :
      DTR.PendingMessage}
    {queue : DTR.MessageBag}
    (hEligible :
      DTR.IsPriorityEligible
        messageServers
        selected
        queue)
    (hCandidate :
      candidate ∈
        queue)
    (hSameTime :
      candidate.arrivalTime =
        selected.arrivalTime) :
    DTR.PriorityServerNamePrecedesOrEqual
      selected.name
      candidate.name
      messageServers :=
  hEligible.2
    candidate
    hCandidate
    hSameTime

end DTR
end Relico
