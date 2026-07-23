import Relico.Common.Occurrence
import Relico.DTR.State

set_option autoImplicit false

namespace Relico
namespace DTR

/--
A message occurrence is earliest when no pending occurrence has a
smaller logical arrival time.

Multiple messages with the same earliest time are all eligible.
-/
def IsEarliest
    (selected : DTR.PendingMessage)
    (queue : DTR.MessageBag) :
    Prop :=
  ∀ candidate,
    candidate ∈ queue →
      selected.arrivalTime ≤
        candidate.arrivalTime

/--
An occurrence-preserving scheduler selection from a DTR message bag.
-/
structure DispatchSelection
    (queue remaining : DTR.MessageBag) where

  selected :
    DTR.PendingMessage

  removed :
    Occurrence.RemovesOne
      selected
      queue
      remaining

  earliest :
    DTR.IsEarliest
      selected
      queue

/--
The selected message belongs to the original message bag.
-/
theorem DispatchSelection.selected_mem
    {queue remaining : DTR.MessageBag}
    (selection :
      DTR.DispatchSelection
        queue
        remaining) :
    selection.selected ∈ queue :=
  Occurrence.RemovesOne.selected_mem
    selection.removed

end DTR
end Relico
