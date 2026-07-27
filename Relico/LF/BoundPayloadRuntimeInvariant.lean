import Relico.LF.BoundPayloadState
import Relico.LF.PriorityTimingInvariant

set_option autoImplicit false

namespace Relico

namespace LF
namespace BoundPayloadState

/--
All queued generated-LF payload actions have microstep zero.

Positive-delay internal schedules establish this property.
-/
def PendingMicrostepsZero
    (state : LF.BoundPayloadState) :
    Prop :=

  LF.ActionQueue.AllMicrostepsZero
    state.pendingActions

/--
Every queued generated-LF payload action is at a later logical time than the
current state.

This alternative is required immediately after a zero-delay external
invocation, where the current microstep may be positive but the residual queue
is empty.
-/
def PendingStrictlyFuture
    (state : LF.BoundPayloadState) :
    Prop :=

  ∀ action,
    action ∈ state.pendingActions →
      state.currentTag.time <
        action.tag.time

/--
Target scheduler invariant for the positive-delay internal payload fragment.

Queued internal actions always have microstep zero. At a dispatch boundary,
either the current tag also has microstep zero, or every queued action is
strictly later in metric time.
-/
structure RuntimeInvariant
    (state : LF.BoundPayloadState) :
    Prop where

  pendingMicrostepsZero :
    PendingMicrostepsZero
      state

  currentZeroOrPendingStrictlyFuture :
    state.currentTag.microstep = 0 ∨
      PendingStrictlyFuture
        state

end BoundPayloadState
end LF

end Relico
