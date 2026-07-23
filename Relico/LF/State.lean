import Relico.LF.Syntax

set_option autoImplicit false

namespace Relico
namespace LF

/--
A Lingua Franca tag consists of logical time and a microstep.
-/
structure Tag where
  time : LogicalTime
  microstep : Nat
deriving Repr, DecidableEq, BEq, Inhabited

namespace Tag

/--
Compute the tag produced by scheduling a logical action.

A zero delay advances the microstep. A positive delay advances logical
time and resets the microstep to zero.
-/
def schedule
    (tag : Tag)
    (delay : Delay) :
    Tag :=
  if delay.value = 0 then
    {
      time := tag.time
      microstep := tag.microstep + 1
    }
  else
    {
      time := LogicalTime.after tag.time delay
      microstep := 0
    }

@[simp]
theorem schedule_zero
    (tag : Tag) :
    schedule tag ⟨0⟩ =
      {
        time := tag.time
        microstep := tag.microstep + 1
      } := by
  simp [schedule]

theorem schedule_positive
    (tag : Tag)
    (delay : Delay)
    (hPositive : 0 < delay.value) :
    schedule tag delay =
      {
        time := LogicalTime.after tag.time delay
        microstep := 0
      } := by
  have hNonzero : delay.value ≠ 0 :=
    Nat.ne_of_gt hPositive

  simp [schedule, hNonzero]

/--
Scheduling preserves the intended logical arrival time.

For zero delay, the logical time stays unchanged and the microstep
advances. For positive delay, logical time advances by the delay.
-/
@[simp]
theorem schedule_time
    (tag : Tag)
    (delay : Delay) :
    (schedule tag delay).time =
      LogicalTime.after tag.time delay := by
  unfold schedule
  by_cases hZero : delay.value = 0
  · simp [hZero, LogicalTime.after]
  · simp [hZero]

end Tag

/--
One pending logical-action occurrence.
-/
structure PendingAction where
  name : ActionName
  tag : Tag
deriving Repr, DecidableEq, BEq, Inhabited

abbrev ActionQueue := List PendingAction

/--
Runtime state for the generated LF subset in vertical slice v0.

The active body contains the statements remaining in the startup
reaction or currently executing message reaction.
-/
structure State where
  currentTag : Tag
  stateValue : Int
  pendingActions : ActionQueue
  activeBody : Body
deriving Repr, DecidableEq, BEq, Inhabited

end LF
end Relico
