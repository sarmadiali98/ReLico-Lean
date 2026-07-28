import Relico.Common.Occurrence
import Relico.LF.State

set_option autoImplicit false

namespace Relico
namespace LF
namespace Tag

/--
Lexicographic ordering of LF tags.

Logical time is compared first. Microsteps order tags that have the
same logical time.
-/
def PrecedesOrEqual
    (left right : LF.Tag) :
    Prop :=
  left.time < right.time ∨
    (left.time = right.time ∧
      left.microstep ≤ right.microstep)

theorem precedesOrEqual_refl
    (tag : LF.Tag) :
    PrecedesOrEqual tag tag := by
  exact
    Or.inr
      ⟨rfl, Nat.le_refl tag.microstep⟩

theorem precedesOrEqual_same_time
    {left right : LF.Tag}
    (hTime :
      left.time = right.time)
    (hMicrostep :
      left.microstep ≤ right.microstep) :
    PrecedesOrEqual left right := by
  exact
    Or.inr
      ⟨hTime, hMicrostep⟩

/--
Two LF tags are equal when both components are equal.

This standalone lemma avoids dependent elimination in correctness
proofs whose surrounding hypotheses are indexed by pending actions.
-/
theorem eq_of_time_eq_of_microstep
    {left right :
      LF.Tag}
    (hTime :
      left.time =
        right.time)
    (hMicrostep :
      left.microstep =
        right.microstep) :
    left =
      right := by

  cases left with

  | mk leftTime leftMicrostep =>
      cases right with

      | mk rightTime rightMicrostep =>
          cases hTime
          cases hMicrostep
          rfl

/--
At equal metric time, a later microstep cannot precede an earlier
microstep.

Reaction declaration order is consulted only after complete-tag
ordering and therefore cannot reverse this fact.
-/
theorem not_precedesOrEqual_same_time_of_microstep_lt
    {earlier later :
      LF.Tag}
    (hSameTime :
      earlier.time =
        later.time)
    (hEarlierMicrostep :
      earlier.microstep <
        later.microstep) :
    ¬ PrecedesOrEqual
        later
        earlier := by

  intro hOrder

  rcases hOrder with
    hEarlierTime |
      ⟨_hEqualTime,
       hMicrostepOrder⟩

  · rw [
      hSameTime
    ] at hEarlierTime

    exact
      (Nat.lt_irrefl
        later.time)
        hEarlierTime

  · exact
      (Nat.not_le_of_gt
        hEarlierMicrostep)
        hMicrostepOrder

theorem time_le_of_precedesOrEqual
    {left right : LF.Tag}
    (hOrder :
      PrecedesOrEqual left right) :
    left.time ≤ right.time := by
  rcases hOrder with
    hEarlier | ⟨hSameTime, hMicrostep⟩

  · exact Nat.le_of_lt hEarlier

  · rw [hSameTime]
    exact Nat.le_refl right.time

end Tag

/--
An action occurrence is earliest when its tag precedes or equals every
pending action tag.
-/
def IsEarliest
    (selected : LF.PendingAction)
    (queue : LF.ActionQueue) :
    Prop :=
  ∀ candidate,
    candidate ∈ queue →
      LF.Tag.PrecedesOrEqual
        selected.tag
        candidate.tag

/--
An occurrence-preserving scheduler selection from an LF action queue.
-/
structure DispatchSelection
    (queue remaining : LF.ActionQueue) where

  selected :
    LF.PendingAction

  removed :
    Occurrence.RemovesOne
      selected
      queue
      remaining

  earliest :
    LF.IsEarliest
      selected
      queue

/--
The selected action belongs to the original action queue.
-/
theorem DispatchSelection.selected_mem
    {queue remaining : LF.ActionQueue}
    (selection :
      LF.DispatchSelection
        queue
        remaining) :
    selection.selected ∈ queue :=
  Occurrence.RemovesOne.selected_mem
    selection.removed

end LF
end Relico
