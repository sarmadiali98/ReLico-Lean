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

/--
The **strict** lexicographic tag order.

`PrecedesOrEqual` is a preorder, and deliberately so: two events at one tag tie, and
`precedesOrEqual_total` (`Relico/LF/GeneralRuntime.lean`) records that the tie is the ordinary case rather
than a corner one, because every zero-delay send produces events sharing a time. Causality is the one place
where a tie is not acceptable — a message must arrive *strictly* after the send that produced it, or an
arrival could sit at the very tag it was sent from.

Stated because the paper's **Lemma 3 (Causality Preservation)** concludes `TT_i < TT_j`, and no strict tag
order existed anywhere in this development. Measured 2026-08-25: every `StrictlyPrecedes` in the tree was
either `sourceStrictlyPrecedes` (source-side *actor* selection) or one of the multi-store strict *priority*
orders — never a tag order. The body mirrors `PrecedesOrEqual` with `<` in the microstep conjunct and is
otherwise identical, so the two orders cannot drift apart on the time component.
-/
def StrictlyPrecedes
    (left right : LF.Tag) :
    Prop :=
  left.time < right.time ∨
    (left.time = right.time ∧
      left.microstep < right.microstep)

/--
The strict order refines the non-strict one.

Without this the new order would be an island: `PrecedesOrEqual` has roughly sixty use sites and carries
reflexivity, transitivity, totality, decidability and the schedule-monotonicity lemma, and a causality
result that could not be handed to any of them would be of little use to the rest of the development.
-/
theorem precedesOrEqual_of_strictlyPrecedes
    {left right :
      LF.Tag}
    (hOrder :
      StrictlyPrecedes
        left
        right) :
    PrecedesOrEqual
      left
      right := by

  rcases hOrder with
    hTime |
    ⟨hSameTime, hMicrostep⟩

  · exact Or.inl hTime

  · exact Or.inr
      ⟨hSameTime,
        Nat.le_of_lt hMicrostep⟩

/--
**Lemma 3 (Causality Preservation), at tag level.** Scheduling from a tag always produces a tag *strictly*
after it — for every delay, including zero.

This is the strict upgrade of `LF.Tag.precedesOrEqual_schedule`, which already exists in
`Relico/LF/PendingNotPast.lean`. That file is otherwise entirely multi-store, but the lemma is a fact about
`Tag` alone and so serves every family; only the strict half was missing.

**One statement covers both send routes, and that is what makes it Lemma 3 rather than half of it.**
`LF.Tag.schedule` is the paper's `upd`, and it is the tag function of *both* general-family send rules —
`LF.GeneralStep.schedule` for the self-send route and `LF.GeneralStep.setPort` for the connection route —
each of which appends an event tagged `LF.Tag.schedule state.currentTag d` while leaving `currentTag`
alone. The paper's own proof of Lemma 3 reasons only about "an LF connection with `after d`", although its
statement never requires the two actors to differ, so it has no case for a self-send; phrasing the result
over `upd` instead of over connections is exactly the repair recorded as **P26**.

The two cases are the two branches of `upd`, and they are strict for *different* reasons — which is the
other half of what P26 records. A zero delay leaves metric time alone and increments the microstep, so
strictness comes from the microstep. A positive delay advances metric time and **resets the microstep to
zero**, so strictness comes from the time and the microstep moves *backwards*; the lexicographic order is
settled before it is ever consulted. P26's first defect is that the paper's `d > 0` case writes
`TT_j = (t + d, m)`, retaining the microstep its own `upd` discards — harmless to the conclusion, for
precisely the reason this proof makes explicit.

Per **F72**, `omega` is blind to `Tag.time`, whose type is the `LogicalTime` abbreviation, while
`Tag.microstep` is a bare `Nat` and is visible to it. So the time reasoning closes with explicit `Nat`
lemmas and `omega` is used only on the microstep goal.
-/
theorem strictlyPrecedes_schedule
    (currentTag : LF.Tag)
    (delay : Delay) :
    StrictlyPrecedes
      currentTag
      (LF.Tag.schedule
        currentTag
        delay) := by

  by_cases hZero :
      delay.value = 0

  · have hTime :
        (LF.Tag.schedule currentTag delay).time =
          currentTag.time := by
      simp [LF.Tag.schedule, hZero]

    have hMicrostep :
        (LF.Tag.schedule currentTag delay).microstep =
          currentTag.microstep + 1 := by
      simp [LF.Tag.schedule, hZero]

    refine Or.inr
      ⟨hTime.symm, ?_⟩

    rw [hMicrostep]

    omega

  · have hPositive :
        0 < delay.value :=
      Nat.pos_of_ne_zero hZero

    have hTime :
        (LF.Tag.schedule currentTag delay).time =
          currentTag.time + delay.value := by
      simp [LF.Tag.schedule, LogicalTime.after, hZero]

    have hIncrease :
        currentTag.time <
          currentTag.time + delay.value := by
      simpa using
        Nat.add_lt_add_left hPositive currentTag.time

    refine Or.inl ?_

    rw [hTime]

    exact hIncrease

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
