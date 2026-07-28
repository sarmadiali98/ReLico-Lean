/-
Copyright (c) 2026.

Ordinary generated-LF scheduler consistency.

`LF.StoreState.PendingNotPast` states that every pending logical-action
occurrence has a complete LF tag greater than or equal to the state's current
tag.

The invariant permits:

- the current complete tag;
- later microsteps at the current metric time;
- later metric times;
- zero-delay and positive-delay schedules.

It excludes only pending occurrences whose complete LF tags are already in
the past.

No source-side timing component or source restriction is introduced.
-/

import Relico.Correctness.DirectLFDispatchSelection
import Relico.LF.MultiStoreDispatchSemantics
import Relico.LF.MultiStoreSemantics

set_option autoImplicit false

namespace Relico
namespace LF

namespace Tag

/--
Scheduling from an LF tag never produces a tag before the current tag.

For zero delay, metric time is unchanged and the microstep increases.
For positive delay, metric time increases and the scheduled microstep is zero.
-/
theorem precedesOrEqual_schedule
    (currentTag : LF.Tag)
    (delay : Delay) :
    LF.Tag.PrecedesOrEqual
      currentTag
      (LF.Tag.schedule
        currentTag
        delay) := by

  by_cases hZero :
      delay.value = 0

  · apply
      LF.Tag.precedesOrEqual_same_time

    · simp [
        LF.Tag.schedule,
        hZero
      ]

    · simp [
        LF.Tag.schedule,
        hZero
      ]

  · have hPositive :
        0 < delay.value :=
      Nat.pos_of_ne_zero
        hZero

    have hMetricTimeIncrease :
        currentTag.time <
          currentTag.time +
            delay.value := by

      simpa using
        Nat.add_lt_add_left
          hPositive
          currentTag.time

    exact
      Or.inl
        (by
          simpa [
            LF.Tag.schedule,
            LogicalTime.after,
            hZero
          ] using
            hMetricTimeIncrease)

end Tag

namespace ActionQueue

/--
Every pending LF action is at the current tag or a later complete LF tag.

This relation permits:

* the same metric time and the same microstep;
* the same metric time and a later microstep;
* a later metric time with any generated microstep.

It excludes only pending occurrences whose complete tags are already before
the current tag.
-/
def PendingNotPast
    (currentTag : LF.Tag)
    (pendingActions : LF.ActionQueue) :
    Prop :=
  ∀ action,
    action ∈ pendingActions →
      LF.Tag.PrecedesOrEqual
        currentTag
        action.tag

@[simp]
theorem pendingNotPast_nil
    (currentTag : LF.Tag) :
    LF.ActionQueue.PendingNotPast
      currentTag
      [] := by

  intro action hAction
  cases hAction

/--
Appending one action that is not before the current tag preserves the
pending-not-past invariant.
-/
theorem PendingNotPast.append_one
    {currentTag : LF.Tag}
    {pendingActions : LF.ActionQueue}
    {newAction : LF.PendingAction}
    (hPending :
      LF.ActionQueue.PendingNotPast
        currentTag
        pendingActions)
    (hNew :
      LF.Tag.PrecedesOrEqual
        currentTag
        newAction.tag) :
    LF.ActionQueue.PendingNotPast
      currentTag
      (pendingActions ++ [newAction]) := by

  intro action hAction

  simp only [
    List.mem_append,
    List.mem_singleton
  ] at hAction

  rcases hAction with
    hExisting |
    hAdded

  · exact
      hPending
        action
        hExisting

  · subst action
    exact hNew

/--
Removing one occurrence preserves pending-not-past relative to an unchanged
current tag.
-/
theorem PendingNotPast.remove
    {currentTag : LF.Tag}
    {pendingActions remainingActions :
      LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hPending :
      LF.ActionQueue.PendingNotPast
        currentTag
        pendingActions)
    (hRemoved :
      Occurrence.RemovesOne
        selectedAction
        pendingActions
        remainingActions) :
    LF.ActionQueue.PendingNotPast
      currentTag
      remainingActions := by

  intro action hAction

  exact
    hPending
      action
      (Occurrence.RemovesOne.remaining_mem
        hRemoved
        hAction)

/--
Removing an earliest action establishes pending-not-past relative to the
selected action's tag.

This is the exact post-dispatch invariant: dispatch changes the current tag to
the selected tag, and every residual action is no earlier than that selected
tag.
-/
theorem pendingNotPast_of_remove_earliest
    {pendingActions remainingActions :
      LF.ActionQueue}
    {selectedAction : LF.PendingAction}
    (hEarliest :
      LF.IsEarliest
        selectedAction
        pendingActions)
    (hRemoved :
      Occurrence.RemovesOne
        selectedAction
        pendingActions
        remainingActions) :
    LF.ActionQueue.PendingNotPast
      selectedAction.tag
      remainingActions := by

  intro action hAction

  exact
    hEarliest
      action
      (Occurrence.RemovesOne.remaining_mem
        hRemoved
        hAction)

end ActionQueue

namespace StoreState

/--
Ordinary LF scheduler consistency: no pending action is before the state's
current complete LF tag.
-/
def PendingNotPast
    (state : LF.StoreState) :
    Prop :=
  LF.ActionQueue.PendingNotPast
    state.currentTag
    state.pendingActions

/--
An LF store state with no pending actions satisfies pending-not-past.
-/
theorem pendingNotPast_of_pendingActions_nil
    {state : LF.StoreState}
    (hEmpty :
      state.pendingActions = []) :
    LF.StoreState.PendingNotPast
      state := by

  unfold
    LF.StoreState.PendingNotPast

  rw [hEmpty]

  exact
    LF.ActionQueue.pendingNotPast_nil
      state.currentTag

/--
Extract the complete-tag order for one pending action.
-/
theorem PendingNotPast.action
    {state : LF.StoreState}
    (hPending :
      LF.StoreState.PendingNotPast
        state)
    {action : LF.PendingAction}
    (hAction :
      action ∈ state.pendingActions) :
    LF.Tag.PrecedesOrEqual
      state.currentTag
      action.tag := by

  exact
    hPending
      action
      hAction

end StoreState

namespace MultiStoreStep

/--
Every ordinary generated-LF statement step preserves pending-not-past.

Assignment leaves the current tag and pending action queue unchanged.
Scheduling appends an action whose tag is obtained from the current tag and
therefore cannot be in the past.

Zero-delay scheduling is included.
-/
theorem preserves_pendingNotPast
    {declaredVariables : List VarName}
    {declaredActions : List ActionName}
    {before after : LF.StoreState}
    {label : LF.Label}
    (hStep :
      LF.MultiStoreStep
        declaredVariables
        declaredActions
        before
        label
        after)
    (hBefore :
      LF.StoreState.PendingNotPast
        before) :
    LF.StoreState.PendingNotPast
      after := by

  cases hStep with

  | assign
      currentTag
      stateStore
      pendingActions
      target
      expression
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      exact hBefore

  | schedule
      currentTag
      stateStore
      pendingActions
      targetAction
      delay
      remaining
      hTarget =>

      change
        LF.ActionQueue.PendingNotPast
          currentTag
          (pendingActions ++ [
            {
              name :=
                targetAction

              tag :=
                LF.Tag.schedule
                  currentTag
                  delay
            }
          ])

      change
        LF.ActionQueue.PendingNotPast
          currentTag
          pendingActions
        at hBefore

      apply
        LF.ActionQueue.PendingNotPast.append_one
          hBefore

      exact
        LF.Tag.precedesOrEqual_schedule
          currentTag
          delay

end MultiStoreStep

namespace MultiStoreDispatchStep

/--
Every ordinary generated-LF dispatch establishes pending-not-past in its
resulting state.

The selected action is reaction-priority eligible and hence earliest by
complete LF tag. Dispatch removes that occurrence, changes the current tag to
its tag, and leaves only actions whose tags do not precede it.
-/
theorem establishes_pendingNotPast
    {messageReactions : List LF.Reaction}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hDispatch :
      LF.MultiStoreDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after) :
    LF.StoreState.PendingNotPast
      after := by

  cases hDispatch with

  | fire
      currentTag
      stateStore
      pendingActions
      remainingActions
      selectedAction
      selectedReaction
      hReactionDeclared
      hRemoved
      hPriorityEligible
      hNotPast
      hTrigger =>

      change
        LF.ActionQueue.PendingNotPast
          selectedAction.tag
          remainingActions

      exact
        LF.ActionQueue.pendingNotPast_of_remove_earliest
          hPriorityEligible.1
          hRemoved

end MultiStoreDispatchStep

end LF
end Relico
