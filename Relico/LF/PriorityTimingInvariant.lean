import Relico.Common.Occurrence
import Relico.LF.MultiStoreDispatchSemantics
import Relico.LF.MultiStoreSemantics

set_option autoImplicit false

namespace Relico
namespace LF

namespace Tag

/--
A positive-delay schedule always produces microstep zero.
-/
theorem schedule_positive_microstep_zero
    (tag : LF.Tag)
    (delay : Delay)
    (hPositive :
      0 < delay.value) :
    (LF.Tag.schedule
      tag
      delay).microstep =
      0 := by

  rw [
    LF.Tag.schedule_positive
      tag
      delay
      hPositive
  ]

/--
A zero-delay schedule advances the current microstep.
-/
theorem schedule_zero_microstep
    (tag : LF.Tag) :
    (LF.Tag.schedule
      tag
      ⟨0⟩).microstep =
      tag.microstep + 1 := by

  rw [
    LF.Tag.schedule_zero
  ]

end Tag

namespace ActionQueue

/--
Every pending logical-action occurrence has microstep zero.
-/
def AllMicrostepsZero
    (queue : LF.ActionQueue) :
    Prop :=
  ∀ action,
    action ∈ queue →
    action.tag.microstep = 0

@[simp]
theorem allMicrostepsZero_nil :
    AllMicrostepsZero
      [] := by

  intro action hMember
  cases hMember

theorem allMicrostepsZero_cons
    {head : LF.PendingAction}
    {tail : LF.ActionQueue}
    (hHead :
      head.tag.microstep = 0)
    (hTail :
      AllMicrostepsZero tail) :
    AllMicrostepsZero
      (head :: tail) := by

  intro action hMember

  simp only [
    List.mem_cons
  ] at hMember

  rcases hMember with
    rfl | hTailMember

  · exact hHead

  · exact
      hTail
        action
        hTailMember

theorem allMicrostepsZero_append_one
    {queue : LF.ActionQueue}
    {action : LF.PendingAction}
    (hQueue :
      AllMicrostepsZero queue)
    (hAction :
      action.tag.microstep = 0) :
    AllMicrostepsZero
      (queue ++ [action]) := by

  intro candidate hMember

  simp only [
    List.mem_append,
    List.mem_singleton
  ] at hMember

  rcases hMember with
    hExisting | hAdded

  · exact
      hQueue
        candidate
        hExisting

  · subst candidate
    exact hAction

theorem allMicrostepsZero_remove
    {queue remaining :
      LF.ActionQueue}
    {selected : LF.PendingAction}
    (hQueue :
      AllMicrostepsZero queue)
    (hRemoved :
      Occurrence.RemovesOne
        selected
        queue
        remaining) :
    AllMicrostepsZero
      remaining := by

  intro candidate hMember

  exact
    hQueue
      candidate
      (Occurrence.RemovesOne.remaining_mem
        hRemoved
        hMember)

end ActionQueue

namespace StoreState

/--
Runtime timing invariant for the priority-sensitive generated-LF
fragment.
-/
def PendingMicrostepsZero
    (state : LF.StoreState) :
    Prop :=
  LF.ActionQueue.AllMicrostepsZero
    state.pendingActions

end StoreState

namespace MultiStoreStep

/--
Scheduling a positive-delay action preserves the zero-microstep queue
invariant.
-/
theorem schedule_preserves_pendingMicrostepsZero
    (currentTag : LF.Tag)
    (pendingActions : LF.ActionQueue)
    (targetAction : ActionName)
    (delay : Delay)
    (hQueue :
      LF.ActionQueue.AllMicrostepsZero
        pendingActions)
    (hPositive :
      0 < delay.value) :
    LF.ActionQueue.AllMicrostepsZero
      (pendingActions ++ [
        {
          name :=
            targetAction

          tag :=
            LF.Tag.schedule
              currentTag
              delay
        }
      ]) := by

  apply
    LF.ActionQueue.allMicrostepsZero_append_one
      hQueue

  exact
    LF.Tag.schedule_positive_microstep_zero
      currentTag
      delay
      hPositive

end MultiStoreStep

namespace MultiStoreDispatchStep

/--
Dispatch removes one pending action and therefore preserves the
zero-microstep queue invariant.
-/
theorem preserves_pendingMicrostepsZero
    {messageReactions :
      List LF.Reaction}
    {before after : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hDispatch :
      LF.MultiStoreDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (hBefore :
      LF.StoreState.PendingMicrostepsZero
        before) :
    LF.StoreState.PendingMicrostepsZero
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
      hEarliest
      hNotPast
      hTrigger =>

      exact
        LF.ActionQueue.allMicrostepsZero_remove
          hBefore
          hRemoved

end MultiStoreDispatchStep
end LF
end Relico
