import Relico.Correctness.PriorityTiming
import Relico.Tests.MultiStoreModelTranslation

set_option autoImplicit false

namespace Relico
namespace Tests

def priorityTimingPositiveBody :
    DTR.Body := [
  .selfSend
    resetMessageName
    ⟨2⟩
]

def priorityTimingZeroBody :
    DTR.Body := [
  .selfSend
    resetMessageName
    ⟨0⟩
]

theorem priority_timing_accepts_positive_delay :
    DTR.Body.PriorityTimingWellFormed
      priorityTimingPositiveBody := by

  simp [
    priorityTimingPositiveBody
  ]

theorem priority_timing_rejects_zero_delay :
    ¬ DTR.Body.PriorityTimingWellFormed
        priorityTimingZeroBody := by

  simp [
    priorityTimingZeroBody
  ]

def priorityTimingBaseTag :
    LF.Tag where

  time :=
    5

  microstep :=
    7

theorem positive_delay_resets_microstep :
    (LF.Tag.schedule
      priorityTimingBaseTag
      ⟨2⟩).microstep =
      0 := by

  exact
    LF.Tag.schedule_positive_microstep_zero
      priorityTimingBaseTag
      ⟨2⟩
      (by decide)

theorem zero_delay_advances_microstep :
    (LF.Tag.schedule
      priorityTimingBaseTag
      ⟨0⟩).microstep =
      8 := by

  decide

def priorityTimingLeftMessage :
    DTR.PendingMessage where

  name :=
    twoStateMessageName

  arrivalTime :=
    9

def priorityTimingRightMessage :
    DTR.PendingMessage where

  name :=
    resetMessageName

  arrivalTime :=
    9

def priorityTimingLeftAction :
    LF.PendingAction where

  name :=
    Translation.actionNameFor
      twoStateMessageName

  tag := {
    time :=
      9

    microstep :=
      0
  }

def priorityTimingRightAction :
    LF.PendingAction where

  name :=
    Translation.actionNameFor
      resetMessageName

  tag := {
    time :=
      9

    microstep :=
      0
  }

theorem priorityTimingLeftCorresponds :
    Correctness.PendingCorresponds
      priorityTimingLeftMessage
      priorityTimingLeftAction := by

  exact {
    actionName :=
      rfl

    logicalTime :=
      rfl
  }

theorem priorityTimingRightCorresponds :
    Correctness.PendingCorresponds
      priorityTimingRightMessage
      priorityTimingRightAction := by

  exact {
    actionName :=
      rfl

    logicalTime :=
      rfl
  }

theorem equal_source_times_and_zero_microsteps_give_equal_tags :
    priorityTimingLeftAction.tag =
      priorityTimingRightAction.tag := by

  exact
    Correctness.PendingCorresponds.targetTag_eq_of_sameTime_and_zero
      priorityTimingLeftCorresponds
      priorityTimingRightCorresponds
      rfl
      rfl
      rfl

def priorityTimingQueue :
    LF.ActionQueue := [
  priorityTimingLeftAction,
  priorityTimingRightAction
]

theorem priority_timing_queue_has_zero_microsteps :
    LF.ActionQueue.AllMicrostepsZero
      priorityTimingQueue := by

  intro action hMember

  simp [
    priorityTimingQueue
  ] at hMember

  rcases hMember with
    hLeft | hRight

  · subst action
    rfl

  · subst action
    rfl

theorem positive_schedule_preserves_zero_microsteps :
    LF.ActionQueue.AllMicrostepsZero
      (priorityTimingQueue ++ [
        {
          name :=
            Translation.actionNameFor
              resetMessageName

          tag :=
            LF.Tag.schedule
              priorityTimingBaseTag
              ⟨3⟩
        }
      ]) := by

  exact
    LF.MultiStoreStep.schedule_preserves_pendingMicrostepsZero
      priorityTimingBaseTag
      priorityTimingQueue
      (Translation.actionNameFor
        resetMessageName)
      ⟨3⟩
      priority_timing_queue_has_zero_microsteps
      (by decide)

end Tests
end Relico
