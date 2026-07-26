import Relico.Tests.PriorityDispatchScheduling
import Relico.Correctness.Correspondence
import Relico.DTR.MultiStoreSemantics
import Relico.LF.MultiStoreSemantics

set_option autoImplicit false

namespace Relico
namespace Tests

def zeroDelayPriorityDelay :
    Delay :=
  {
    value := 0
  }

def zeroDelayPriorityTime :
    LogicalTime :=
  5

def zeroDelayPriorityTag :
    LF.Tag :=
  {
    time :=
      zeroDelayPriorityTime

    microstep :=
      0
  }

def zeroDelayPriorityOldLowMessage :
    DTR.PendingMessage :=
  {
    name :=
      dispatchPriorityLowName

    arrivalTime :=
      zeroDelayPriorityTime
  }

def zeroDelayPriorityNewHighMessage :
    DTR.PendingMessage :=
  {
    name :=
      dispatchPriorityHighName

    arrivalTime :=
      LogicalTime.after
        zeroDelayPriorityTime
        zeroDelayPriorityDelay
  }

def zeroDelayPriorityOldLowAction :
    LF.PendingAction :=
  {
    name :=
      Translation.actionNameFor
        dispatchPriorityLowName

    tag :=
      zeroDelayPriorityTag
  }

def zeroDelayPriorityNewHighAction :
    LF.PendingAction :=
  {
    name :=
      Translation.actionNameFor
        dispatchPriorityHighName

    tag :=
      LF.Tag.schedule
        zeroDelayPriorityTag
        zeroDelayPriorityDelay
  }

def zeroDelayPrioritySourceQueue :
    DTR.MessageBag := [
  zeroDelayPriorityOldLowMessage,
  zeroDelayPriorityNewHighMessage
]

def zeroDelayPriorityTargetQueue :
    LF.ActionQueue := [
  zeroDelayPriorityOldLowAction,
  zeroDelayPriorityNewHighAction
]

theorem zero_delay_priority_source_high_is_eligible :
    DTR.IsPriorityEligible
      dispatchPriorityServers
      zeroDelayPriorityNewHighMessage
      zeroDelayPrioritySourceQueue := by

  refine
    ⟨?_,
     ?_⟩

  · intro candidate hCandidate

    simp [
      zeroDelayPrioritySourceQueue
    ] at hCandidate

    rcases hCandidate with
      hLow | hHigh

    · subst candidate
      native_decide

    · subst candidate
      native_decide

  · intro candidate hCandidate hSameTime

    simp [
      zeroDelayPrioritySourceQueue
    ] at hCandidate

    rcases hCandidate with
      hLow | hHigh

    · subst candidate

      simpa [
        zeroDelayPriorityNewHighMessage,
        zeroDelayPriorityOldLowMessage
      ] using
        dispatch_source_high_precedes_low

    · subst candidate

      simpa [
        zeroDelayPriorityNewHighMessage
      ] using
        dispatch_source_high_precedes_itself

theorem zero_delay_priority_target_low_is_eligible :
    LF.IsReactionPriorityEligible
      dispatchPriorityReactions
      zeroDelayPriorityOldLowAction
      zeroDelayPriorityTargetQueue := by

  refine
    ⟨?_,
     ?_⟩

  · intro candidate hCandidate

    simp [
      zeroDelayPriorityTargetQueue
    ] at hCandidate

    rcases hCandidate with
      hLow | hHigh

    · subst candidate

      exact
        LF.Tag.precedesOrEqual_refl
          zeroDelayPriorityOldLowAction.tag

    · subst candidate

      apply
        LF.Tag.precedesOrEqual_same_time
          (left :=
            zeroDelayPriorityOldLowAction.tag)
          (right :=
            zeroDelayPriorityNewHighAction.tag)

      · native_decide

      · native_decide

  · intro candidate hCandidate hSameTag

    simp [
      zeroDelayPriorityTargetQueue
    ] at hCandidate

    rcases hCandidate with
      hLow | hHigh

    · subst candidate
      native_decide

    · subst candidate

      have hDifferent :
          zeroDelayPriorityNewHighAction.tag ≠
            zeroDelayPriorityOldLowAction.tag := by
        native_decide

      exact
        False.elim
          (hDifferent hSameTag)

theorem zero_delay_priority_target_high_is_not_eligible :
    ¬ LF.IsReactionPriorityEligible
        dispatchPriorityReactions
        zeroDelayPriorityNewHighAction
        zeroDelayPriorityTargetQueue := by

  intro hEligible

  have hOrder :
      LF.Tag.PrecedesOrEqual
        zeroDelayPriorityNewHighAction.tag
        zeroDelayPriorityOldLowAction.tag :=

    hEligible.1
      zeroDelayPriorityOldLowAction
      (by
        simp [
          zeroDelayPriorityTargetQueue
        ])

  change
    zeroDelayPriorityNewHighAction.tag.time <
          zeroDelayPriorityOldLowAction.tag.time ∨
      (zeroDelayPriorityNewHighAction.tag.time =
            zeroDelayPriorityOldLowAction.tag.time ∧
        zeroDelayPriorityNewHighAction.tag.microstep ≤
          zeroDelayPriorityOldLowAction.tag.microstep)
    at hOrder

  rcases hOrder with
    hEarlier | hSameTimeAndMicrostep

  · have hNotEarlier :
        ¬ zeroDelayPriorityNewHighAction.tag.time <
            zeroDelayPriorityOldLowAction.tag.time := by
      native_decide

    exact
      hNotEarlier hEarlier

  · have hNotMicrostep :
        ¬ zeroDelayPriorityNewHighAction.tag.microstep ≤
            zeroDelayPriorityOldLowAction.tag.microstep := by
      native_decide

    exact
      hNotMicrostep
        hSameTimeAndMicrostep.2

theorem zero_delay_priority_queues_correspond :
    Correctness.QueueCorresponds
      zeroDelayPrioritySourceQueue
      zeroDelayPriorityTargetQueue := by

  apply
    Correctness.QueueCorresponds.cons

  · exact {
      actionName :=
        rfl

      logicalTime :=
        rfl
    }

  apply
    Correctness.QueueCorresponds.cons

  · exact {
      actionName :=
        rfl

      logicalTime := by
        simp [
          zeroDelayPriorityNewHighMessage,
          zeroDelayPriorityNewHighAction,
          zeroDelayPriorityTag,
          zeroDelayPriorityDelay,
          zeroDelayPriorityTime,
          LF.Tag.schedule,
          LogicalTime.after
        ]
    }

  exact
    Correctness.QueueCorresponds.nil

def zeroDelayPrioritySourceBefore :
    DTR.StoreState :=
  {
    currentTime :=
      zeroDelayPriorityTime

    stateStore :=
      []

    pendingMessages := [
      zeroDelayPriorityOldLowMessage
    ]

    activeBody := [
      DTR.Stmt.selfSend
        dispatchPriorityHighName
        zeroDelayPriorityDelay
    ]
  }

def zeroDelayPrioritySourceAfter :
    DTR.StoreState :=
  {
    currentTime :=
      zeroDelayPriorityTime

    stateStore :=
      []

    pendingMessages :=
      zeroDelayPrioritySourceQueue

    activeBody :=
      []
  }

def zeroDelayPriorityTargetBefore :
    LF.StoreState :=
  {
    currentTag :=
      zeroDelayPriorityTag

    stateStore :=
      []

    pendingActions := [
      zeroDelayPriorityOldLowAction
    ]

    activeBody := [
      LF.Stmt.schedule
        (Translation.actionNameFor
          dispatchPriorityHighName)
        zeroDelayPriorityDelay
    ]
  }

def zeroDelayPriorityTargetAfter :
    LF.StoreState :=
  {
    currentTag :=
      zeroDelayPriorityTag

    stateStore :=
      []

    pendingActions :=
      zeroDelayPriorityTargetQueue

    activeBody :=
      []
  }

theorem zero_delay_priority_source_shape_is_reachable :
    DTR.MultiStoreStep
      []
      [
        dispatchPriorityLowName,
        dispatchPriorityHighName
      ]
      zeroDelayPrioritySourceBefore
      (DTR.Label.send
        dispatchPriorityHighName
        (LogicalTime.after
          zeroDelayPriorityTime
          zeroDelayPriorityDelay))
      zeroDelayPrioritySourceAfter := by

  simpa [
    zeroDelayPrioritySourceBefore,
    zeroDelayPrioritySourceAfter,
    zeroDelayPrioritySourceQueue,
    zeroDelayPriorityOldLowMessage,
    zeroDelayPriorityNewHighMessage
  ] using
    (DTR.MultiStoreStep.selfSend
      (declaredVariables := [])
      (declaredMessageServers := [
        dispatchPriorityLowName,
        dispatchPriorityHighName
      ])
      (currentTime :=
        zeroDelayPriorityTime)
      (stateStore :=
        ([] : StateStore))
      (pendingMessages := [
        zeroDelayPriorityOldLowMessage
      ])
      (targetMessage :=
        dispatchPriorityHighName)
      (delay :=
        zeroDelayPriorityDelay)
      (remaining :=
        [])
      (by simp))

theorem zero_delay_priority_target_shape_is_reachable :
    LF.MultiStoreStep
      []
      [
        Translation.actionNameFor
          dispatchPriorityLowName,
        Translation.actionNameFor
          dispatchPriorityHighName
      ]
      zeroDelayPriorityTargetBefore
      (LF.Label.schedule
        (Translation.actionNameFor
          dispatchPriorityHighName)
        (LF.Tag.schedule
          zeroDelayPriorityTag
          zeroDelayPriorityDelay))
      zeroDelayPriorityTargetAfter := by

  simpa [
    zeroDelayPriorityTargetBefore,
    zeroDelayPriorityTargetAfter,
    zeroDelayPriorityTargetQueue,
    zeroDelayPriorityOldLowAction,
    zeroDelayPriorityNewHighAction
  ] using
    (LF.MultiStoreStep.schedule
      (declaredVariables := [])
      (declaredActions := [
        Translation.actionNameFor
          dispatchPriorityLowName,
        Translation.actionNameFor
          dispatchPriorityHighName
      ])
      (currentTag :=
        zeroDelayPriorityTag)
      (stateStore :=
        ([] : StateStore))
      (pendingActions := [
        zeroDelayPriorityOldLowAction
      ])
      (targetAction :=
        Translation.actionNameFor
          dispatchPriorityHighName)
      (delay :=
        zeroDelayPriorityDelay)
      (remaining :=
        [])
      (by simp))

end Tests
end Relico
