import Relico.Correctness.PriorityEligibility
import Relico.Tests.PriorityDispatchScheduling

set_option autoImplicit false

namespace Relico
namespace Tests

theorem dispatch_low_pending_corresponds :
    Correctness.PendingCorresponds
      dispatchLowMessage
      dispatchLowAction := by

  exact {
    actionName :=
      rfl

    logicalTime :=
      rfl
  }

theorem dispatch_high_pending_corresponds :
    Correctness.PendingCorresponds
      dispatchHighMessage
      dispatchHighAction := by

  exact {
    actionName :=
      rfl

    logicalTime :=
      rfl
  }

theorem dispatch_priority_queues_correspond :
    Correctness.QueueCorresponds
      dispatchSourcePriorityQueue
      dispatchTargetPriorityQueue := by

  exact
    Correctness.QueueCorresponds.cons
      dispatch_low_pending_corresponds
      (Correctness.QueueCorresponds.cons
        dispatch_high_pending_corresponds
        Correctness.QueueCorresponds.nil)

theorem dispatch_target_priority_queue_all_microsteps_zero :
    LF.ActionQueue.AllMicrostepsZero
      dispatchTargetPriorityQueue := by

  intro targetAction
  intro hTargetAction

  simp [
    dispatchTargetPriorityQueue
  ] at hTargetAction

  rcases hTargetAction with
    hLow | hHigh

  · subst targetAction
    rfl

  · subst targetAction
    rfl

theorem dispatch_source_priority_transports_forward :
    LF.IsReactionPriorityEligible
      dispatchPriorityReactions
      dispatchHighAction
      dispatchTargetPriorityQueue := by

  simpa [
    dispatchPriorityReactions
  ] using
    Correctness.sourcePriorityEligible_implies_targetReactionPriorityEligible
        (messageServers :=
          dispatchPriorityServers)
        dispatch_priority_queues_correspond
        dispatch_high_pending_corresponds
        (LF.IsReactionPriorityEligible.isEarliest
          dispatch_target_high_is_reaction_priority_eligible)
        dispatch_source_high_is_priority_eligible

theorem dispatch_target_priority_transports_backward :
    DTR.IsPriorityEligible
      dispatchPriorityServers
      dispatchHighMessage
      dispatchSourcePriorityQueue := by

  exact
    Correctness.targetReactionPriorityEligible_implies_sourcePriorityEligible
        dispatch_priority_queues_correspond
        dispatch_high_pending_corresponds
        (by
          simp [
            dispatchTargetPriorityQueue
          ])
        dispatch_target_high_is_reaction_priority_eligible
        dispatch_target_priority_queue_all_microsteps_zero

theorem dispatch_source_earliest_transports_at_microstep_zero :
    LF.IsEarliest
      dispatchHighAction
      dispatchTargetPriorityQueue := by

  exact
    Correctness.sourceEarliest_implies_targetEarliest_of_allMicrostepsZero
        dispatch_priority_queues_correspond
        dispatch_high_pending_corresponds
        (by
          simp [
            dispatchTargetPriorityQueue
          ])
        (DTR.IsPriorityEligible.isEarliest
          dispatch_source_high_is_priority_eligible)
        dispatch_target_priority_queue_all_microsteps_zero

end Tests
end Relico
