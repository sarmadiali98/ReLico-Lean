import Relico.Correctness.PriorityMachineTiming
import Relico.Tests.MultiStoreMachine

set_option autoImplicit false

namespace Relico
namespace Tests

theorem multi_statement_source_priority_timing :
    DTR.Body.PriorityTimingWellFormed
      multiStatementSourceBefore.activeBody := by

  simp [
    multiStatementSourceBefore,
    DTR.Body.PriorityTimingWellFormed,
    DTR.Stmt.PriorityTimingWellFormed
  ]

theorem multi_statement_source_step_preserves_priority_timing :
    DTR.Body.PriorityTimingWellFormed
      multiStatementSourceAfter.activeBody := by

  exact
    DTR.MultiStoreStep.preserves_priorityTimingWellFormed
      multi_source_cross_server_send
      multi_statement_source_priority_timing

theorem multi_statement_target_pending_microsteps_zero :
    LF.StoreState.PendingMicrostepsZero
      multiStatementTargetBefore := by

  intro action hAction

  simp [
    multiStatementTargetBefore
  ] at hAction

theorem multi_statement_target_step_preserves_microsteps_zero :
    LF.StoreState.PendingMicrostepsZero
      multiStatementTargetAfter := by

  exact
    Correctness.targetMultiStoreMachineStep_preserves_pendingMicrostepsZero
      multi_target_statement_machine_step
        multiStatementInitialStatesCorrespond
        multi_statement_source_priority_timing
        multi_statement_target_pending_microsteps_zero

theorem multi_dispatch_target_step_preserves_microsteps_zero :
    LF.StoreState.PendingMicrostepsZero
      multiLfDispatchAfter := by

  exact
    Correctness.targetMultiStoreMachineStep_preserves_pendingMicrostepsZero
      multi_target_dispatch_machine_step
        multiDispatchStatesCorrespond
        (by
          simp [
            multiDtrDispatchBefore
          ])
        multi_lf_dispatch_before_pending_microsteps_zero

end Tests
end Relico
