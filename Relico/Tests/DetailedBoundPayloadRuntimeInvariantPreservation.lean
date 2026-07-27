import Relico.Correctness.DetailedBoundPayloadRuntimeInvariantPreservation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadRuntimeInvariantPreservation

#check Correctness.compiledBoundPayloadScheduleHead_positive
#check Correctness.boundPayloadStep_preserves_priorityTimingWellFormed
#check Correctness.targetBoundPayloadStep_preserves_runtimeInvariant
#check Correctness.targetBoundPayloadDispatch_preserves_runtimeInvariant
#check Correctness.boundPayloadDispatch_establishes_priorityTimingWellFormed
#check Correctness.boundPayloadStep_forward_preserves_runtimeInvariants
#check Correctness.boundPayloadDispatch_forward_preserves_runtimeInvariants

theorem source_statement_timing_interface
    {declaredMessageServer : MsgName}
    {before after : DTR.BoundPayloadState}
    {label : DTR.BoundPayloadLabel}
    (hStep :
      DTR.BoundPayloadStep
        declaredMessageServer
        before
        label
        after)
    (hTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        before.activeBody) :
    DTR.BoundPayloadBody.PriorityTimingWellFormed
      after.activeBody := by

  exact
    Correctness.boundPayloadStep_preserves_priorityTimingWellFormed
      hStep
      hTiming

theorem target_statement_invariant_interface
    {declaredMessageServer : MsgName}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter : LF.BoundPayloadState}
    {targetLabel : LF.BoundPayloadLabel}
    (hTargetStep :
      LF.BoundPayloadStep
        (Translation.actionNameFor
          declaredMessageServer)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      Correctness.BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSourceTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceBefore.activeBody)
    (hTargetInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetBefore) :
    LF.BoundPayloadState.RuntimeInvariant
      targetAfter := by

  exact
    Correctness.targetBoundPayloadStep_preserves_runtimeInvariant
      hTargetStep
      hStates
      hSourceTiming
      hTargetInvariant

theorem target_dispatch_invariant_interface
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.BoundPayloadDispatchStep
        reaction
        before
        selectedAction
        after)
    (hBefore :
      LF.BoundPayloadState.RuntimeInvariant
        before) :
    LF.BoundPayloadState.RuntimeInvariant
      after := by

  exact
    Correctness.targetBoundPayloadDispatch_preserves_runtimeInvariant
      hDispatch
      hBefore

theorem source_dispatch_timing_interface
    {server : DTR.PayloadMessageServer}
    {before after : DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    (hDispatch :
      DTR.BoundPayloadDispatchStep
        server
        before
        selectedMessage
        after)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
    DTR.BoundPayloadBody.PriorityTimingWellFormed
      after.activeBody := by

  exact
    Correctness.boundPayloadDispatch_establishes_priorityTimingWellFormed
      hDispatch
      hServerTiming

theorem matched_statement_package_interface
    {declaredMessageServer : MsgName}
    {sourceBefore sourceAfter : DTR.BoundPayloadState}
    {sourceLabel : DTR.BoundPayloadLabel}
    {targetBefore : LF.BoundPayloadState}
    (hSourceStep :
      DTR.BoundPayloadStep
        declaredMessageServer
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      Correctness.BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSourceTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceBefore.activeBody)
    (hTargetInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetBefore) :
    ∃ targetLabel targetAfter,
      LF.BoundPayloadStep
          (Translation.actionNameFor
            declaredMessageServer)
          targetBefore
          targetLabel
          targetAfter ∧
        Correctness.BoundPayloadLabelCorresponds
          sourceLabel
          targetLabel ∧
        Correctness.BoundPayloadStateCorresponds
          sourceAfter
          targetAfter ∧
        DTR.BoundPayloadBody.PriorityTimingWellFormed
          sourceAfter.activeBody ∧
        LF.BoundPayloadState.RuntimeInvariant
          targetAfter := by

  exact
    Correctness.boundPayloadStep_forward_preserves_runtimeInvariants
      hSourceStep
      hStates
      hSourceTiming
      hTargetInvariant

theorem matched_dispatch_package_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter : DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {targetBefore : LF.BoundPayloadState}
    (hSourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter)
    (hStates :
      Correctness.BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body)
    (hTargetInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetBefore) :
    ∃ selectedAction targetAfter,
      LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter ∧
        Correctness.PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        Correctness.BoundPayloadStateCorresponds
          sourceAfter
          targetAfter ∧
        DTR.BoundPayloadBody.PriorityTimingWellFormed
          sourceAfter.activeBody ∧
        LF.BoundPayloadState.RuntimeInvariant
          targetAfter := by

  exact
    Correctness.boundPayloadDispatch_forward_preserves_runtimeInvariants
      hSourceDispatch
      hStates
      hServerTiming
      hTargetInvariant

end DetailedBoundPayloadRuntimeInvariantPreservation
end Tests
end Relico
