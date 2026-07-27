import Relico.Correctness.DetailedBoundPayloadForwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadForwardWeakSimulation

theorem target_tag_order_interface
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.BoundPayloadDispatchStep
        reaction
        before
        selectedAction
        after) :
    LF.Tag.PrecedesOrEqual
      before.currentTag
      after.currentTag := by

  exact
    Correctness.lfBoundPayloadDispatch_tagOrder
      hDispatch

theorem target_microstep_order_interface
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.BoundPayloadDispatchStep
        reaction
        before
        selectedAction
        after)
    (hSameTime :
      before.currentTag.time =
        after.currentTag.time) :
    before.currentTag.microstep ≤
      after.currentTag.microstep := by

  exact
    Correctness.lfBoundPayloadDispatch_microstep_le_of_sameTime
      hDispatch
      hSameTime

theorem statement_forward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {sourceLabel : DTR.BoundPayloadLabel}
    {targetBefore : LF.BoundPayloadState}
    (hSourceStep :
      DTR.BoundPayloadStep
        server.name
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    Correctness.DetailedBoundPayloadForwardMatch
      server
      .tau
      (.stable sourceAfter)
      (.stable targetBefore) := by

  exact
    Correctness.detailedBoundPayload_statement_forward_weak
      hSourceStep
      hStates

theorem timeAdvance_forward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {targetBefore : LF.BoundPayloadState}
    (hSourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter)
    (hFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore))
    (hCompatible :
      Correctness.BoundPayloadForwardDispatchCompatible
        selectedMessage
        sourceAfter.pendingMessages
        targetBefore) :
    Correctness.DetailedBoundPayloadForwardMatch
      server
      (.timeAdvance
        sourceBefore.currentTime
        sourceAfter.currentTime)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        hSourceDispatch)
      (.stable targetBefore) := by

  exact
    Correctness.detailedBoundPayload_timeAdvance_forward_weak
      hSourceDispatch
      hFuture
      hStates
      hCompatible

theorem consume_afterTime_forward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)) :
    Correctness.DetailedBoundPayloadForwardMatch
      server
      (.consume selectedMessage)
      (.stable sourceAfter)
      (.afterTime
        targetBefore
        selectedAction
        targetAfter
        targetDispatch) := by

  exact
    Correctness.detailedBoundPayload_consume_afterTime_forward_weak
      hStates

theorem consume_ready_forward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          sourceDispatch)
        (.dispatchReady
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)) :
    Correctness.DetailedBoundPayloadForwardMatch
      server
      (.consume selectedMessage)
      (.stable sourceAfter)
      (.dispatchReady
        targetBefore
        selectedAction
        targetAfter
        targetDispatch) := by

  exact
    Correctness.detailedBoundPayload_consume_ready_forward_weak
      hStates

theorem consumeNow_forward_interface
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {targetBefore : LF.BoundPayloadState}
    (hSourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter)
    (hSameSourceTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime)
    (hStates :
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore))
    (hCompatible :
      Correctness.BoundPayloadForwardDispatchCompatible
        selectedMessage
        sourceAfter.pendingMessages
        targetBefore) :
    Correctness.DetailedBoundPayloadForwardMatch
      server
      (.consume selectedMessage)
      (.stable sourceAfter)
      (.stable targetBefore) := by

  exact
    Correctness.detailedBoundPayload_consumeNow_forward_weak
      hSourceDispatch
      hSameSourceTime
      hStates
      hCompatible

theorem target_corresponds_interface
    {server : DTR.PayloadMessageServer}
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {sourceAfter :
      DTR.DetailedBoundPayloadState server}
    {targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    (hMatch :
      Correctness.DetailedBoundPayloadForwardMatch
        server
        sourceLabel
        sourceAfter
        targetBefore) :
    ∃ targetAfter :
        LF.DetailedBoundPayloadState
          (Translation.compilePayloadMessageServer
            server),
      Correctness.DetailedBoundPayloadStateCorresponds
        server
        sourceAfter
        targetAfter := by

  exact
    Correctness.DetailedBoundPayloadForwardMatch.target_corresponds
      hMatch

end DetailedBoundPayloadForwardWeakSimulation
end Tests
end Relico
