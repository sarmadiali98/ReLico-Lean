import Relico.Correctness.PayloadDispatchQueue
import Relico.Tests.PayloadSemantics

set_option autoImplicit false

namespace Relico
namespace Tests

def payloadDispatchSourceSelected :
    DTR.PendingMessage :=
  DTR.PendingMessage.scheduleWithPayload
    3
    payloadSemanticsMessage
    [
      42
    ]
    payloadSemanticsDelay

def payloadDispatchTargetSelected :
    LF.PendingAction :=
  LF.PendingAction.scheduleWithPayload
    payloadSemanticsCurrentTag
    payloadSemanticsAction
    [
      42
    ]
    payloadSemanticsDelay

theorem payload_dispatch_queue_forgets_to_ordinary :
    Correctness.QueueCorresponds
      payloadSemanticsSourceAfter.pendingMessages
      payloadSemanticsTargetAfter.pendingActions := by

  exact
    Correctness.PayloadQueueCorresponds.toQueueCorresponds
      payload_semantics_after_corresponds.pendingEvents

theorem payload_dispatch_remove_source_exists :
    ∃ selectedAction targetRemaining,
      Occurrence.RemovesOne
          selectedAction
          payloadSemanticsTargetAfter.pendingActions
          targetRemaining ∧
        Correctness.PendingPayloadCorresponds
          payloadDispatchSourceSelected
          selectedAction ∧
        Correctness.PayloadQueueCorresponds
          []
          targetRemaining := by

  have hRemove :
      Occurrence.RemovesOne
        payloadDispatchSourceSelected
        payloadSemanticsSourceAfter.pendingMessages
        [] := by

    simpa [
      payloadDispatchSourceSelected,
      payloadSemanticsSourceAfter
    ] using
      (Occurrence.RemovesOne.head
        (selected :=
          payloadDispatchSourceSelected)
        ([] : DTR.MessageBag))

  exact
    Correctness.PayloadQueueCorresponds.remove_source
      payload_semantics_after_corresponds.pendingEvents
      hRemove

theorem payload_dispatch_remove_target_exists :
    ∃ selectedMessage sourceRemaining,
      Occurrence.RemovesOne
          selectedMessage
          payloadSemanticsSourceAfter.pendingMessages
          sourceRemaining ∧
        Correctness.PendingPayloadCorresponds
          selectedMessage
          payloadDispatchTargetSelected ∧
        Correctness.PayloadQueueCorresponds
          sourceRemaining
          [] := by

  have hRemove :
      Occurrence.RemovesOne
        payloadDispatchTargetSelected
        payloadSemanticsTargetAfter.pendingActions
        [] := by

    simpa [
      payloadDispatchTargetSelected,
      payloadSemanticsTargetAfter
    ] using
      (Occurrence.RemovesOne.head
        (selected :=
          payloadDispatchTargetSelected)
        ([] : LF.ActionQueue))

  exact
    Correctness.PayloadQueueCorresponds.remove_target
      payload_semantics_after_corresponds.pendingEvents
      hRemove

theorem payload_dispatch_source_membership_exists :
    ∃ targetAction,
      targetAction ∈
          payloadSemanticsTargetAfter.pendingActions ∧
        Correctness.PendingPayloadCorresponds
          payloadDispatchSourceSelected
          targetAction := by

  apply
    Correctness.PayloadQueueCorresponds.source_mem
      payload_semantics_after_corresponds.pendingEvents

  simp [
    payloadDispatchSourceSelected,
    payloadSemanticsSourceAfter
  ]

theorem payload_dispatch_target_membership_exists :
    ∃ sourceMessage,
      sourceMessage ∈
          payloadSemanticsSourceAfter.pendingMessages ∧
        Correctness.PendingPayloadCorresponds
          sourceMessage
          payloadDispatchTargetSelected := by

  apply
    Correctness.PayloadQueueCorresponds.target_mem
      payload_semantics_after_corresponds.pendingEvents

  simp [
    payloadDispatchTargetSelected,
    payloadSemanticsTargetAfter
  ]

end Tests
end Relico
