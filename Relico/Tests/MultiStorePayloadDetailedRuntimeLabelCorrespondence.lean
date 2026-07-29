import Relico.Correctness.MultiStorePayloadDetailedRuntimeLabelCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace MultiStorePayloadDetailedRuntimeLabelCorrespondence

theorem stable_runtime_iff
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceState :
      DTR.MultiStorePayloadState}
    {targetState :
      LF.MultiStorePayloadState} :
    Correctness.MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          (.stable sourceState)
          (.stable targetState) ↔
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState :=

  Correctness.multiStorePayloadDetailedRuntime_stable_iff

theorem forward_dispatch_packages_detailed_witness
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetBefore :
      LF.MultiStorePayloadState}
    (hSourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore) :
    ∃ selectedAction targetAfter,
      LF.MultiStorePayloadDispatchStep
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetBefore
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetAfter ∧
        Correctness.MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          (Translation.compileMultiStorePayloadReaction
            selectedServer)
          targetAfter :=

  Correctness.multiStorePayloadDetailedRuntime_dispatch_forward
    hSourceDispatch
    hRuntime

theorem backward_dispatch_packages_detailed_witness
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hRuntime :
      Correctness.MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore) :
    ∃ selectedMessage selectedServer sourceAfter,
      DTR.MultiStorePayloadDispatchStep
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter ∧
        Correctness.MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
          messageServers
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          targetBefore
          selectedAction
          selectedReaction
          targetAfter :=

  Correctness.multiStorePayloadDetailedRuntime_dispatch_backward
    hTargetDispatch
    hRuntime

theorem consume_label_preserves_exact_payload
    {sourceMessage :
      DTR.PendingMessage}
    {sourceServer :
      DTR.MultiStorePayloadMessageServer}
    {targetAction :
      LF.PendingAction}
    {targetReaction :
      LF.MultiStorePayloadReaction}
    (hLabels :
      Correctness.MultiStorePayloadDetailedLabelCorresponds
        (.consume
          sourceMessage
          sourceServer)
        (.consume
          targetAction
          targetReaction)) :
    targetAction.payload =
      sourceMessage.payload :=

  hLabels.consume_payload_eq

theorem target_microstep_corresponds_to_source_tau
    (before after :
      LF.Tag) :
    Correctness.MultiStorePayloadDetailedLabelCorresponds
      DTR.DetailedMultiStorePayloadLabel.tau
      (LF.DetailedMultiStorePayloadLabel.microstepAdvance
        before
        after) :=

  Correctness.MultiStorePayloadDetailedLabelCorresponds.microstep
    before
    after

theorem witness_exposes_metric_times
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hWitness :
      Correctness.MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    targetBefore.currentTag.time =
          sourceBefore.currentTime ∧
      targetAfter.currentTag.time =
          sourceAfter.currentTime :=

  Correctness.multiStorePayloadDetailedRuntimeDispatchWitness_times
    hWitness

theorem future_after_time_phase
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {sourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hWitness :
      Correctness.MultiStorePayloadDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    Correctness.MultiStorePayloadDetailedRuntimeStateCorresponds
      messageServers
      (.dispatchReady
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        sourceDispatch)
      (.afterTime
        targetBefore
        selectedAction
        selectedReaction
        targetAfter
        targetDispatch) :=

  Correctness.multiStorePayloadDetailedRuntime_futureAfterTime
    hFuture
    hWitness

end MultiStorePayloadDetailedRuntimeLabelCorrespondence
end Tests
end Relico
