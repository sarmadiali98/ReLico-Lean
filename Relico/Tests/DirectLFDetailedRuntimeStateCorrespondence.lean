import Relico.Correctness.DirectLFDetailedRuntimeStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFDetailedRuntimeStateCorrespondence

/--
Regression for the stable detailed phase.
-/
theorem stable_phase_iff
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState :
      LF.StoreState} :
    Correctness.DirectLFDetailedRuntimeStateCorresponds
          messageServers
          (.stable sourceState)
          (.stable targetState) ↔
      Correctness.DirectLFRuntimeStateCorresponds
        messageServers
        sourceState
        targetState :=
  Correctness.directLFDetailedRuntime_stable_iff

/--
Regression for the future-after-time phase.
-/
theorem future_after_time_phase
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hSourceFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hWitness :
      Correctness.DirectLFDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    Correctness.DirectLFDetailedRuntimeStateCorresponds
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
  Correctness.directLFDetailedRuntime_futureAfterTime
    hSourceFuture
    hWitness

/--
Regression for the future dispatch-ready phase.
-/
theorem future_ready_phase
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hSourceFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hPositiveMicrostep :
      0 <
        targetAfter.currentTag.microstep)
    (hWitness :
      Correctness.DirectLFDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    Correctness.DirectLFDetailedRuntimeStateCorresponds
      messageServers
      (.dispatchReady
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        sourceDispatch)
      (.dispatchReady
        targetBefore
        selectedAction
        selectedReaction
        targetAfter
        targetDispatch) :=
  Correctness.directLFDetailedRuntime_futureReady
    hSourceFuture
    hPositiveMicrostep
    hWitness

/--
Regression for the same-time later-microstep stuttering phase.
-/
theorem same_time_microstep_ahead_phase
    {messageServers :
      List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.StoreState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MessageServer}
    (sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    {targetBefore targetAfter :
      LF.StoreState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hSourceSameTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime)
    (hTargetLaterMicrostep :
      targetBefore.currentTag.microstep <
        targetAfter.currentTag.microstep)
    (hWitness :
      Correctness.DirectLFDetailedRuntimeDispatchWitnessCorresponds
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        targetBefore
        selectedAction
        selectedReaction
        targetAfter) :
    Correctness.DirectLFDetailedRuntimeStateCorresponds
      messageServers
      (.stable sourceBefore)
      (.dispatchReady
        targetBefore
        selectedAction
        selectedReaction
        targetAfter
        targetDispatch) :=
  Correctness.directLFDetailedRuntime_sameTimeMicrostepAhead
    sourceDispatch
    hSourceSameTime
    hTargetLaterMicrostep
    hWitness

#check
  Correctness.DirectLFDetailedRuntimeStateCorresponds

#check
  Correctness.DirectLFDetailedRuntimeDispatchWitnessCorresponds

#check
  Correctness.directLFDetailedRuntime_dispatch_forward

#check
  Correctness.directLFDetailedRuntime_dispatch_backward

#check stable_phase_iff
#check future_after_time_phase
#check future_ready_phase
#check same_time_microstep_ahead_phase

end DirectLFDetailedRuntimeStateCorrespondence
end Tests
end Relico
