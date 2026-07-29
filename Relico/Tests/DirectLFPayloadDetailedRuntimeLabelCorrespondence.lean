import Relico.Correctness.DirectLFPayloadDetailedLabelCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DirectLFPayloadDetailedRuntimeLabelCorrespondence

#check Correctness.DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds
#check Correctness.DirectLFPayloadDetailedRuntimeStateCorresponds
#check Correctness.directLFPayloadDetailedRuntime_stable_iff
#check Correctness.directLFPayloadDetailedRuntimeDispatchWitness_mk
#check Correctness.directLFPayloadDetailedRuntimeDispatchWitness_times
#check Correctness.directLFPayloadDetailedRuntime_dispatch_forward
#check Correctness.directLFPayloadDetailedRuntime_dispatch_backward
#check Correctness.directLFPayloadDetailedRuntime_futureAfterTime
#check Correctness.directLFPayloadDetailedRuntime_futureReady
#check Correctness.directLFPayloadDetailedRuntime_sameTimeMicrostepAhead
#check Correctness.DirectLFPayloadDetailedRuntimeDispatchWitnessCorresponds.toDetailedRuntimeDispatchWitnessCorresponds
#check Correctness.DirectLFPayloadDetailedRuntimeStateCorresponds.toDetailedRuntimeStateCorresponds

#check Correctness.DirectLFPayloadDetailedLabelCorresponds
#check Correctness.DirectLFPayloadDetailedLabelCorresponds.tau
#check Correctness.DirectLFPayloadDetailedLabelCorresponds.microstep
#check Correctness.DirectLFPayloadDetailedLabelCorresponds.timeAdvance
#check Correctness.DirectLFPayloadDetailedLabelCorresponds.consume
#check Correctness.DirectLFPayloadDetailedLabelCorresponds.toDetailedLabelCorresponds
#check Correctness.DirectLFPayloadDetailedLabelCorresponds.consume_payload_eq

example
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState : LF.StoreState}
    (hStates :
      Correctness.DirectLFPayloadRuntimeStateCorresponds
        messageServers
        sourceState
        targetState) :
    Correctness.DirectLFPayloadDetailedRuntimeStateCorresponds
      messageServers
      (.stable sourceState)
      (.stable targetState) := by

  exact
    (Correctness.directLFPayloadDetailedRuntime_stable_iff).2
      hStates

example
    {sourceMessage : DTR.PendingMessage}
    {sourceServer : DTR.MessageServer}
    {targetAction : LF.PendingAction}
    {targetReaction : LF.Reaction}
    (hPending :
      Correctness.PendingPayloadCorresponds
        sourceMessage
        targetAction)
    (hReaction :
      targetReaction =
        Translation.compileMessageReaction
          sourceServer) :
    Correctness.DirectLFPayloadDetailedLabelCorresponds
      (DTR.DetailedMultiStoreLabel.consume
        sourceMessage
        sourceServer)
      (LF.DetailedMultiStoreLabel.consume
        targetAction
        targetReaction) := by

  exact
    Correctness.DirectLFPayloadDetailedLabelCorresponds.consume
      hPending
      hReaction

example
    {sourceMessage : DTR.PendingMessage}
    {sourceServer : DTR.MessageServer}
    {targetAction : LF.PendingAction}
    {targetReaction : LF.Reaction}
    (hLabels :
      Correctness.DirectLFPayloadDetailedLabelCorresponds
        (DTR.DetailedMultiStoreLabel.consume
          sourceMessage
          sourceServer)
        (LF.DetailedMultiStoreLabel.consume
          targetAction
          targetReaction)) :
    targetAction.payload =
      sourceMessage.payload := by

  exact
    Correctness.DirectLFPayloadDetailedLabelCorresponds.consume_payload_eq
      hLabels

end DirectLFPayloadDetailedRuntimeLabelCorrespondence
end Tests
end Relico
