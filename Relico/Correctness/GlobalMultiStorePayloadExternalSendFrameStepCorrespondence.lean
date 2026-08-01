import Relico.DTR.GlobalMultiStorePayloadOneStep
import Relico.LF.GlobalMultiStorePayloadOneStep
import Relico.Correctness.GlobalMultiStorePayloadExternalSendFrameCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness
namespace GlobalMultiStorePayloadExternalSendFrameStepCorrespondence

/--
Expose the existing translated successful-frame transition witness at the E4C
module boundary.

This is not the complete forward/backward correspondence theorem for the
global one-step sums. That theorem remains deferred to E4D.
-/
theorem translated_successfulFrame_transitionWitness
    (model :
      DTR.GlobalMultiStorePayloadModel)
    (sourceBefore :
      DTR.GlobalMultiStorePayloadState)
    (targetBefore :
      LF.GlobalMultiStorePayloadState)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (sourceFrame :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame)
    (payload :
      Payload)
    (foundation :
      DTR.GlobalMultiStorePayloadExternalSend.Success)
    (sourceSenderBefore :
      DTR.MultiStorePayloadState)
    (targetSenderBefore :
      LF.MultiStorePayloadState)
    (targetReceiverBefore :
      LF.MultiStorePayloadState)
    (hSourceSenderLookup :
      sourceBefore.lookupActor
          sourceFrame.statement.sender =
        some sourceSenderBefore)
    (hTargetSenderLookup :
      targetBefore.lookupActor
          sourceFrame.statement.sender =
        some targetSenderBefore)
    (hTargetReceiverLookup :
      targetBefore.lookupActor
          foundation.occurrence.receiver =
        some targetReceiverBefore)
    (hSenderStates :
      MultiStorePayloadStateCorresponds
        sourceSenderBefore
        targetSenderBefore)
    (hStatement :
      DTR.GlobalMultiStorePayloadExternalSendStatement.attempt
          model
          sourceBefore
          history
          sourceFrame.statement =
        Except.ok foundation)
    (hFoundation :
      DTR.GlobalMultiStorePayloadExternalSend.attempt
          model
          sourceBefore
          history
          (sourceFrame.statement.toRequest payload) =
        Except.ok foundation) :
    GlobalMultiStorePayloadExternalSendFrameTransitionWitness
      model
      sourceBefore
      targetBefore
      history
      sourceFrame
      payload
      foundation
      sourceSenderBefore
      targetSenderBefore
      targetReceiverBefore :=

  translated_globalMultiStorePayloadExternalSendFrame_transition
    model
    sourceBefore
    targetBefore
    history
    sourceFrame
    payload
    foundation
    sourceSenderBefore
    targetSenderBefore
    targetReceiverBefore
    hSourceSenderLookup
    hTargetSenderLookup
    hTargetReceiverLookup
    hSenderStates
    hStatement
    hFoundation

end GlobalMultiStorePayloadExternalSendFrameStepCorrespondence
end Correctness
end Relico
