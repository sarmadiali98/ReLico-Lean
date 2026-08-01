import Relico.DTR.GlobalMultiStorePayloadOneStep
import Relico.LF.GlobalMultiStorePayloadOneStep
import Relico.Correctness.GlobalMultiStorePayloadExternalSendFrameStepCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadOneStep

theorem source_externalSendFrame_constructor
    {model :
      DTR.GlobalMultiStorePayloadModel}
    {history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key}
    {before :
      DTR.GlobalMultiStorePayloadState}
    {frame :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame}
    {result :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Success}
    (hAttempt :
      DTR.GlobalMultiStorePayloadExternalSendFrame.attempt
          model
          before
          history
          frame =
        Except.ok result) :
    DTR.GlobalMultiStorePayloadOneStep.Step
      model
      history
      before
      result.state :=

  DTR.GlobalMultiStorePayloadOneStep.Step.externalSendFrame
    (DTR.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep.success
      hAttempt)

theorem source_dispatch_constructor
    {model :
      DTR.GlobalMultiStorePayloadModel}
    {history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key}
    {actorName :
      ActorName}
    {before after :
      DTR.GlobalMultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    (hDispatch :
      DTR.GlobalMultiStorePayloadDispatch.Step
        model
        actorName
        before
        selectedMessage
        selectedServer
        after) :
    DTR.GlobalMultiStorePayloadOneStep.Step
      model
      history
      before
      after :=

  DTR.GlobalMultiStorePayloadOneStep.Step.dispatch
    hDispatch

theorem target_externalSendFrame_constructor
    {program :
      LF.GlobalMultiStorePayloadProgram}
    {before after :
      LF.GlobalMultiStorePayloadState}
    {occurrence :
      LF.GlobalMultiStorePayloadExternalSend.Occurrence}
    {frame :
      LF.GlobalMultiStorePayloadExternalSendFrame.Frame}
    (hApply :
      LF.GlobalMultiStorePayloadExternalSendFrame.apply?
          before
          occurrence
          frame =
        some after) :
    LF.GlobalMultiStorePayloadOneStep.Step
      program
      before
      after :=

  LF.GlobalMultiStorePayloadOneStep.Step.externalSendFrame
    (LF.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep.applied
      hApply)

theorem target_dispatch_constructor
    {program :
      LF.GlobalMultiStorePayloadProgram}
    {actorName :
      ActorName}
    {before after :
      LF.GlobalMultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hDispatch :
      LF.GlobalMultiStorePayloadDispatch.Step
        program
        actorName
        before
        selectedAction
        selectedReaction
        after) :
    LF.GlobalMultiStorePayloadOneStep.Step
      program
      before
      after :=

  LF.GlobalMultiStorePayloadOneStep.Step.dispatch
    hDispatch

theorem source_oneStep_inversion
    {model :
      DTR.GlobalMultiStorePayloadModel}
    {history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key}
    {before after :
      DTR.GlobalMultiStorePayloadState}
    (hStep :
      DTR.GlobalMultiStorePayloadOneStep.Step
        model
        history
        before
        after) :
    (∃ frame result,
      DTR.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep
        model
        history
        before
        frame
        result
        after) ∨
    (∃ actorName selectedMessage selectedServer,
      DTR.GlobalMultiStorePayloadDispatch.Step
        model
        actorName
        before
        selectedMessage
        selectedServer
        after) :=

  Iff.mp
    DTR.GlobalMultiStorePayloadOneStep.Step.iff_externalSendFrame_or_dispatch
    hStep

theorem target_oneStep_inversion
    {program :
      LF.GlobalMultiStorePayloadProgram}
    {before after :
      LF.GlobalMultiStorePayloadState}
    (hStep :
      LF.GlobalMultiStorePayloadOneStep.Step
        program
        before
        after) :
    (∃ occurrence frame,
      LF.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep
        before
        occurrence
        frame
        after) ∨
    (∃ actorName selectedAction selectedReaction,
      LF.GlobalMultiStorePayloadDispatch.Step
        program
        actorName
        before
        selectedAction
        selectedReaction
        after) :=

  Iff.mp
    LF.GlobalMultiStorePayloadOneStep.Step.iff_externalSendFrame_or_dispatch
    hStep

end GlobalMultiStorePayloadOneStep
end Tests
end Relico
