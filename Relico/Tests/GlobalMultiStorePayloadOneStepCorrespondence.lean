import Relico.Correctness.GlobalMultiStorePayloadOneStepCorrespondence

set_option autoImplicit false

namespace Relico
namespace Tests
namespace GlobalMultiStorePayloadOneStepCorrespondence

theorem externalSendFrame_forward_regression
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key}
    {sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadState}
    {targetBefore :
      LF.GlobalMultiStorePayloadState}
    {sourceFrame :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame}
    (hCompatible :
      Correctness.GlobalMultiStorePayloadOneStepCorrespondence.ForwardExternalSendFrameCompatible
        sourceModel
        targetProgram
        history
        sourceBefore
        sourceAfter
        targetBefore
        sourceFrame) :
    ∃ targetAfter,
      LF.GlobalMultiStorePayloadOneStep.Step
          targetProgram
          targetBefore
          targetAfter ∧
        Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter :=

  Correctness.GlobalMultiStorePayloadOneStepCorrespondence.externalSendFrame_forward
    hCompatible

theorem externalSendFrame_backward_regression
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key}
    {sourceBefore :
      DTR.GlobalMultiStorePayloadState}
    {targetAfter :
      LF.GlobalMultiStorePayloadState}
    {targetFrame :
      LF.GlobalMultiStorePayloadExternalSendFrame.Frame}
    (hCompatible :
      Correctness.GlobalMultiStorePayloadOneStepCorrespondence.BackwardExternalSendFrameCompatible
        sourceModel
        targetProgram
        history
        sourceBefore
        targetAfter
        targetFrame) :
    ∃ sourceAfter,
      DTR.GlobalMultiStorePayloadOneStep.Step
          sourceModel
          history
          sourceBefore
          sourceAfter ∧
        Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter :=

  Correctness.GlobalMultiStorePayloadOneStepCorrespondence.externalSendFrame_backward
    hCompatible

theorem oneStep_forward_regression
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key}
    {sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadState}
    {targetBefore :
      LF.GlobalMultiStorePayloadState}
    (hSourceStep :
      DTR.GlobalMultiStorePayloadOneStep.Step
        sourceModel
        history
        sourceBefore
        sourceAfter)
    (hGlobal :
      Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore
        targetBefore)
    (hFrameCompatible :
      ∀
        {sourceFrame :
          DTR.GlobalMultiStorePayloadExternalSendFrame.Frame}
        {result :
          DTR.GlobalMultiStorePayloadExternalSendFrame.Success},
        DTR.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep
            sourceModel
            history
            sourceBefore
            sourceFrame
            result
            sourceAfter →
          Correctness.GlobalMultiStorePayloadOneStepCorrespondence.ForwardExternalSendFrameCompatible
            sourceModel
            targetProgram
            history
            sourceBefore
            sourceAfter
            targetBefore
            sourceFrame) :
    ∃ targetAfter,
      LF.GlobalMultiStorePayloadOneStep.Step
          targetProgram
          targetBefore
          targetAfter ∧
        Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter :=

  Correctness.GlobalMultiStorePayloadOneStepCorrespondence.oneStep_forward
    hSourceStep
    hGlobal
    hFrameCompatible

theorem oneStep_backward_regression
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key}
    {sourceBefore :
      DTR.GlobalMultiStorePayloadState}
    {targetBefore targetAfter :
      LF.GlobalMultiStorePayloadState}
    (hTargetStep :
      LF.GlobalMultiStorePayloadOneStep.Step
        targetProgram
        targetBefore
        targetAfter)
    (hGlobal :
      Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore
        targetBefore)
    (hFrameCompatible :
      ∀
        {targetOccurrence :
          LF.GlobalMultiStorePayloadExternalSend.Occurrence}
        {targetFrame :
          LF.GlobalMultiStorePayloadExternalSendFrame.Frame},
        LF.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep
            targetBefore
            targetOccurrence
            targetFrame
            targetAfter →
          Correctness.GlobalMultiStorePayloadOneStepCorrespondence.BackwardExternalSendFrameCompatible
            sourceModel
            targetProgram
            history
            sourceBefore
            targetAfter
            targetFrame) :
    ∃ sourceAfter,
      DTR.GlobalMultiStorePayloadOneStep.Step
          sourceModel
          history
          sourceBefore
          sourceAfter ∧
        Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter :=

  Correctness.GlobalMultiStorePayloadOneStepCorrespondence.oneStep_backward
    hTargetStep
    hGlobal
    hFrameCompatible

end GlobalMultiStorePayloadOneStepCorrespondence
end Tests
end Relico
