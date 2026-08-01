import Relico.DTR.GlobalMultiStorePayloadOneStep
import Relico.LF.GlobalMultiStorePayloadOneStep
import Relico.Correctness.GlobalMultiStorePayloadExternalSendFrameCorrespondence
import Relico.Correctness.GlobalMultiStorePayloadDispatchCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness
namespace GlobalMultiStorePayloadOneStepCorrespondence

/--
Evidence required to lift a successful source external-send frame step.

The existing frame-transition witness supplies the translated target
execution. Complete correspondence of the resulting global states is carried
explicitly because the existing frame witness does not package that relation.
-/
structure ForwardExternalSendFrameCompatible
    (sourceModel :
      DTR.GlobalMultiStorePayloadModel)
    (targetProgram :
      LF.GlobalMultiStorePayloadProgram)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadState)
    (targetBefore :
      LF.GlobalMultiStorePayloadState)
    (sourceFrame :
      DTR.GlobalMultiStorePayloadExternalSendFrame.Frame) :
    Type where

  payload :
    Payload

  foundation :
    DTR.GlobalMultiStorePayloadExternalSend.Success

  sourceSenderBefore :
    DTR.MultiStorePayloadState

  targetSenderBefore :
    LF.MultiStorePayloadState

  targetReceiverBefore :
    LF.MultiStorePayloadState

  witness :
    GlobalMultiStorePayloadExternalSendFrameTransitionWitness
      sourceModel
      sourceBefore
      targetBefore
      history
      sourceFrame
      payload
      foundation
      sourceSenderBefore
      targetSenderBefore
      targetReceiverBefore

  afterCorresponds :
    GlobalMultiStorePayloadRuntimeStateCorresponds
      sourceModel
      targetProgram
      sourceAfter
      (globalMultiStorePayloadExternalSendFrameTargetAfter
        targetBefore
        targetReceiverBefore
        foundation
        sourceFrame
        targetSenderBefore)

/--
Evidence required to reflect a successful target external-send frame step.

The current frame API exports no target-to-source reflection theorem.
Consequently, the corresponding source frame step and complete global
post-state correspondence are represented explicitly.
-/
structure BackwardExternalSendFrameCompatible
    (sourceModel :
      DTR.GlobalMultiStorePayloadModel)
    (targetProgram :
      LF.GlobalMultiStorePayloadProgram)
    (history :
      List DTR.GlobalMultiStorePayloadExternalSend.Key)
    (sourceBefore :
      DTR.GlobalMultiStorePayloadState)
    (targetAfter :
      LF.GlobalMultiStorePayloadState)
    (targetFrame :
      LF.GlobalMultiStorePayloadExternalSendFrame.Frame) :
    Type where

  sourceFrame :
    DTR.GlobalMultiStorePayloadExternalSendFrame.Frame

  result :
    DTR.GlobalMultiStorePayloadExternalSendFrame.Success

  sourceAfter :
    DTR.GlobalMultiStorePayloadState

  frameCorresponds :
    GlobalMultiStorePayloadExternalSendFrameCorresponds
      sourceFrame
      targetFrame

  sourceStep :
    DTR.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep
      sourceModel
      history
      sourceBefore
      sourceFrame
      result
      sourceAfter

  afterCorresponds :
    GlobalMultiStorePayloadRuntimeStateCorresponds
      sourceModel
      targetProgram
      sourceAfter
      targetAfter

/--
A compatible source external-send frame branch produces a target E4C
one-step transition and globally corresponding post-state.
-/
theorem externalSendFrame_forward
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
      ForwardExternalSendFrameCompatible
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
        GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter := by

  rcases hCompatible with
    ⟨payload,
     foundation,
     sourceSenderBefore,
     targetSenderBefore,
     targetReceiverBefore,
     hWitness,
     hAfter⟩

  exact
    ⟨globalMultiStorePayloadExternalSendFrameTargetAfter
       targetBefore
       targetReceiverBefore
       foundation
       sourceFrame
       targetSenderBefore,
     LF.GlobalMultiStorePayloadOneStep.Step.externalSendFrame
       (LF.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep.applied
         hWitness.targetExecution),
     hAfter⟩

/--
A compatible target external-send frame branch reflects to a source E4C
one-step transition and globally corresponding post-state.
-/
theorem externalSendFrame_backward
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
      BackwardExternalSendFrameCompatible
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
        GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter := by

  rcases hCompatible with
    ⟨sourceFrame,
     result,
     sourceAfter,
     _hFrameCorresponds,
     hSourceFrame,
     hAfter⟩

  exact
    ⟨sourceAfter,
     DTR.GlobalMultiStorePayloadOneStep.Step.externalSendFrame
       hSourceFrame,
     hAfter⟩

/--
Forward correspondence for the complete E4C one-step sum.

The dispatch branch reuses the existing global dispatch theorem. The
external-send branch requires explicit evidence for the concrete frame step.
-/
theorem oneStep_forward
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
      GlobalMultiStorePayloadRuntimeStateCorresponds
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
          ForwardExternalSendFrameCompatible
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
        GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter := by

  cases hSourceStep with

  | externalSendFrame hSourceFrame =>
      exact
        externalSendFrame_forward
          (hFrameCompatible hSourceFrame)

  | dispatch hSourceDispatch =>
      obtain
        ⟨_selectedAction,
         targetAfter,
         hTargetDispatch,
         _hSelected,
         hAfter⟩ :=
        _root_.Relico.Correctness.GlobalMultiStorePayloadDispatch.synchronizedGlobalDispatch_forward
          hSourceDispatch
          hGlobal

      exact
        ⟨targetAfter,
         LF.GlobalMultiStorePayloadOneStep.Step.dispatch
           hTargetDispatch,
         hAfter⟩

/--
Backward correspondence for the complete E4C one-step sum.

The dispatch branch reuses the existing backward global dispatch theorem.
The external-send branch requires an explicitly reflected source frame step.
-/
theorem oneStep_backward
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
      GlobalMultiStorePayloadRuntimeStateCorresponds
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
          BackwardExternalSendFrameCompatible
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
        GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter
          targetAfter := by

  cases hTargetStep with

  | externalSendFrame hTargetFrame =>
      exact
        externalSendFrame_backward
          (hFrameCompatible hTargetFrame)

  | dispatch hTargetDispatch =>
      obtain
        ⟨_selectedMessage,
         _selectedServer,
         sourceAfter,
         _hReaction,
         hSourceDispatch,
         _hSelected,
         hAfter⟩ :=
        _root_.Relico.Correctness.GlobalMultiStorePayloadDispatch.synchronizedGlobalDispatch_backward
          hTargetDispatch
          hGlobal

      exact
        ⟨sourceAfter,
         DTR.GlobalMultiStorePayloadOneStep.Step.dispatch
           hSourceDispatch,
         hAfter⟩

end GlobalMultiStorePayloadOneStepCorrespondence
end Correctness
end Relico
