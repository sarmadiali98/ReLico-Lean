import Relico.DTR.GlobalMultiStorePayloadFiniteExecution
import Relico.LF.GlobalMultiStorePayloadFiniteExecution
import Relico.Correctness.GlobalMultiStorePayloadOneStepCorrespondence

set_option autoImplicit false

namespace Relico

namespace Correctness
namespace GlobalMultiStorePayloadFiniteExecutionCorrespondence

/--
Forward compatibility evidence indexed by one concrete finite source
derivation.

The head field supplies exactly the frame evidence needed by E4D. The tail
field supplies compatibility for every target middle state that corresponds
to the concrete source middle configuration.
-/
inductive ForwardStepsCompatible
    (sourceModel :
      DTR.GlobalMultiStorePayloadModel)
    (targetProgram :
      LF.GlobalMultiStorePayloadProgram) :
    {sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadFiniteExecution.Configuration} →
    DTR.GlobalMultiStorePayloadFiniteExecution.Steps
      sourceModel
      sourceBefore
      sourceAfter →
    LF.GlobalMultiStorePayloadState →
    Type where

  | refl
      {sourceConfiguration :
        DTR.GlobalMultiStorePayloadFiniteExecution.Configuration}
      {targetState :
        LF.GlobalMultiStorePayloadState} :
      ForwardStepsCompatible
        sourceModel
        targetProgram
        (DTR.GlobalMultiStorePayloadFiniteExecution.Steps.refl
          sourceConfiguration)
        targetState

  | cons
      {sourceBefore sourceMiddle sourceAfter :
        DTR.GlobalMultiStorePayloadFiniteExecution.Configuration}
      {targetBefore :
        LF.GlobalMultiStorePayloadState}
      (sourceHead :
        DTR.GlobalMultiStorePayloadFiniteExecution.Step
          sourceModel
          sourceBefore
          sourceMiddle)
      (sourceTail :
        DTR.GlobalMultiStorePayloadFiniteExecution.Steps
          sourceModel
          sourceMiddle
          sourceAfter)
      (headCompatible :
        GlobalMultiStorePayloadRuntimeStateCorresponds
            sourceModel
            targetProgram
            sourceBefore.state
            targetBefore →
          ∀
            {sourceFrame :
              DTR.GlobalMultiStorePayloadExternalSendFrame.Frame}
            {result :
              DTR.GlobalMultiStorePayloadExternalSendFrame.Success},
            DTR.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep
                sourceModel
                sourceBefore.history
                sourceBefore.state
                sourceFrame
                result
                sourceMiddle.state →
              GlobalMultiStorePayloadOneStepCorrespondence.ForwardExternalSendFrameCompatible
                sourceModel
                targetProgram
                sourceBefore.history
                sourceBefore.state
                sourceMiddle.state
                targetBefore
                sourceFrame)
      (tailCompatible :
        ∀
          {targetMiddle :
            LF.GlobalMultiStorePayloadState},
          GlobalMultiStorePayloadRuntimeStateCorresponds
              sourceModel
              targetProgram
              sourceMiddle.state
              targetMiddle →
            ForwardStepsCompatible
              sourceModel
              targetProgram
              sourceTail
              targetMiddle) :
      ForwardStepsCompatible
        sourceModel
        targetProgram
        (DTR.GlobalMultiStorePayloadFiniteExecution.Steps.cons
          sourceHead
          sourceTail)
        targetBefore

/--
Backward compatibility evidence indexed by one concrete finite target
derivation.

The tail evidence is indexed by the source configuration reconstructed from
the concrete target head step.
-/
inductive BackwardStepsCompatible
    (sourceModel :
      DTR.GlobalMultiStorePayloadModel)
    (targetProgram :
      LF.GlobalMultiStorePayloadProgram) :
    {targetBefore targetAfter :
      LF.GlobalMultiStorePayloadState} →
    LF.GlobalMultiStorePayloadFiniteExecution.Steps
      targetProgram
      targetBefore
      targetAfter →
    DTR.GlobalMultiStorePayloadFiniteExecution.Configuration →
    Type where

  | refl
      {targetState :
        LF.GlobalMultiStorePayloadState}
      {sourceConfiguration :
        DTR.GlobalMultiStorePayloadFiniteExecution.Configuration} :
      BackwardStepsCompatible
        sourceModel
        targetProgram
        (LF.GlobalMultiStorePayloadFiniteExecution.Steps.refl
          targetState)
        sourceConfiguration

  | cons
      {targetBefore targetMiddle targetAfter :
        LF.GlobalMultiStorePayloadState}
      {sourceBefore :
        DTR.GlobalMultiStorePayloadFiniteExecution.Configuration}
      (targetHead :
        LF.GlobalMultiStorePayloadOneStep.Step
          targetProgram
          targetBefore
          targetMiddle)
      (targetTail :
        LF.GlobalMultiStorePayloadFiniteExecution.Steps
          targetProgram
          targetMiddle
          targetAfter)
      (headCompatible :
        GlobalMultiStorePayloadRuntimeStateCorresponds
            sourceModel
            targetProgram
            sourceBefore.state
            targetBefore →
          ∀
            {targetOccurrence :
              LF.GlobalMultiStorePayloadExternalSend.Occurrence}
            {targetFrame :
              LF.GlobalMultiStorePayloadExternalSendFrame.Frame},
            LF.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep
                targetBefore
                targetOccurrence
                targetFrame
                targetMiddle →
              GlobalMultiStorePayloadOneStepCorrespondence.BackwardExternalSendFrameCompatible
                sourceModel
                targetProgram
                sourceBefore.history
                sourceBefore.state
                targetMiddle
                targetFrame)
      (tailCompatible :
        ∀
          {sourceMiddle :
            DTR.GlobalMultiStorePayloadFiniteExecution.Configuration},
          DTR.GlobalMultiStorePayloadFiniteExecution.Step
              sourceModel
              sourceBefore
              sourceMiddle →
            GlobalMultiStorePayloadRuntimeStateCorresponds
                sourceModel
                targetProgram
                sourceMiddle.state
                targetMiddle →
              BackwardStepsCompatible
                sourceModel
                targetProgram
                targetTail
                sourceMiddle) :
      BackwardStepsCompatible
        sourceModel
        targetProgram
        (LF.GlobalMultiStorePayloadFiniteExecution.Steps.cons
          targetHead
          targetTail)
        sourceBefore

/--
Finite forward correspondence for evolving-history source configurations.

The proof recurses on the compatibility evidence itself. This keeps the
concrete source head, source middle configuration, finite tail, and recursive
compatibility evidence definitionally aligned.
-/
theorem finite_forward
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadFiniteExecution.Configuration}
    {targetBefore :
      LF.GlobalMultiStorePayloadState}
    (hSourceSteps :
      DTR.GlobalMultiStorePayloadFiniteExecution.Steps
        sourceModel
        sourceBefore
        sourceAfter)
    (hCompatible :
      ForwardStepsCompatible
        sourceModel
        targetProgram
        hSourceSteps
        targetBefore)
    (hGlobal :
      GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore.state
        targetBefore) :
    ∃ targetAfter,
      LF.GlobalMultiStorePayloadFiniteExecution.Steps
          targetProgram
          targetBefore
          targetAfter ∧
        GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter.state
          targetAfter := by

  exact
    ForwardStepsCompatible.rec
      (motive := fun
          {sourceBefore sourceAfter}
          _sourceSteps
          {targetBefore}
          _compatible =>
        GlobalMultiStorePayloadRuntimeStateCorresponds
            sourceModel
            targetProgram
            sourceBefore.state
            targetBefore →
          ∃ targetAfter,
            LF.GlobalMultiStorePayloadFiniteExecution.Steps
                targetProgram
                targetBefore
                targetAfter ∧
              GlobalMultiStorePayloadRuntimeStateCorresponds
                sourceModel
                targetProgram
                sourceAfter.state
                targetAfter)

      (fun
          {sourceConfiguration}
          {targetState}
          hCurrentGlobal =>
        ⟨
          targetState,
          LF.GlobalMultiStorePayloadFiniteExecution.Steps.refl
            targetState,
          hCurrentGlobal
        ⟩)

      (fun
          {sourceBefore}
          {sourceMiddle}
          {sourceAfter}
          {targetBefore}
          sourceHead
          _sourceTail
          hHeadCompatible
          _hTailCompatible
          inductionHypothesis
          hCurrentGlobal => by

        obtain
          ⟨targetMiddle,
           hTargetHead,
           hMiddleGlobal⟩ :=
          _root_.Relico.Correctness.GlobalMultiStorePayloadOneStepCorrespondence.oneStep_forward
            (DTR.GlobalMultiStorePayloadFiniteExecution.Step.toOneStep
              sourceHead)
            hCurrentGlobal
            (hHeadCompatible
              hCurrentGlobal)

        obtain
          ⟨targetAfter,
           hTargetTail,
           hAfterGlobal⟩ :=
          inductionHypothesis
            hMiddleGlobal
            hMiddleGlobal

        exact
          ⟨
            targetAfter,
            LF.GlobalMultiStorePayloadFiniteExecution.Steps.cons
              hTargetHead
              hTargetTail,
            hAfterGlobal
          ⟩)

      hCompatible
      hGlobal

/--
Finite backward correspondence for evolving-history source configurations.

The proof recurses on the backward compatibility evidence itself. The
recursive hypothesis is therefore indexed by the exact target tail and by
the source configuration reconstructed from the concrete target head.
-/
theorem finite_backward
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {sourceBefore :
      DTR.GlobalMultiStorePayloadFiniteExecution.Configuration}
    {targetBefore targetAfter :
      LF.GlobalMultiStorePayloadState}
    (hTargetSteps :
      LF.GlobalMultiStorePayloadFiniteExecution.Steps
        targetProgram
        targetBefore
        targetAfter)
    (hCompatible :
      BackwardStepsCompatible
        sourceModel
        targetProgram
        hTargetSteps
        sourceBefore)
    (hGlobal :
      GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore.state
        targetBefore) :
    ∃ sourceAfter,
      DTR.GlobalMultiStorePayloadFiniteExecution.Steps
          sourceModel
          sourceBefore
          sourceAfter ∧
        GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter.state
          targetAfter := by

  exact
    BackwardStepsCompatible.rec
      (motive := fun
          {targetBefore targetAfter}
          _targetSteps
          {sourceBefore}
          _compatible =>
        GlobalMultiStorePayloadRuntimeStateCorresponds
            sourceModel
            targetProgram
            sourceBefore.state
            targetBefore →
          ∃ sourceAfter,
            DTR.GlobalMultiStorePayloadFiniteExecution.Steps
                sourceModel
                sourceBefore
                sourceAfter ∧
              GlobalMultiStorePayloadRuntimeStateCorresponds
                sourceModel
                targetProgram
                sourceAfter.state
                targetAfter)

      (fun
          {targetState}
          {sourceConfiguration}
          hCurrentGlobal =>
        ⟨
          sourceConfiguration,
          DTR.GlobalMultiStorePayloadFiniteExecution.Steps.refl
            sourceConfiguration,
          hCurrentGlobal
        ⟩)

      (fun
          {targetBefore}
          {targetMiddle}
          {targetAfter}
          {sourceBefore}
          targetHead
          _targetTail
          hHeadCompatible
          _hTailCompatible
          inductionHypothesis
          hCurrentGlobal => by

        obtain
          ⟨sourceMiddleState,
           hSourceHeadRaw,
           hMiddleGlobal⟩ :=
          _root_.Relico.Correctness.GlobalMultiStorePayloadOneStepCorrespondence.oneStep_backward
            targetHead
            hCurrentGlobal
            (hHeadCompatible
              hCurrentGlobal)

        obtain
          ⟨sourceMiddle,
           hSourceHead,
           hSourceMiddleState⟩ :=
          DTR.GlobalMultiStorePayloadFiniteExecution.Step.exists_of_oneStep
            hSourceHeadRaw

        rw [← hSourceMiddleState] at hMiddleGlobal

        obtain
          ⟨sourceAfter,
           hSourceTail,
           hAfterGlobal⟩ :=
          inductionHypothesis
            hSourceHead
            hMiddleGlobal
            hMiddleGlobal

        exact
          ⟨
            sourceAfter,
            DTR.GlobalMultiStorePayloadFiniteExecution.Steps.cons
              hSourceHead
              hSourceTail,
            hAfterGlobal
          ⟩)

      hCompatible
      hGlobal

end GlobalMultiStorePayloadFiniteExecutionCorrespondence
end Correctness

end Relico
