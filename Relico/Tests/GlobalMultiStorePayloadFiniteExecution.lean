import Relico.Correctness.GlobalMultiStorePayloadFiniteExecutionCorrespondence

set_option autoImplicit false

namespace Relico

namespace Tests
namespace GlobalMultiStorePayloadFiniteExecution

theorem sourceStep_toOneStep_regression
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {before after :
      DTR.GlobalMultiStorePayloadFiniteExecution.Configuration}
    (hStep :
      DTR.GlobalMultiStorePayloadFiniteExecution.Step
        sourceModel
        before
        after) :
    DTR.GlobalMultiStorePayloadOneStep.Step
      sourceModel
      before.history
      before.state
      after.state :=
  DTR.GlobalMultiStorePayloadFiniteExecution.Step.toOneStep
    hStep

theorem sourceStep_exists_of_oneStep_regression
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {before :
      DTR.GlobalMultiStorePayloadFiniteExecution.Configuration}
    {afterState :
      DTR.GlobalMultiStorePayloadState}
    (hStep :
      DTR.GlobalMultiStorePayloadOneStep.Step
        sourceModel
        before.history
        before.state
        afterState) :
    ∃ after,
      DTR.GlobalMultiStorePayloadFiniteExecution.Step
          sourceModel
          before
          after ∧
        after.state =
          afterState :=
  DTR.GlobalMultiStorePayloadFiniteExecution.Step.exists_of_oneStep
    hStep

theorem finite_forward_regression
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {sourceBefore sourceAfter :
      DTR.GlobalMultiStorePayloadFiniteExecution.Configuration}
    {targetBefore :
      LF.GlobalMultiStorePayloadState}
    (hSteps :
      DTR.GlobalMultiStorePayloadFiniteExecution.Steps
        sourceModel
        sourceBefore
        sourceAfter)
    (hCompatible :
      Correctness.GlobalMultiStorePayloadFiniteExecutionCorrespondence.ForwardStepsCompatible
        sourceModel
        targetProgram
        hSteps
        targetBefore)
    (hGlobal :
      Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore.state
        targetBefore) :
    ∃ targetAfter,
      LF.GlobalMultiStorePayloadFiniteExecution.Steps
          targetProgram
          targetBefore
          targetAfter ∧
        Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter.state
          targetAfter :=
  Correctness.GlobalMultiStorePayloadFiniteExecutionCorrespondence.finite_forward
    hSteps
    hCompatible
    hGlobal

theorem finite_backward_regression
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {targetProgram :
      LF.GlobalMultiStorePayloadProgram}
    {sourceBefore :
      DTR.GlobalMultiStorePayloadFiniteExecution.Configuration}
    {targetBefore targetAfter :
      LF.GlobalMultiStorePayloadState}
    (hSteps :
      LF.GlobalMultiStorePayloadFiniteExecution.Steps
        targetProgram
        targetBefore
        targetAfter)
    (hCompatible :
      Correctness.GlobalMultiStorePayloadFiniteExecutionCorrespondence.BackwardStepsCompatible
        sourceModel
        targetProgram
        hSteps
        sourceBefore)
    (hGlobal :
      Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
        sourceModel
        targetProgram
        sourceBefore.state
        targetBefore) :
    ∃ sourceAfter,
      DTR.GlobalMultiStorePayloadFiniteExecution.Steps
          sourceModel
          sourceBefore
          sourceAfter ∧
        Correctness.GlobalMultiStorePayloadRuntimeStateCorresponds
          sourceModel
          targetProgram
          sourceAfter.state
          targetAfter :=
  Correctness.GlobalMultiStorePayloadFiniteExecutionCorrespondence.finite_backward
    hSteps
    hCompatible
    hGlobal

end GlobalMultiStorePayloadFiniteExecution
end Tests

end Relico
