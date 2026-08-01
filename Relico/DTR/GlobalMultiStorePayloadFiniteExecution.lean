import Relico.DTR.GlobalMultiStorePayloadOneStep

set_option autoImplicit false

namespace Relico

namespace DTR
namespace GlobalMultiStorePayloadFiniteExecution

/--
A source finite-execution endpoint carries the global runtime state and the
evolving duplicate-detection history.
-/
structure Configuration where
  state :
    DTR.GlobalMultiStorePayloadState

  history :
    List DTR.GlobalMultiStorePayloadExternalSend.Key

/--
One source configuration step.

External-send execution advances to the history returned by the successful
frame result. Dispatch preserves the current history.
-/
inductive Step
    (sourceModel :
      DTR.GlobalMultiStorePayloadModel) :
    Configuration →
    Configuration →
    Prop where

  | externalSendFrame
      {before :
        Configuration}
      {afterState :
        DTR.GlobalMultiStorePayloadState}
      {sourceFrame :
        DTR.GlobalMultiStorePayloadExternalSendFrame.Frame}
      {result :
        DTR.GlobalMultiStorePayloadExternalSendFrame.Success}
      (hFrame :
        DTR.GlobalMultiStorePayloadOneStep.ExternalSendFrameStep
          sourceModel
          before.history
          before.state
          sourceFrame
          result
          afterState) :
      Step
        sourceModel
        before
        {
          state :=
            afterState

          history :=
            result.foundation.history
        }

  | dispatch
      {before :
        Configuration}
      {afterState :
        DTR.GlobalMultiStorePayloadState}
      {actorName :
        ActorName}
      {selectedMessage :
        DTR.PendingMessage}
      {selectedServer :
        DTR.MultiStorePayloadMessageServer}
      (hDispatch :
        DTR.GlobalMultiStorePayloadDispatch.Step
          sourceModel
          actorName
          before.state
          selectedMessage
          selectedServer
          afterState) :
      Step
        sourceModel
        before
        {
          state :=
            afterState

          history :=
            before.history
        }

/--
A finite reflexive sequence of source configuration steps.
-/
inductive Steps
    (sourceModel :
      DTR.GlobalMultiStorePayloadModel) :
    Configuration →
    Configuration →
    Prop where

  | refl
      (configuration :
        Configuration) :
      Steps
        sourceModel
        configuration
        configuration

  | cons
      {before middle after :
        Configuration}
      (head :
        Step
          sourceModel
          before
          middle)
      (tail :
        Steps
          sourceModel
          middle
          after) :
      Steps
        sourceModel
        before
        after

namespace Step

/--
A source configuration step projects to the published E4C source one-step
relation at its current history.
-/
theorem toOneStep
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {before after :
      Configuration}
    (hSourceStep :
      Step
        sourceModel
        before
        after) :
    DTR.GlobalMultiStorePayloadOneStep.Step
      sourceModel
      before.history
      before.state
      after.state := by

  cases hSourceStep with

  | externalSendFrame hFrame =>
      exact
        DTR.GlobalMultiStorePayloadOneStep.Step.externalSendFrame
          hFrame

  | dispatch hDispatch =>
      exact
        DTR.GlobalMultiStorePayloadOneStep.Step.dispatch
          hDispatch

/--
A published E4C source one-step transition lifts to a source configuration
step with the correct next history.
-/
theorem exists_of_oneStep
    {sourceModel :
      DTR.GlobalMultiStorePayloadModel}
    {before :
      Configuration}
    {afterState :
      DTR.GlobalMultiStorePayloadState}
    (hSourceStep :
      DTR.GlobalMultiStorePayloadOneStep.Step
        sourceModel
        before.history
        before.state
        afterState) :
    ∃ after,
      Step
          sourceModel
          before
          after ∧
        after.state =
          afterState := by

  rcases
      DTR.GlobalMultiStorePayloadOneStep.Step.iff_externalSendFrame_or_dispatch.mp
        hSourceStep
    with
    hFrame | hDispatch

  · rcases hFrame with
      ⟨sourceFrame,
       result,
       hFrame⟩

    exact
      ⟨
        {
          state :=
            afterState

          history :=
            result.foundation.history
        },
        Step.externalSendFrame
          hFrame,
        rfl
      ⟩

  · rcases hDispatch with
      ⟨actorName,
       selectedMessage,
       selectedServer,
       hDispatch⟩

    exact
      ⟨
        {
          state :=
            afterState

          history :=
            before.history
        },
        Step.dispatch
          hDispatch,
        rfl
      ⟩

end Step
end GlobalMultiStorePayloadFiniteExecution
end DTR

end Relico
