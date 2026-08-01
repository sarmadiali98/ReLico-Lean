import Relico.DTR.GlobalMultiStorePayloadExternalSendFrame
import Relico.DTR.GlobalMultiStorePayloadDispatch

set_option autoImplicit false

namespace Relico
namespace DTR
namespace GlobalMultiStorePayloadOneStep

/--
A successful source external-send frame evaluation.

The successful result remains explicit. Its `state` field is the resulting
global source state.
-/
inductive ExternalSendFrameStep
    (model :
      GlobalMultiStorePayloadModel)
    (history :
      List GlobalMultiStorePayloadExternalSend.Key) :
    GlobalMultiStorePayloadState →
    GlobalMultiStorePayloadExternalSendFrame.Frame →
    GlobalMultiStorePayloadExternalSendFrame.Success →
    GlobalMultiStorePayloadState →
    Prop where

  | success
      {before :
        GlobalMultiStorePayloadState}
      {frame :
        GlobalMultiStorePayloadExternalSendFrame.Frame}
      {result :
        GlobalMultiStorePayloadExternalSendFrame.Success}
      (hAttempt :
        GlobalMultiStorePayloadExternalSendFrame.attempt
            model
            before
            history
            frame =
          Except.ok result) :

      ExternalSendFrameStep
        model
        history
        before
        frame
        result
        result.state

theorem ExternalSendFrameStep.attempt_eq
    {model :
      GlobalMultiStorePayloadModel}
    {history :
      List GlobalMultiStorePayloadExternalSend.Key}
    {before after :
      GlobalMultiStorePayloadState}
    {frame :
      GlobalMultiStorePayloadExternalSendFrame.Frame}
    {result :
      GlobalMultiStorePayloadExternalSendFrame.Success}
    (hStep :
      ExternalSendFrameStep
        model
        history
        before
        frame
        result
        after) :
    GlobalMultiStorePayloadExternalSendFrame.attempt
        model
        before
        history
        frame =
      Except.ok result := by

  cases hStep with
  | success hAttempt =>
      exact hAttempt

theorem ExternalSendFrameStep.after_eq
    {model :
      GlobalMultiStorePayloadModel}
    {history :
      List GlobalMultiStorePayloadExternalSend.Key}
    {before after :
      GlobalMultiStorePayloadState}
    {frame :
      GlobalMultiStorePayloadExternalSendFrame.Frame}
    {result :
      GlobalMultiStorePayloadExternalSendFrame.Success}
    (hStep :
      ExternalSendFrameStep
        model
        history
        before
        frame
        result
        after) :
    after =
      result.state := by

  cases hStep
  rfl

/--
One source global step.

This is the disjoint union of successful external-send frame execution and
explicit actor-indexed dispatch. It does not choose an actor autonomously and
does not define a separate time-advance transition.
-/
inductive Step
    (model :
      GlobalMultiStorePayloadModel)
    (history :
      List GlobalMultiStorePayloadExternalSend.Key) :
    GlobalMultiStorePayloadState →
    GlobalMultiStorePayloadState →
    Prop where

  | externalSendFrame
      {before after :
        GlobalMultiStorePayloadState}
      {frame :
        GlobalMultiStorePayloadExternalSendFrame.Frame}
      {result :
        GlobalMultiStorePayloadExternalSendFrame.Success}
      (hFrame :
        ExternalSendFrameStep
          model
          history
          before
          frame
          result
          after) :

      Step
        model
        history
        before
        after

  | dispatch
      {actorName :
        ActorName}
      {before after :
        GlobalMultiStorePayloadState}
      {selectedMessage :
        PendingMessage}
      {selectedServer :
        MultiStorePayloadMessageServer}
      (hDispatch :
        GlobalMultiStorePayloadDispatch.Step
          model
          actorName
          before
          selectedMessage
          selectedServer
          after) :

      Step
        model
        history
        before
        after

theorem Step.iff_externalSendFrame_or_dispatch
    {model :
      GlobalMultiStorePayloadModel}
    {history :
      List GlobalMultiStorePayloadExternalSend.Key}
    {before after :
      GlobalMultiStorePayloadState} :
    Step
        model
        history
        before
        after ↔
      (∃ frame result,
        ExternalSendFrameStep
          model
          history
          before
          frame
          result
          after) ∨
      (∃ actorName selectedMessage selectedServer,
        GlobalMultiStorePayloadDispatch.Step
          model
          actorName
          before
          selectedMessage
          selectedServer
          after) := by

  constructor

  · intro hStep

    cases hStep with
    | externalSendFrame hFrame =>
        exact
          Or.inl
            ⟨_, _, hFrame⟩

    | dispatch hDispatch =>
        exact
          Or.inr
            ⟨_, _, _, hDispatch⟩

  · intro hCases

    rcases hCases with
      hFrame |
      hDispatch

    · rcases hFrame with
        ⟨frame, result, hFrame⟩

      exact
        Step.externalSendFrame
          hFrame

    · rcases hDispatch with
        ⟨actorName,
          selectedMessage,
          selectedServer,
          hDispatch⟩

      exact
        Step.dispatch
          hDispatch

end GlobalMultiStorePayloadOneStep
end DTR
end Relico
