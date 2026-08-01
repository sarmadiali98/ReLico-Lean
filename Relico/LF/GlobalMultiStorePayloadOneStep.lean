import Relico.LF.GlobalMultiStorePayloadExternalSendFrame
import Relico.LF.GlobalMultiStorePayloadDispatch

set_option autoImplicit false

namespace Relico
namespace LF
namespace GlobalMultiStorePayloadOneStep

/--
A successful target external-send frame application.
-/
inductive ExternalSendFrameStep :
    GlobalMultiStorePayloadState →
    GlobalMultiStorePayloadExternalSend.Occurrence →
    GlobalMultiStorePayloadExternalSendFrame.Frame →
    GlobalMultiStorePayloadState →
    Prop where

  | applied
      {before after :
        GlobalMultiStorePayloadState}
      {occurrence :
        GlobalMultiStorePayloadExternalSend.Occurrence}
      {frame :
        GlobalMultiStorePayloadExternalSendFrame.Frame}
      (hApply :
        GlobalMultiStorePayloadExternalSendFrame.apply?
            before
            occurrence
            frame =
          some after) :

      ExternalSendFrameStep
        before
        occurrence
        frame
        after

theorem ExternalSendFrameStep.apply_eq
    {before after :
      GlobalMultiStorePayloadState}
    {occurrence :
      GlobalMultiStorePayloadExternalSend.Occurrence}
    {frame :
      GlobalMultiStorePayloadExternalSendFrame.Frame}
    (hStep :
      ExternalSendFrameStep
        before
        occurrence
        frame
        after) :
    GlobalMultiStorePayloadExternalSendFrame.apply?
        before
        occurrence
        frame =
      some after := by

  cases hStep with
  | applied hApply =>
      exact hApply

/--
One target global step.

This is the disjoint union of successful external-send frame execution and
explicit actor-indexed dispatch. It does not choose an actor autonomously and
does not define a separate time-advance transition.
-/
inductive Step
    (program :
      GlobalMultiStorePayloadProgram) :
    GlobalMultiStorePayloadState →
    GlobalMultiStorePayloadState →
    Prop where

  | externalSendFrame
      {before after :
        GlobalMultiStorePayloadState}
      {occurrence :
        GlobalMultiStorePayloadExternalSend.Occurrence}
      {frame :
        GlobalMultiStorePayloadExternalSendFrame.Frame}
      (hFrame :
        ExternalSendFrameStep
          before
          occurrence
          frame
          after) :

      Step
        program
        before
        after

  | dispatch
      {actorName :
        ActorName}
      {before after :
        GlobalMultiStorePayloadState}
      {selectedAction :
        PendingAction}
      {selectedReaction :
        MultiStorePayloadReaction}
      (hDispatch :
        GlobalMultiStorePayloadDispatch.Step
          program
          actorName
          before
          selectedAction
          selectedReaction
          after) :

      Step
        program
        before
        after

theorem Step.iff_externalSendFrame_or_dispatch
    {program :
      GlobalMultiStorePayloadProgram}
    {before after :
      GlobalMultiStorePayloadState} :
    Step
        program
        before
        after ↔
      (∃ occurrence frame,
        ExternalSendFrameStep
          before
          occurrence
          frame
          after) ∨
      (∃ actorName selectedAction selectedReaction,
        GlobalMultiStorePayloadDispatch.Step
          program
          actorName
          before
          selectedAction
          selectedReaction
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
        ⟨occurrence, frame, hFrame⟩

      exact
        Step.externalSendFrame
          hFrame

    · rcases hDispatch with
        ⟨actorName,
          selectedAction,
          selectedReaction,
          hDispatch⟩

      exact
        Step.dispatch
          hDispatch

end GlobalMultiStorePayloadOneStep
end LF
end Relico
