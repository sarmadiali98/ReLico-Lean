/-
Copyright (c) 2026.

Payload-refined detailed-label correspondence for DirectLF.

Internal labels, LF microstep stuttering, and metric-time correspondence are
unchanged. A consumption label additionally records exact payload equality
through `PendingPayloadCorresponds`.
-/

import Relico.Correctness.DirectLFPayloadDetailedRuntimeStateCorrespondence
import Relico.Correctness.DirectLFDetailedForwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Payload-refined correspondence between one detailed DTR label and one detailed
generated-LF label.
-/
inductive DirectLFPayloadDetailedLabelCorresponds :
    DTR.DetailedMultiStoreLabel →
    LF.DetailedMultiStoreLabel →
    Prop where

  | tau :
      DirectLFPayloadDetailedLabelCorresponds
        DTR.DetailedMultiStoreLabel.tau
        LF.DetailedMultiStoreLabel.tau

  | microstep
      (before after : LF.Tag) :
      DirectLFPayloadDetailedLabelCorresponds
        DTR.DetailedMultiStoreLabel.tau
        (LF.DetailedMultiStoreLabel.microstepAdvance
          before
          after)

  | timeAdvance
      {sourceBefore sourceAfter : LogicalTime}
      {targetBefore targetAfter : LogicalTime}
      (hBeforeTime :
        targetBefore =
          sourceBefore)
      (hAfterTime :
        targetAfter =
          sourceAfter) :
      DirectLFPayloadDetailedLabelCorresponds
        (DTR.DetailedMultiStoreLabel.timeAdvance
          sourceBefore
          sourceAfter)
        (LF.DetailedMultiStoreLabel.timeAdvance
          targetBefore
          targetAfter)

  | consume
      {sourceMessage : DTR.PendingMessage}
      {sourceServer : DTR.MessageServer}
      {targetAction : LF.PendingAction}
      {targetReaction : LF.Reaction}
      (hOccurrence :
        PendingPayloadCorresponds
          sourceMessage
          targetAction)
      (hReaction :
        targetReaction =
          Translation.compileMessageReaction
            sourceServer) :
      DirectLFPayloadDetailedLabelCorresponds
        (DTR.DetailedMultiStoreLabel.consume
          sourceMessage
          sourceServer)
        (LF.DetailedMultiStoreLabel.consume
          targetAction
          targetReaction)

/--
Forgetting exact payload equality yields the existing detailed-label
correspondence.
-/
theorem DirectLFPayloadDetailedLabelCorresponds.toDetailedLabelCorresponds
    {sourceLabel : DTR.DetailedMultiStoreLabel}
    {targetLabel : LF.DetailedMultiStoreLabel}
    (hLabels :
      DirectLFPayloadDetailedLabelCorresponds
        sourceLabel
        targetLabel) :
    DirectLFDetailedLabelCorresponds
      sourceLabel
      targetLabel := by

  cases hLabels with

  | tau =>
      exact
        DirectLFDetailedLabelCorresponds.tau

  | microstep before after =>
      exact
        DirectLFDetailedLabelCorresponds.microstep
          before
          after

  | timeAdvance hBeforeTime hAfterTime =>
      exact
        DirectLFDetailedLabelCorresponds.timeAdvance
          hBeforeTime
          hAfterTime

  | consume hOccurrence hReaction =>
      exact
        DirectLFDetailedLabelCorresponds.consume
          (PendingPayloadCorresponds.toPendingCorresponds
            hOccurrence)
          hReaction

/--
Corresponding detailed consumption labels carry exactly equal payloads.
-/
theorem DirectLFPayloadDetailedLabelCorresponds.consume_payload_eq
    {sourceMessage : DTR.PendingMessage}
    {sourceServer : DTR.MessageServer}
    {targetAction : LF.PendingAction}
    {targetReaction : LF.Reaction}
    (hLabels :
      DirectLFPayloadDetailedLabelCorresponds
        (DTR.DetailedMultiStoreLabel.consume
          sourceMessage
          sourceServer)
        (LF.DetailedMultiStoreLabel.consume
          targetAction
          targetReaction)) :
    targetAction.payload =
      sourceMessage.payload := by

  cases hLabels with

  | consume hOccurrence _hReaction =>
      exact
        hOccurrence.payload

end Correctness
end Relico
