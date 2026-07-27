import Relico.Correctness.BoundPayloadStep
import Relico.Correctness.DetailedBoundPayloadStateCorrespondence
import Relico.DTR.DetailedBoundPayloadWeakSemantics
import Relico.LF.DetailedBoundPayloadWeakSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between detailed parameter-aware source and generated-LF
labels.

Generated-LF microstep administration corresponds to source stuttering and is
therefore related to source `tau`.
-/
inductive DetailedBoundPayloadLabelCorresponds :
    DTR.DetailedBoundPayloadLabel →
    LF.DetailedBoundPayloadLabel →
    Prop where

  | tau :
      DetailedBoundPayloadLabelCorresponds
        .tau
        .tau

  | microstep
      (before after : LF.Tag) :
      DetailedBoundPayloadLabelCorresponds
        .tau
        (.microstepAdvance before after)

  | timeAdvance
      {sourceBefore sourceAfter :
        LogicalTime}
      {targetBefore targetAfter :
        LogicalTime}
      (beforeTime :
        targetBefore =
          sourceBefore)
      (afterTime :
        targetAfter =
          sourceAfter) :
      DetailedBoundPayloadLabelCorresponds
        (.timeAdvance
          sourceBefore
          sourceAfter)
        (.timeAdvance
          targetBefore
          targetAfter)

  | consume
      {selectedMessage :
        DTR.PendingMessage}
      {selectedAction :
        LF.PendingAction}
      (occurrence :
        PendingPayloadCorresponds
          selectedMessage
          selectedAction) :
      DetailedBoundPayloadLabelCorresponds
        (.consume selectedMessage)
        (.consume selectedAction)

namespace DetailedBoundPayloadLabelCorresponds

/--
Corresponding labels agree on whether they are internal.
-/
theorem internal_iff
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {targetLabel :
      LF.DetailedBoundPayloadLabel}
    (hLabels :
      DetailedBoundPayloadLabelCorresponds
        sourceLabel
        targetLabel) :
    DTR.DetailedBoundPayloadLabel.isTau
          sourceLabel ↔
      LF.DetailedBoundPayloadLabel.isTau
        targetLabel := by

  cases hLabels <;>
    simp [
      DTR.DetailedBoundPayloadLabel.isTau,
      LF.DetailedBoundPayloadLabel.isTau
    ]

/--
Corresponding consumption labels retain exact payload-aware occurrence
correspondence.
-/
theorem consume_occurrence
    {selectedMessage :
      DTR.PendingMessage}
    {selectedAction :
      LF.PendingAction}
    (hLabels :
      DetailedBoundPayloadLabelCorresponds
        (.consume selectedMessage)
        (.consume selectedAction)) :
    PendingPayloadCorresponds
      selectedMessage
      selectedAction := by

  cases hLabels with
  | consume occurrence =>
      exact occurrence

end DetailedBoundPayloadLabelCorresponds


end Correctness
end Relico
