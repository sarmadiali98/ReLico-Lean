import Relico.Correctness.DetailedBoundPayloadWeakFoundation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedBoundPayloadWeakFoundation

theorem source_exact_step_is_weak_interface
    {server : DTR.PayloadMessageServer}
    {source target :
      DTR.DetailedBoundPayloadState server}
    {label :
      DTR.DetailedBoundPayloadLabel}
    (hStep :
      DTR.DetailedBoundPayloadStep
        server
        source
        label
        target) :
    DTR.DetailedBoundPayloadWeakStep
      server
      source
      label
      target := by

  exact
    DTR.detailedBoundPayloadWeakStep_of_step
      hStep

theorem target_exact_step_is_weak_interface
    {reaction : LF.PayloadReaction}
    {source target :
      LF.DetailedBoundPayloadState reaction}
    {label :
      LF.DetailedBoundPayloadLabel}
    (hStep :
      LF.DetailedBoundPayloadStep
        reaction
        source
        label
        target) :
    LF.DetailedBoundPayloadWeakStep
      reaction
      source
      label
      target := by

  exact
    LF.detailedBoundPayloadWeakStep_of_step
      hStep

theorem source_weak_tau_reflexive_interface
    {server : DTR.PayloadMessageServer}
    (state :
      DTR.DetailedBoundPayloadState server) :
    DTR.DetailedBoundPayloadWeakStep
      server
      state
      .tau
      state := by

  exact
    DTR.detailedBoundPayloadWeakTau_refl
      state

theorem target_weak_tau_reflexive_interface
    {reaction : LF.PayloadReaction}
    (state :
      LF.DetailedBoundPayloadState reaction) :
    LF.DetailedBoundPayloadWeakStep
      reaction
      state
      .tau
      state := by

  exact
    LF.detailedBoundPayloadWeakTau_refl
      state

theorem target_microstep_is_weak_tau_interface
    {reaction : LF.PayloadReaction}
    {source target :
      LF.DetailedBoundPayloadState reaction}
    {before after : LF.Tag}
    (hStep :
      LF.DetailedBoundPayloadStep
        reaction
        source
        (.microstepAdvance before after)
        target) :
    LF.DetailedBoundPayloadWeakStep
      reaction
      source
      .tau
      target := by

  exact
    LF.detailedBoundPayloadMicrostep_is_weakTau
      hStep

theorem tau_label_correspondence_interface :
    Correctness.DetailedBoundPayloadLabelCorresponds
      DTR.DetailedBoundPayloadLabel.tau
      LF.DetailedBoundPayloadLabel.tau := by

  exact
    Correctness.DetailedBoundPayloadLabelCorresponds.tau

theorem microstep_label_correspondence_interface
    (before after : LF.Tag) :
    Correctness.DetailedBoundPayloadLabelCorresponds
      DTR.DetailedBoundPayloadLabel.tau
      (LF.DetailedBoundPayloadLabel.microstepAdvance
        before
        after) := by

  exact
    Correctness.DetailedBoundPayloadLabelCorresponds.microstep
      before
      after

theorem time_label_correspondence_interface
    (before after : LogicalTime) :
    Correctness.DetailedBoundPayloadLabelCorresponds
      (DTR.DetailedBoundPayloadLabel.timeAdvance
        before
        after)
      (LF.DetailedBoundPayloadLabel.timeAdvance
        before
        after) := by

  exact
    Correctness.DetailedBoundPayloadLabelCorresponds.timeAdvance
      rfl
      rfl

theorem consume_label_correspondence_interface
    {selectedMessage : DTR.PendingMessage}
    {selectedAction : LF.PendingAction}
    (hOccurrence :
      Correctness.PendingPayloadCorresponds
        selectedMessage
        selectedAction) :
    Correctness.DetailedBoundPayloadLabelCorresponds
      (.consume selectedMessage)
      (.consume selectedAction) := by

  exact
    Correctness.DetailedBoundPayloadLabelCorresponds.consume
      hOccurrence

theorem corresponding_labels_internal_iff_interface
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {targetLabel :
      LF.DetailedBoundPayloadLabel}
    (hLabels :
      Correctness.DetailedBoundPayloadLabelCorresponds
        sourceLabel
        targetLabel) :
    DTR.DetailedBoundPayloadLabel.isTau
          sourceLabel ↔
      LF.DetailedBoundPayloadLabel.isTau
        targetLabel := by

  exact
    Correctness.DetailedBoundPayloadLabelCorresponds.internal_iff
      hLabels

theorem consume_correspondence_retains_payload_interface
    {selectedMessage : DTR.PendingMessage}
    {selectedAction : LF.PendingAction}
    (hLabels :
      Correctness.DetailedBoundPayloadLabelCorresponds
        (.consume selectedMessage)
        (.consume selectedAction)) :
    Correctness.PendingPayloadCorresponds
      selectedMessage
      selectedAction := by

  exact
    Correctness.DetailedBoundPayloadLabelCorresponds.consume_occurrence
      hLabels

end DetailedBoundPayloadWeakFoundation
end Tests
end Relico
