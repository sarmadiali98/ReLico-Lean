import Relico.LF.DetailedBoundPayloadSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
Internal closure for the detailed parameter-aware generated-LF semantics.
-/
abbrev DetailedBoundPayloadTauSteps
    (reaction : LF.PayloadReaction)
    (source target :
      LF.DetailedBoundPayloadState reaction) :
    Prop :=
  Common.TauSteps
    (LF.DetailedBoundPayloadStep reaction)
    LF.DetailedBoundPayloadLabel.isTau
    source
    target

/--
Weak labeled transition for the detailed parameter-aware generated-LF
semantics.
-/
abbrev DetailedBoundPayloadWeakStep
    (reaction : LF.PayloadReaction)
    (source :
      LF.DetailedBoundPayloadState reaction)
    (label :
      LF.DetailedBoundPayloadLabel)
    (target :
      LF.DetailedBoundPayloadState reaction) :
    Prop :=
  Common.WeakStep
    (LF.DetailedBoundPayloadStep reaction)
    LF.DetailedBoundPayloadLabel.isTau
    source
    label
    target

@[simp]
theorem detailedBoundPayload_tau_internal :
    LF.DetailedBoundPayloadLabel.isTau
      LF.DetailedBoundPayloadLabel.tau := by

  exact True.intro

theorem detailedBoundPayload_microstep_internal
    (before after : LF.Tag) :
    LF.DetailedBoundPayloadLabel.isTau
      (.microstepAdvance before after) := by

  exact True.intro

theorem detailedBoundPayload_timeAdvance_visible
    (before after : LogicalTime) :
    ¬ LF.DetailedBoundPayloadLabel.isTau
        (.timeAdvance before after) := by

  simp [
    LF.DetailedBoundPayloadLabel.isTau
  ]

theorem detailedBoundPayload_consume_visible
    (selectedAction : LF.PendingAction) :
    ¬ LF.DetailedBoundPayloadLabel.isTau
        (.consume selectedAction) := by

  simp [
    LF.DetailedBoundPayloadLabel.isTau
  ]

theorem detailedBoundPayloadWeakStep_of_step
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
    Common.WeakStep.of_step
      (isTau :=
        LF.DetailedBoundPayloadLabel.isTau)
      hStep

theorem detailedBoundPayloadTauSteps_single
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
        target)
    (hTau :
      LF.DetailedBoundPayloadLabel.isTau
        label) :
    LF.DetailedBoundPayloadTauSteps
      reaction
      source
      target := by

  exact
    Common.TauSteps.single
      hStep
      hTau

theorem detailedBoundPayloadTauSteps_trans
    {reaction : LF.PayloadReaction}
    {source middle target :
      LF.DetailedBoundPayloadState reaction}
    (left :
      LF.DetailedBoundPayloadTauSteps
        reaction
        source
        middle)
    (right :
      LF.DetailedBoundPayloadTauSteps
        reaction
        middle
        target) :
    LF.DetailedBoundPayloadTauSteps
      reaction
      source
      target := by

  exact
    Common.TauSteps.trans
      left
      right

theorem detailedBoundPayloadTauSteps_to_weakTau
    {reaction : LF.PayloadReaction}
    {source target :
      LF.DetailedBoundPayloadState reaction}
    (hSteps :
      LF.DetailedBoundPayloadTauSteps
        reaction
        source
        target) :
    LF.DetailedBoundPayloadWeakStep
      reaction
      source
      .tau
      target := by

  exact
    Common.WeakStep.of_tauSteps
      (label :=
        LF.DetailedBoundPayloadLabel.tau)
      LF.detailedBoundPayload_tau_internal
      hSteps

theorem detailedBoundPayloadWeakTau_refl
    {reaction : LF.PayloadReaction}
    (state :
      LF.DetailedBoundPayloadState reaction) :
    LF.DetailedBoundPayloadWeakStep
      reaction
      state
      .tau
      state := by

  exact
    Common.WeakStep.tau_refl
      (step :=
        LF.DetailedBoundPayloadStep
          reaction)
      (isTau :=
        LF.DetailedBoundPayloadLabel.isTau)
      LF.detailedBoundPayload_tau_internal

theorem detailedBoundPayloadStatement_is_weak
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {label : LF.BoundPayloadLabel}
    (hStatement :
      LF.BoundPayloadStep
        reaction.logicalAction
        before
        label
        after) :
    LF.DetailedBoundPayloadWeakStep
      reaction
      (.stable before)
      .tau
      (.stable after) := by

  exact
    LF.detailedBoundPayloadWeakStep_of_step
      (LF.DetailedBoundPayloadStep.statement
        hStatement)

theorem detailedBoundPayloadMicrostep_to_tauSteps
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
    LF.DetailedBoundPayloadTauSteps
      reaction
      source
      target := by

  exact
    LF.detailedBoundPayloadTauSteps_single
      hStep
      (LF.detailedBoundPayload_microstep_internal
        before
        after)

theorem detailedBoundPayloadMicrostep_is_weakTau
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
    LF.detailedBoundPayloadTauSteps_to_weakTau
      (LF.detailedBoundPayloadMicrostep_to_tauSteps
        hStep)

theorem detailedBoundPayloadTimeAdvance_is_weak
    {reaction : LF.PayloadReaction}
    {source target :
      LF.DetailedBoundPayloadState reaction}
    {before after : LogicalTime}
    (hStep :
      LF.DetailedBoundPayloadStep
        reaction
        source
        (.timeAdvance before after)
        target) :
    LF.DetailedBoundPayloadWeakStep
      reaction
      source
      (.timeAdvance before after)
      target := by

  exact
    Common.WeakStep.visible
      (LF.detailedBoundPayload_timeAdvance_visible
        before
        after)
      (Common.TauSteps.refl source)
      hStep
      (Common.TauSteps.refl target)

theorem detailedBoundPayloadConsume_is_weak
    {reaction : LF.PayloadReaction}
    {source target :
      LF.DetailedBoundPayloadState reaction}
    {selectedAction : LF.PendingAction}
    (hStep :
      LF.DetailedBoundPayloadStep
        reaction
        source
        (.consume selectedAction)
        target) :
    LF.DetailedBoundPayloadWeakStep
      reaction
      source
      (.consume selectedAction)
      target := by

  exact
    Common.WeakStep.visible
      (LF.detailedBoundPayload_consume_visible
        selectedAction)
      (Common.TauSteps.refl source)
      hStep
      (Common.TauSteps.refl target)


end LF
end Relico
