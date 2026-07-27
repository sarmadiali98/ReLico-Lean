import Relico.DTR.DetailedBoundPayloadSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Internal closure for the detailed parameter-aware source semantics.
-/
abbrev DetailedBoundPayloadTauSteps
    (server : DTR.PayloadMessageServer)
    (source target :
      DTR.DetailedBoundPayloadState server) :
    Prop :=
  Common.TauSteps
    (DTR.DetailedBoundPayloadStep server)
    DTR.DetailedBoundPayloadLabel.isTau
    source
    target

/--
Weak labeled transition for the detailed parameter-aware source semantics.
-/
abbrev DetailedBoundPayloadWeakStep
    (server : DTR.PayloadMessageServer)
    (source :
      DTR.DetailedBoundPayloadState server)
    (label :
      DTR.DetailedBoundPayloadLabel)
    (target :
      DTR.DetailedBoundPayloadState server) :
    Prop :=
  Common.WeakStep
    (DTR.DetailedBoundPayloadStep server)
    DTR.DetailedBoundPayloadLabel.isTau
    source
    label
    target

@[simp]
theorem detailedBoundPayload_tau_internal :
    DTR.DetailedBoundPayloadLabel.isTau
      DTR.DetailedBoundPayloadLabel.tau := by

  exact True.intro

theorem detailedBoundPayload_timeAdvance_visible
    (before after : LogicalTime) :
    ¬ DTR.DetailedBoundPayloadLabel.isTau
        (.timeAdvance before after) := by

  simp [
    DTR.DetailedBoundPayloadLabel.isTau
  ]

theorem detailedBoundPayload_consume_visible
    (selectedMessage : DTR.PendingMessage) :
    ¬ DTR.DetailedBoundPayloadLabel.isTau
        (.consume selectedMessage) := by

  simp [
    DTR.DetailedBoundPayloadLabel.isTau
  ]

theorem detailedBoundPayloadWeakStep_of_step
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
    Common.WeakStep.of_step
      (isTau :=
        DTR.DetailedBoundPayloadLabel.isTau)
      hStep

theorem detailedBoundPayloadTauSteps_single
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
        target)
    (hTau :
      DTR.DetailedBoundPayloadLabel.isTau
        label) :
    DTR.DetailedBoundPayloadTauSteps
      server
      source
      target := by

  exact
    Common.TauSteps.single
      hStep
      hTau

theorem detailedBoundPayloadTauSteps_trans
    {server : DTR.PayloadMessageServer}
    {source middle target :
      DTR.DetailedBoundPayloadState server}
    (left :
      DTR.DetailedBoundPayloadTauSteps
        server
        source
        middle)
    (right :
      DTR.DetailedBoundPayloadTauSteps
        server
        middle
        target) :
    DTR.DetailedBoundPayloadTauSteps
      server
      source
      target := by

  exact
    Common.TauSteps.trans
      left
      right

theorem detailedBoundPayloadTauSteps_to_weakTau
    {server : DTR.PayloadMessageServer}
    {source target :
      DTR.DetailedBoundPayloadState server}
    (hSteps :
      DTR.DetailedBoundPayloadTauSteps
        server
        source
        target) :
    DTR.DetailedBoundPayloadWeakStep
      server
      source
      .tau
      target := by

  exact
    Common.WeakStep.of_tauSteps
      (label :=
        DTR.DetailedBoundPayloadLabel.tau)
      DTR.detailedBoundPayload_tau_internal
      hSteps

theorem detailedBoundPayloadWeakTau_refl
    {server : DTR.PayloadMessageServer}
    (state :
      DTR.DetailedBoundPayloadState server) :
    DTR.DetailedBoundPayloadWeakStep
      server
      state
      .tau
      state := by

  exact
    Common.WeakStep.tau_refl
      (step :=
        DTR.DetailedBoundPayloadStep
          server)
      (isTau :=
        DTR.DetailedBoundPayloadLabel.isTau)
      DTR.detailedBoundPayload_tau_internal

theorem detailedBoundPayloadStatement_is_weak
    {server : DTR.PayloadMessageServer}
    {before after : DTR.BoundPayloadState}
    {label : DTR.BoundPayloadLabel}
    (hStatement :
      DTR.BoundPayloadStep
        server.name
        before
        label
        after) :
    DTR.DetailedBoundPayloadWeakStep
      server
      (.stable before)
      .tau
      (.stable after) := by

  exact
    DTR.detailedBoundPayloadWeakStep_of_step
      (DTR.DetailedBoundPayloadStep.statement
        hStatement)

theorem detailedBoundPayloadTimeAdvance_is_weak
    {server : DTR.PayloadMessageServer}
    {source target :
      DTR.DetailedBoundPayloadState server}
    {before after : LogicalTime}
    (hStep :
      DTR.DetailedBoundPayloadStep
        server
        source
        (.timeAdvance before after)
        target) :
    DTR.DetailedBoundPayloadWeakStep
      server
      source
      (.timeAdvance before after)
      target := by

  exact
    Common.WeakStep.visible
      (DTR.detailedBoundPayload_timeAdvance_visible
        before
        after)
      (Common.TauSteps.refl source)
      hStep
      (Common.TauSteps.refl target)

theorem detailedBoundPayloadConsume_is_weak
    {server : DTR.PayloadMessageServer}
    {source target :
      DTR.DetailedBoundPayloadState server}
    {selectedMessage : DTR.PendingMessage}
    (hStep :
      DTR.DetailedBoundPayloadStep
        server
        source
        (.consume selectedMessage)
        target) :
    DTR.DetailedBoundPayloadWeakStep
      server
      source
      (.consume selectedMessage)
      target := by

  exact
    Common.WeakStep.visible
      (DTR.detailedBoundPayload_consume_visible
        selectedMessage)
      (Common.TauSteps.refl source)
      hStep
      (Common.TauSteps.refl target)


end DTR
end Relico
