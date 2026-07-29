import Relico.DTR.DetailedMultiStorePayloadSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
DTR detailed labels treated as internal by the payload weak semantics.

DTR has no microstep label. Only ordinary statement execution is silent.
-/
inductive DetailedMultiStorePayloadSilentLabel :
    DetailedMultiStorePayloadLabel →
      Prop where

  | tau :
      DetailedMultiStorePayloadSilentLabel
        .tau

/--
Visible payload-aware DTR detailed labels.
-/
inductive DetailedMultiStorePayloadVisibleLabel :
    DetailedMultiStorePayloadLabel →
      Prop where

  | timeAdvance
      (before after :
        LogicalTime) :
      DetailedMultiStorePayloadVisibleLabel
        (.timeAdvance
          before
          after)

  | consume
      (selectedMessage :
        PendingMessage)
      (selectedServer :
        MultiStorePayloadMessageServer) :
      DetailedMultiStorePayloadVisibleLabel
        (.consume
          selectedMessage
          selectedServer)

/--
Zero or more internal payload-aware DTR detailed transitions.
-/
inductive DetailedMultiStorePayloadTauSteps
    (messageServers :
      List MultiStorePayloadMessageServer) :
    DetailedMultiStorePayloadState
        messageServers →
      DetailedMultiStorePayloadState
          messageServers →
        Prop where

  | refl
      (state :
        DetailedMultiStorePayloadState
          messageServers) :
      DetailedMultiStorePayloadTauSteps
        messageServers
        state
        state

  | tail
      {before middle after :
        DetailedMultiStorePayloadState
          messageServers}
      {label :
        DetailedMultiStorePayloadLabel}
      (step :
        DetailedMultiStorePayloadStep
          messageServers
          before
          label
          middle)
      (silent :
        DetailedMultiStorePayloadSilentLabel
          label)
      (remaining :
        DetailedMultiStorePayloadTauSteps
          messageServers
          middle
          after) :
      DetailedMultiStorePayloadTauSteps
        messageServers
        before
        after

/--
One payload-aware DTR weak transition.

A weak tau transition is an internal closure. A visible transition consists
of an internal prefix, one exact visible detailed step, and an internal
suffix.
-/
inductive DetailedMultiStorePayloadWeakStep
    (messageServers :
      List MultiStorePayloadMessageServer) :
    DetailedMultiStorePayloadState
        messageServers →
      DetailedMultiStorePayloadLabel →
        DetailedMultiStorePayloadState
            messageServers →
          Prop where

  | tau
      {before after :
        DetailedMultiStorePayloadState
          messageServers}
      (steps :
        DetailedMultiStorePayloadTauSteps
          messageServers
          before
          after) :
      DetailedMultiStorePayloadWeakStep
        messageServers
        before
        .tau
        after

  | visible
      {before after prefixState suffixState :
        DetailedMultiStorePayloadState
          messageServers}
      {label :
        DetailedMultiStorePayloadLabel}
      (visibleLabel :
        DetailedMultiStorePayloadVisibleLabel
          label)
      (internalBefore :
        DetailedMultiStorePayloadTauSteps
          messageServers
          before
          prefixState)
      (step :
        DetailedMultiStorePayloadStep
          messageServers
          prefixState
          label
          suffixState)
      (internalAfter :
        DetailedMultiStorePayloadTauSteps
          messageServers
          suffixState
          after) :
      DetailedMultiStorePayloadWeakStep
        messageServers
        before
        label
        after

/--
Internal DTR closures compose.
-/
theorem detailedMultiStorePayloadTauSteps_trans
    {messageServers :
      List MultiStorePayloadMessageServer}
    {left middle right :
      DetailedMultiStorePayloadState
        messageServers}
    (first :
      DetailedMultiStorePayloadTauSteps
        messageServers
        left
        middle)
    (second :
      DetailedMultiStorePayloadTauSteps
        messageServers
        middle
        right) :
    DetailedMultiStorePayloadTauSteps
      messageServers
      left
      right := by

  induction first with

  | refl =>
      exact second

  | tail step silent remaining inductionHypothesis =>
      exact
        DetailedMultiStorePayloadTauSteps.tail
          step
          silent
          (inductionHypothesis
            second)

/--
Every detailed DTR state has a reflexive weak tau transition.
-/
theorem detailedMultiStorePayloadWeakTau_refl
    {messageServers :
      List MultiStorePayloadMessageServer}
    (state :
      DetailedMultiStorePayloadState
        messageServers) :
    DetailedMultiStorePayloadWeakStep
      messageServers
      state
      .tau
      state := by

  exact
    DetailedMultiStorePayloadWeakStep.tau
      (DetailedMultiStorePayloadTauSteps.refl
        state)

/--
An ordinary DTR payload statement transition is one internal transition.
-/
theorem detailedMultiStorePayloadStatement_to_tauSteps
    {messageServers :
      List MultiStorePayloadMessageServer}
    {before after :
      MultiStorePayloadState}
    (statementStep :
      MultiStorePayloadStep
        before
        after) :
    DetailedMultiStorePayloadTauSteps
      messageServers
      (.stable before)
      (.stable after) := by

  exact
    DetailedMultiStorePayloadTauSteps.tail
      (DetailedMultiStorePayloadStep.statement
        statementStep)
      DetailedMultiStorePayloadSilentLabel.tau
      (DetailedMultiStorePayloadTauSteps.refl
        (.stable after))

/--
An ordinary DTR payload statement transition is a weak tau transition.
-/
theorem detailedMultiStorePayloadStatement_is_weak
    {messageServers :
      List MultiStorePayloadMessageServer}
    {before after :
      MultiStorePayloadState}
    (statementStep :
      MultiStorePayloadStep
        before
        after) :
    DetailedMultiStorePayloadWeakStep
      messageServers
      (.stable before)
      .tau
      (.stable after) := by

  exact
    DetailedMultiStorePayloadWeakStep.tau
      (detailedMultiStorePayloadStatement_to_tauSteps
        statementStep)

/--
An exact visible DTR metric-time transition is a weak visible transition.
-/
theorem detailedMultiStorePayloadTimeAdvance_is_weak
    {messageServers :
      List MultiStorePayloadMessageServer}
    {before after :
      DetailedMultiStorePayloadState
        messageServers}
    {timeBefore timeAfter :
      LogicalTime}
    (step :
      DetailedMultiStorePayloadStep
        messageServers
        before
        (.timeAdvance
          timeBefore
          timeAfter)
        after) :
    DetailedMultiStorePayloadWeakStep
      messageServers
      before
      (.timeAdvance
        timeBefore
        timeAfter)
      after := by

  exact
    DetailedMultiStorePayloadWeakStep.visible
      (DetailedMultiStorePayloadVisibleLabel.timeAdvance
        timeBefore
        timeAfter)
      (DetailedMultiStorePayloadTauSteps.refl
        before)
      step
      (DetailedMultiStorePayloadTauSteps.refl
        after)

/--
An exact visible DTR payload consumption is a weak visible transition.
-/
theorem detailedMultiStorePayloadConsume_is_weak
    {messageServers :
      List MultiStorePayloadMessageServer}
    {before after :
      DetailedMultiStorePayloadState
        messageServers}
    {selectedMessage :
      PendingMessage}
    {selectedServer :
      MultiStorePayloadMessageServer}
    (step :
      DetailedMultiStorePayloadStep
        messageServers
        before
        (.consume
          selectedMessage
          selectedServer)
        after) :
    DetailedMultiStorePayloadWeakStep
      messageServers
      before
      (.consume
        selectedMessage
        selectedServer)
      after := by

  exact
    DetailedMultiStorePayloadWeakStep.visible
      (DetailedMultiStorePayloadVisibleLabel.consume
        selectedMessage
        selectedServer)
      (DetailedMultiStorePayloadTauSteps.refl
        before)
      step
      (DetailedMultiStorePayloadTauSteps.refl
        after)

end DTR
end Relico
