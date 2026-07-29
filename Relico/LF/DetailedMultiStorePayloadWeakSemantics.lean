import Relico.LF.DetailedMultiStorePayloadSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
LF detailed labels treated as internal by the payload weak semantics.

Both ordinary statement execution and target-only microstep advancement are
silent. Metric-time advancement and reaction consumption remain visible.
-/
inductive DetailedMultiStorePayloadSilentLabel :
    DetailedMultiStorePayloadLabel →
      Prop where

  | tau :
      DetailedMultiStorePayloadSilentLabel
        .tau

  | microstep
      (before after :
        Tag) :
      DetailedMultiStorePayloadSilentLabel
        (.microstepAdvance
          before
          after)

/--
Visible generated-LF payload detailed labels.
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
      (selectedAction :
        PendingAction)
      (selectedReaction :
        MultiStorePayloadReaction) :
      DetailedMultiStorePayloadVisibleLabel
        (.consume
          selectedAction
          selectedReaction)

/--
Zero or more internal generated-LF payload detailed transitions.
-/
inductive DetailedMultiStorePayloadTauSteps
    (messageReactions :
      List MultiStorePayloadReaction) :
    DetailedMultiStorePayloadState
        messageReactions →
      DetailedMultiStorePayloadState
          messageReactions →
        Prop where

  | refl
      (state :
        DetailedMultiStorePayloadState
          messageReactions) :
      DetailedMultiStorePayloadTauSteps
        messageReactions
        state
        state

  | tail
      {before middle after :
        DetailedMultiStorePayloadState
          messageReactions}
      {label :
        DetailedMultiStorePayloadLabel}
      (step :
        DetailedMultiStorePayloadStep
          messageReactions
          before
          label
          middle)
      (silent :
        DetailedMultiStorePayloadSilentLabel
          label)
      (remaining :
        DetailedMultiStorePayloadTauSteps
          messageReactions
          middle
          after) :
      DetailedMultiStorePayloadTauSteps
        messageReactions
        before
        after

/--
One generated-LF payload weak transition.

Target statement and microstep transitions may occur before or after one
visible metric-time or consumption transition.
-/
inductive DetailedMultiStorePayloadWeakStep
    (messageReactions :
      List MultiStorePayloadReaction) :
    DetailedMultiStorePayloadState
        messageReactions →
      DetailedMultiStorePayloadLabel →
        DetailedMultiStorePayloadState
            messageReactions →
          Prop where

  | tau
      {before after :
        DetailedMultiStorePayloadState
          messageReactions}
      (steps :
        DetailedMultiStorePayloadTauSteps
          messageReactions
          before
          after) :
      DetailedMultiStorePayloadWeakStep
        messageReactions
        before
        .tau
        after

  | visible
      {before after prefixState suffixState :
        DetailedMultiStorePayloadState
          messageReactions}
      {label :
        DetailedMultiStorePayloadLabel}
      (visibleLabel :
        DetailedMultiStorePayloadVisibleLabel
          label)
      (internalBefore :
        DetailedMultiStorePayloadTauSteps
          messageReactions
          before
          prefixState)
      (step :
        DetailedMultiStorePayloadStep
          messageReactions
          prefixState
          label
          suffixState)
      (internalAfter :
        DetailedMultiStorePayloadTauSteps
          messageReactions
          suffixState
          after) :
      DetailedMultiStorePayloadWeakStep
        messageReactions
        before
        label
        after

/--
Internal generated-LF closures compose.
-/
theorem detailedMultiStorePayloadTauSteps_trans
    {messageReactions :
      List MultiStorePayloadReaction}
    {left middle right :
      DetailedMultiStorePayloadState
        messageReactions}
    (first :
      DetailedMultiStorePayloadTauSteps
        messageReactions
        left
        middle)
    (second :
      DetailedMultiStorePayloadTauSteps
        messageReactions
        middle
        right) :
    DetailedMultiStorePayloadTauSteps
      messageReactions
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
Every generated-LF detailed state has a reflexive weak tau transition.
-/
theorem detailedMultiStorePayloadWeakTau_refl
    {messageReactions :
      List MultiStorePayloadReaction}
    (state :
      DetailedMultiStorePayloadState
        messageReactions) :
    DetailedMultiStorePayloadWeakStep
      messageReactions
      state
      .tau
      state := by

  exact
    DetailedMultiStorePayloadWeakStep.tau
      (DetailedMultiStorePayloadTauSteps.refl
        state)

/--
An LF payload statement transition contributes one internal transition.
-/
theorem detailedMultiStorePayloadStatement_to_tauSteps
    {messageReactions :
      List MultiStorePayloadReaction}
    {before after :
      MultiStorePayloadState}
    (statementStep :
      MultiStorePayloadStep
        before
        after) :
    DetailedMultiStorePayloadTauSteps
      messageReactions
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
An LF payload statement transition is a weak tau transition.
-/
theorem detailedMultiStorePayloadStatement_is_weak
    {messageReactions :
      List MultiStorePayloadReaction}
    {before after :
      MultiStorePayloadState}
    (statementStep :
      MultiStorePayloadStep
        before
        after) :
    DetailedMultiStorePayloadWeakStep
      messageReactions
      (.stable before)
      .tau
      (.stable after) := by

  exact
    DetailedMultiStorePayloadWeakStep.tau
      (detailedMultiStorePayloadStatement_to_tauSteps
        statementStep)

/--
An exact LF microstep transition contributes one internal transition.
-/
theorem detailedMultiStorePayloadMicrostep_to_tauSteps
    {messageReactions :
      List MultiStorePayloadReaction}
    {before after :
      DetailedMultiStorePayloadState
        messageReactions}
    {tagBefore tagAfter :
      Tag}
    (step :
      DetailedMultiStorePayloadStep
        messageReactions
        before
        (.microstepAdvance
          tagBefore
          tagAfter)
        after) :
    DetailedMultiStorePayloadTauSteps
      messageReactions
      before
      after := by

  exact
    DetailedMultiStorePayloadTauSteps.tail
      step
      (DetailedMultiStorePayloadSilentLabel.microstep
        tagBefore
        tagAfter)
      (DetailedMultiStorePayloadTauSteps.refl
        after)

/--
An exact visible LF metric-time transition is a weak visible transition.
-/
theorem detailedMultiStorePayloadTimeAdvance_is_weak
    {messageReactions :
      List MultiStorePayloadReaction}
    {before after :
      DetailedMultiStorePayloadState
        messageReactions}
    {timeBefore timeAfter :
      LogicalTime}
    (step :
      DetailedMultiStorePayloadStep
        messageReactions
        before
        (.timeAdvance
          timeBefore
          timeAfter)
        after) :
    DetailedMultiStorePayloadWeakStep
      messageReactions
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
An exact visible LF payload consumption is a weak visible transition.
-/
theorem detailedMultiStorePayloadConsume_is_weak
    {messageReactions :
      List MultiStorePayloadReaction}
    {before after :
      DetailedMultiStorePayloadState
        messageReactions}
    {selectedAction :
      PendingAction}
    {selectedReaction :
      MultiStorePayloadReaction}
    (step :
      DetailedMultiStorePayloadStep
        messageReactions
        before
        (.consume
          selectedAction
          selectedReaction)
        after) :
    DetailedMultiStorePayloadWeakStep
      messageReactions
      before
      (.consume
        selectedAction
        selectedReaction)
      after := by

  exact
    DetailedMultiStorePayloadWeakStep.visible
      (DetailedMultiStorePayloadVisibleLabel.consume
        selectedAction
        selectedReaction)
      (DetailedMultiStorePayloadTauSteps.refl
        before)
      step
      (DetailedMultiStorePayloadTauSteps.refl
        after)

/--
Future LF consumption with a positive destination microstep is one weak
visible consumption preceded by the target-only microstep.
-/
theorem detailedMultiStorePayloadConsumeAfterTimePositive_is_weak
    {messageReactions :
      List MultiStorePayloadReaction}
    {before after :
      MultiStorePayloadState}
    {selectedAction :
      PendingAction}
    {selectedReaction :
      MultiStorePayloadReaction}
    (dispatch :
      MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (positiveMicrostep :
      0 <
        after.currentTag.microstep) :
    DetailedMultiStorePayloadWeakStep
      messageReactions
      (.afterTime
        before
        selectedAction
        selectedReaction
        after
        dispatch)
      (.consume
        selectedAction
        selectedReaction)
      (.stable after) := by

  have internalPrefix :
      DetailedMultiStorePayloadTauSteps
        messageReactions
        (.afterTime
          before
          selectedAction
          selectedReaction
          after
          dispatch)
        (.dispatchReady
          before
          selectedAction
          selectedReaction
          after
          dispatch) :=

    detailedMultiStorePayloadMicrostep_to_tauSteps
      (DetailedMultiStorePayloadStep.microstepAfterTime
        dispatch
        positiveMicrostep)

  exact
    DetailedMultiStorePayloadWeakStep.visible
      (DetailedMultiStorePayloadVisibleLabel.consume
        selectedAction
        selectedReaction)
      internalPrefix
      (DetailedMultiStorePayloadStep.consumeReady
        dispatch)
      (DetailedMultiStorePayloadTauSteps.refl
        (.stable after))

/--
A same-time LF microstep followed by reaction firing is one weak visible
consumption from the original stable state.
-/
theorem detailedMultiStorePayloadSameTimeMicrostepThenConsume_is_weak
    {messageReactions :
      List MultiStorePayloadReaction}
    {before after :
      MultiStorePayloadState}
    {selectedAction :
      PendingAction}
    {selectedReaction :
      MultiStorePayloadReaction}
    (dispatch :
      MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (sameTime :
      before.currentTag.time =
        after.currentTag.time)
    (laterMicrostep :
      before.currentTag.microstep <
        after.currentTag.microstep) :
    DetailedMultiStorePayloadWeakStep
      messageReactions
      (.stable before)
      (.consume
        selectedAction
        selectedReaction)
      (.stable after) := by

  have internalPrefix :
      DetailedMultiStorePayloadTauSteps
        messageReactions
        (.stable before)
        (.dispatchReady
          before
          selectedAction
          selectedReaction
          after
          dispatch) :=

    detailedMultiStorePayloadMicrostep_to_tauSteps
      (DetailedMultiStorePayloadStep.microstepSameTime
        dispatch
        sameTime
        laterMicrostep)

  exact
    DetailedMultiStorePayloadWeakStep.visible
      (DetailedMultiStorePayloadVisibleLabel.consume
        selectedAction
        selectedReaction)
      internalPrefix
      (DetailedMultiStorePayloadStep.consumeReady
        dispatch)
      (DetailedMultiStorePayloadTauSteps.refl
        (.stable after))

end LF
end Relico
