import Relico.LF.DetailedMultiStoreSemantics

set_option autoImplicit false

namespace Relico
namespace LF

abbrev DetailedTauSteps
    (declaredVariables : List VarName)
    (logicalActions : List ActionName)
    (messageReactions : List LF.Reaction)
    (source target :
      LF.DetailedMultiStoreState messageReactions) :
    Prop :=
  Common.TauSteps
    (LF.DetailedMultiStoreStep
      declaredVariables
      logicalActions
      messageReactions)
    LF.DetailedMultiStoreLabel.isTau
    source
    target

abbrev DetailedWeakStep
    (declaredVariables : List VarName)
    (logicalActions : List ActionName)
    (messageReactions : List LF.Reaction)
    (source :
      LF.DetailedMultiStoreState messageReactions)
    (label : LF.DetailedMultiStoreLabel)
    (target :
      LF.DetailedMultiStoreState messageReactions) :
    Prop :=
  Common.WeakStep
    (LF.DetailedMultiStoreStep
      declaredVariables
      logicalActions
      messageReactions)
    LF.DetailedMultiStoreLabel.isTau
    source
    label
    target

def detailedObservableTrace
    (labels : List LF.DetailedMultiStoreLabel) :
    List LF.DetailedMultiStoreObservable :=
  Common.observableProjection
    LF.DetailedMultiStoreLabel.toObservable
    labels

@[simp]
theorem detailedObservableTrace_nil :
    LF.detailedObservableTrace [] = [] := by
  rfl

@[simp]
theorem detailedObservableTrace_tau_cons
    (remaining : List LF.DetailedMultiStoreLabel) :
    LF.detailedObservableTrace
        (LF.DetailedMultiStoreLabel.tau :: remaining) =
      LF.detailedObservableTrace remaining := by
  rfl

@[simp]
theorem detailedObservableTrace_microstep_cons
    (before after : LF.Tag)
    (remaining : List LF.DetailedMultiStoreLabel) :
    LF.detailedObservableTrace
        (LF.DetailedMultiStoreLabel.microstepAdvance
            before
            after ::
          remaining) =
      LF.detailedObservableTrace remaining := by
  rfl

@[simp]
theorem detailedObservableTrace_timeAdvance_cons
    (before after : LogicalTime)
    (remaining : List LF.DetailedMultiStoreLabel) :
    LF.detailedObservableTrace
        (LF.DetailedMultiStoreLabel.timeAdvance
            before
            after ::
          remaining) =
      LF.DetailedMultiStoreObservable.timeAdvance
          before
          after ::
        LF.detailedObservableTrace remaining := by
  rfl

@[simp]
theorem detailedObservableTrace_consume_cons
    (selectedAction : LF.PendingAction)
    (selectedReaction : LF.Reaction)
    (remaining : List LF.DetailedMultiStoreLabel) :
    LF.detailedObservableTrace
        (LF.DetailedMultiStoreLabel.consume
            selectedAction
            selectedReaction ::
          remaining) =
      LF.DetailedMultiStoreObservable.consume
          selectedAction.name
          selectedAction.tag.time ::
        LF.detailedObservableTrace remaining := by
  rfl

theorem detailedMicrostep_is_internal
    (before after : LF.Tag) :
    LF.DetailedMultiStoreLabel.isTau
      (.microstepAdvance before after) := by
  exact True.intro

theorem detailedTimeAdvance_visible
    (before after : LogicalTime) :
    ¬ LF.DetailedMultiStoreLabel.isTau
        (.timeAdvance before after) := by
  simp [LF.DetailedMultiStoreLabel.isTau]

theorem detailedConsume_visible
    (selectedAction : LF.PendingAction)
    (selectedReaction : LF.Reaction) :
    ¬ LF.DetailedMultiStoreLabel.isTau
        (.consume selectedAction selectedReaction) := by
  simp [LF.DetailedMultiStoreLabel.isTau]

theorem detailedWeakStep_of_step
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source target :
      LF.DetailedMultiStoreState messageReactions}
    {label : LF.DetailedMultiStoreLabel}
    (hStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        source
        label
        target) :
    LF.DetailedWeakStep
      declaredVariables
      logicalActions
      messageReactions
      source
      label
      target := by
  exact
    Common.WeakStep.of_step
      (isTau := LF.DetailedMultiStoreLabel.isTau)
      hStep

theorem detailedTauSteps_single
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source target :
      LF.DetailedMultiStoreState messageReactions}
    {label : LF.DetailedMultiStoreLabel}
    (hStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        source
        label
        target)
    (hTau :
      LF.DetailedMultiStoreLabel.isTau label) :
    LF.DetailedTauSteps
      declaredVariables
      logicalActions
      messageReactions
      source
      target := by
  exact Common.TauSteps.single hStep hTau

theorem detailedTauSteps_trans
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source middle target :
      LF.DetailedMultiStoreState messageReactions}
    (left :
      LF.DetailedTauSteps
        declaredVariables
        logicalActions
        messageReactions
        source
        middle)
    (right :
      LF.DetailedTauSteps
        declaredVariables
        logicalActions
        messageReactions
        middle
        target) :
    LF.DetailedTauSteps
      declaredVariables
      logicalActions
      messageReactions
      source
      target := by
  exact Common.TauSteps.trans left right

theorem detailedTauSteps_to_weakTau
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source target :
      LF.DetailedMultiStoreState messageReactions}
    (hSteps :
      LF.DetailedTauSteps
        declaredVariables
        logicalActions
        messageReactions
        source
        target) :
    LF.DetailedWeakStep
      declaredVariables
      logicalActions
      messageReactions
      source
      LF.DetailedMultiStoreLabel.tau
      target := by
  exact
    Common.WeakStep.of_tauSteps
      (label := LF.DetailedMultiStoreLabel.tau)
      LF.DetailedMultiStoreLabel.isTau_tau
      hSteps

theorem detailedWeakTau_refl
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    (state :
      LF.DetailedMultiStoreState messageReactions) :
    LF.DetailedWeakStep
      declaredVariables
      logicalActions
      messageReactions
      state
      LF.DetailedMultiStoreLabel.tau
      state := by
  exact
    Common.WeakStep.tau_refl
      (step :=
        LF.DetailedMultiStoreStep
          declaredVariables
          logicalActions
          messageReactions)
      (isTau := LF.DetailedMultiStoreLabel.isTau)
      LF.DetailedMultiStoreLabel.isTau_tau

theorem detailedStatement_is_weak
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {before after : LF.StoreState}
    {label : LF.Label}
    (hStatement :
      LF.MultiStoreStep
        declaredVariables
        logicalActions
        before
        label
        after) :
    LF.DetailedWeakStep
      declaredVariables
      logicalActions
      messageReactions
      (.stable before)
      LF.DetailedMultiStoreLabel.tau
      (.stable after) := by
  exact
    LF.detailedWeakStep_of_step
      (LF.DetailedMultiStoreStep.statement hStatement)

theorem detailedMicrostep_to_tauSteps
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source target :
      LF.DetailedMultiStoreState messageReactions}
    {beforeTag afterTag : LF.Tag}
    (hStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        source
        (.microstepAdvance beforeTag afterTag)
        target) :
    LF.DetailedTauSteps
      declaredVariables
      logicalActions
      messageReactions
      source
      target := by
  exact
    LF.detailedTauSteps_single
      hStep
      (LF.detailedMicrostep_is_internal
        beforeTag
        afterTag)

theorem detailedMicrostep_is_weakTau
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source target :
      LF.DetailedMultiStoreState messageReactions}
    {beforeTag afterTag : LF.Tag}
    (hStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        source
        (.microstepAdvance beforeTag afterTag)
        target) :
    LF.DetailedWeakStep
      declaredVariables
      logicalActions
      messageReactions
      source
      LF.DetailedMultiStoreLabel.tau
      target := by
  exact
    LF.detailedTauSteps_to_weakTau
      (LF.detailedMicrostep_to_tauSteps hStep)

theorem detailedTimeAdvance_is_weak
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source target :
      LF.DetailedMultiStoreState messageReactions}
    {before after : LogicalTime}
    (hStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        source
        (.timeAdvance before after)
        target) :
    LF.DetailedWeakStep
      declaredVariables
      logicalActions
      messageReactions
      source
      (.timeAdvance before after)
      target := by
  exact
    Common.WeakStep.visible
      (LF.detailedTimeAdvance_visible before after)
      (Common.TauSteps.refl source)
      hStep
      (Common.TauSteps.refl target)

theorem detailedConsume_is_weak
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source target :
      LF.DetailedMultiStoreState messageReactions}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        logicalActions
        messageReactions
        source
        (.consume selectedAction selectedReaction)
        target) :
    LF.DetailedWeakStep
      declaredVariables
      logicalActions
      messageReactions
      source
      (.consume selectedAction selectedReaction)
      target := by
  exact
    Common.WeakStep.visible
      (LF.detailedConsume_visible
        selectedAction
        selectedReaction)
      (Common.TauSteps.refl source)
      hStep
      (Common.TauSteps.refl target)

end LF
end Relico
