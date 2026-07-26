import Relico.Correctness.DetailedWeakFoundation

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedWeakSemantics

theorem dtr_exact_step_is_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {source target :
      DTR.DetailedMultiStoreState messageServers}
    {label : DTR.DetailedMultiStoreLabel}
    (hStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        source
        label
        target) :
    DTR.DetailedWeakStep
      declaredVariables
      messageServers
      source
      label
      target := by
  exact DTR.detailedWeakStep_of_step hStep

theorem lf_exact_step_is_weak
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
  exact LF.detailedWeakStep_of_step hStep

theorem dtr_internal_path_collapses
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {source target :
      DTR.DetailedMultiStoreState messageServers}
    (hSteps :
      DTR.DetailedTauSteps
        declaredVariables
        messageServers
        source
        target) :
    DTR.DetailedWeakStep
      declaredVariables
      messageServers
      source
      DTR.DetailedMultiStoreLabel.tau
      target := by
  exact DTR.detailedTauSteps_to_weakTau hSteps

theorem lf_internal_path_collapses
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
  exact LF.detailedTauSteps_to_weakTau hSteps

theorem dtr_tau_trace_is_unobservable :
    DTR.detailedObservableTrace
        [
          DTR.DetailedMultiStoreLabel.tau,
          DTR.DetailedMultiStoreLabel.tau
        ] =
      [] := by
  rfl

theorem lf_tau_and_microstep_trace_is_unobservable
    (before after : LF.Tag) :
    LF.detailedObservableTrace
        [
          LF.DetailedMultiStoreLabel.tau,
          LF.DetailedMultiStoreLabel.microstepAdvance
            before
            after,
          LF.DetailedMultiStoreLabel.tau
        ] =
      [] := by
  rfl

theorem lf_microstep_before_consume_is_erased
    (before after : LF.Tag)
    (selectedAction : LF.PendingAction)
    (selectedReaction : LF.Reaction) :
    LF.detailedObservableTrace
        [
          LF.DetailedMultiStoreLabel.microstepAdvance
            before
            after,
          LF.DetailedMultiStoreLabel.consume
            selectedAction
            selectedReaction
        ] =
      [
        LF.DetailedMultiStoreObservable.consume
          selectedAction.name
          selectedAction.tag.time
      ] := by
  rfl

end DetailedWeakSemantics
end Tests
end Relico
