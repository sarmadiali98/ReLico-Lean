import Relico.DTR.DetailedMultiStoreSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

abbrev DetailedTauSteps
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (source target :
      DTR.DetailedMultiStoreState messageServers) :
    Prop :=
  Common.TauSteps
    (DTR.DetailedMultiStoreStep
      declaredVariables
      messageServers)
    DTR.DetailedMultiStoreLabel.isTau
    source
    target

abbrev DetailedWeakStep
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (source :
      DTR.DetailedMultiStoreState messageServers)
    (label : DTR.DetailedMultiStoreLabel)
    (target :
      DTR.DetailedMultiStoreState messageServers) :
    Prop :=
  Common.WeakStep
    (DTR.DetailedMultiStoreStep
      declaredVariables
      messageServers)
    DTR.DetailedMultiStoreLabel.isTau
    source
    label
    target

def detailedObservableTrace
    (labels : List DTR.DetailedMultiStoreLabel) :
    List DTR.DetailedMultiStoreObservable :=
  Common.observableProjection
    DTR.DetailedMultiStoreLabel.toObservable
    labels

@[simp]
theorem detailedObservableTrace_nil :
    DTR.detailedObservableTrace [] = [] := by
  rfl

@[simp]
theorem detailedObservableTrace_tau_cons
    (remaining : List DTR.DetailedMultiStoreLabel) :
    DTR.detailedObservableTrace
        (DTR.DetailedMultiStoreLabel.tau :: remaining) =
      DTR.detailedObservableTrace remaining := by
  rfl

@[simp]
theorem detailedObservableTrace_timeAdvance_cons
    (before after : LogicalTime)
    (remaining : List DTR.DetailedMultiStoreLabel) :
    DTR.detailedObservableTrace
        (DTR.DetailedMultiStoreLabel.timeAdvance
            before
            after ::
          remaining) =
      DTR.DetailedMultiStoreObservable.timeAdvance
          before
          after ::
        DTR.detailedObservableTrace remaining := by
  rfl

@[simp]
theorem detailedObservableTrace_consume_cons
    (selectedMessage : DTR.PendingMessage)
    (selectedServer : DTR.MessageServer)
    (remaining : List DTR.DetailedMultiStoreLabel) :
    DTR.detailedObservableTrace
        (DTR.DetailedMultiStoreLabel.consume
            selectedMessage
            selectedServer ::
          remaining) =
      DTR.DetailedMultiStoreObservable.consume
          selectedMessage.name
          selectedMessage.arrivalTime ::
        DTR.detailedObservableTrace remaining := by
  rfl

theorem detailedTimeAdvance_visible
    (before after : LogicalTime) :
    ¬ DTR.DetailedMultiStoreLabel.isTau
        (.timeAdvance before after) := by
  simp [DTR.DetailedMultiStoreLabel.isTau]

theorem detailedConsume_visible
    (selectedMessage : DTR.PendingMessage)
    (selectedServer : DTR.MessageServer) :
    ¬ DTR.DetailedMultiStoreLabel.isTau
        (.consume selectedMessage selectedServer) := by
  simp [DTR.DetailedMultiStoreLabel.isTau]

theorem detailedWeakStep_of_step
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
  exact
    Common.WeakStep.of_step
      (isTau := DTR.DetailedMultiStoreLabel.isTau)
      hStep

theorem detailedTauSteps_single
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
        target)
    (hTau :
      DTR.DetailedMultiStoreLabel.isTau label) :
    DTR.DetailedTauSteps
      declaredVariables
      messageServers
      source
      target := by
  exact Common.TauSteps.single hStep hTau

theorem detailedTauSteps_trans
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {source middle target :
      DTR.DetailedMultiStoreState messageServers}
    (left :
      DTR.DetailedTauSteps
        declaredVariables
        messageServers
        source
        middle)
    (right :
      DTR.DetailedTauSteps
        declaredVariables
        messageServers
        middle
        target) :
    DTR.DetailedTauSteps
      declaredVariables
      messageServers
      source
      target := by
  exact Common.TauSteps.trans left right

theorem detailedTauSteps_to_weakTau
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
  exact
    Common.WeakStep.of_tauSteps
      (label := DTR.DetailedMultiStoreLabel.tau)
      DTR.DetailedMultiStoreLabel.isTau_tau
      hSteps

theorem detailedWeakTau_refl
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    (state :
      DTR.DetailedMultiStoreState messageServers) :
    DTR.DetailedWeakStep
      declaredVariables
      messageServers
      state
      DTR.DetailedMultiStoreLabel.tau
      state := by
  exact
    Common.WeakStep.tau_refl
      (step :=
        DTR.DetailedMultiStoreStep
          declaredVariables
          messageServers)
      (isTau := DTR.DetailedMultiStoreLabel.isTau)
      DTR.DetailedMultiStoreLabel.isTau_tau

theorem detailedStatement_is_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {before after : DTR.StoreState}
    {label : DTR.Label}
    (hStatement :
      DTR.MultiStoreStep
        declaredVariables
        (DTR.messageServerNames messageServers)
        before
        label
        after) :
    DTR.DetailedWeakStep
      declaredVariables
      messageServers
      (.stable before)
      DTR.DetailedMultiStoreLabel.tau
      (.stable after) := by
  exact
    DTR.detailedWeakStep_of_step
      (DTR.DetailedMultiStoreStep.statement hStatement)

theorem detailedTimeAdvance_is_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {source target :
      DTR.DetailedMultiStoreState messageServers}
    {before after : LogicalTime}
    (hStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        source
        (.timeAdvance before after)
        target) :
    DTR.DetailedWeakStep
      declaredVariables
      messageServers
      source
      (.timeAdvance before after)
      target := by
  exact
    Common.WeakStep.visible
      (DTR.detailedTimeAdvance_visible before after)
      (Common.TauSteps.refl source)
      hStep
      (Common.TauSteps.refl target)

theorem detailedConsume_is_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {source target :
      DTR.DetailedMultiStoreState messageServers}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    (hStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        source
        (.consume selectedMessage selectedServer)
        target) :
    DTR.DetailedWeakStep
      declaredVariables
      messageServers
      source
      (.consume selectedMessage selectedServer)
      target := by
  exact
    Common.WeakStep.visible
      (DTR.detailedConsume_visible
        selectedMessage
        selectedServer)
      (Common.TauSteps.refl source)
      hStep
      (Common.TauSteps.refl target)

end DTR
end Relico
