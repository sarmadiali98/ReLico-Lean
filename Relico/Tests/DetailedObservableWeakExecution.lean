import Relico.Correctness.DetailedObservableWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedObservableWeakExecution

theorem dtr_exact_execution_is_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {source target :
      DTR.DetailedMultiStoreState messageServers}
    {labels : List DTR.DetailedMultiStoreLabel}
    (hSteps :
      DTR.DetailedMultiStoreSteps
        declaredVariables
        messageServers
        source
        labels
        target) :
    DTR.DetailedWeakSteps
      declaredVariables
      messageServers
      source
      labels
      target := by

  exact
    DTR.detailedMultiStoreSteps_to_weakSteps
      hSteps

theorem lf_exact_execution_is_weak
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source target :
      LF.DetailedMultiStoreState messageReactions}
    {labels : List LF.DetailedMultiStoreLabel}
    (hSteps :
      LF.DetailedMultiStoreSteps
        declaredVariables
        logicalActions
        messageReactions
        source
        labels
        target) :
    LF.DetailedWeakSteps
      declaredVariables
      logicalActions
      messageReactions
      source
      labels
      target := by

  exact
    LF.detailedMultiStoreSteps_to_weakSteps
      hSteps

theorem dtr_weak_executions_append
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {source middle target :
      DTR.DetailedMultiStoreState messageServers}
    {leftLabels rightLabels :
      List DTR.DetailedMultiStoreLabel}
    (left :
      DTR.DetailedWeakSteps
        declaredVariables
        messageServers
        source
        leftLabels
        middle)
    (right :
      DTR.DetailedWeakSteps
        declaredVariables
        messageServers
        middle
        rightLabels
        target) :
    DTR.DetailedWeakSteps
      declaredVariables
      messageServers
      source
      (leftLabels ++ rightLabels)
      target := by

  exact
    DTR.detailedWeakSteps_append
      left
      right

theorem corresponding_labels_preserve_projection
    {sourceLabel : DTR.DetailedMultiStoreLabel}
    {targetLabel : LF.DetailedMultiStoreLabel}
    (hLabels :
      Correctness.ConcreteDetailedLabelCorresponds
        sourceLabel
        targetLabel) :
    Correctness.ConcreteDetailedObservableOptionCorresponds
      sourceLabel.toObservable
      targetLabel.toObservable := by

  exact
    hLabels.observableOption

theorem corresponding_weak_traces_preserve_observables
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    (hTrace :
      Correctness.ConcreteDetailedWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    Correctness.ConcreteDetailedObservableTraceCorresponds
      (DTR.detailedObservableTrace
        sourceLabels)
      (LF.detailedObservableTrace
        targetLabels) := by

  exact
    hTrace.observableProjection

end DetailedObservableWeakExecution
end Tests
end Relico
