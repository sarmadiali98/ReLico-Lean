import Relico.Correctness.DetailedFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Tests
namespace DetailedFiniteWeakExecution

theorem forward_finite_execution_interface
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState messageServers}
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    (hSourceSteps :
      DTR.DetailedMultiStoreSteps
        declaredVariables
        messageServers
        sourceBefore
        sourceLabels
        sourceAfter)
    (hStates :
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      Correctness.ConcreteDetailedForwardStepsCompatible
        declaredVariables
        messageServers
        hSourceSteps
        targetBefore) :
    ∃ targetLabels targetAfter,
      LF.DetailedWeakSteps
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          targetLabels
          targetAfter ∧
        Correctness.ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        Correctness.ConcreteDetailedStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧
        Correctness.ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) := by

  exact
    Correctness.concreteDetailedSteps_forward_of_compatible
      hSourceSteps
      hStates
      hCompatible

theorem backward_finite_execution_interface
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore :
      DTR.DetailedMultiStoreState messageServers}
    {targetBefore targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    (hTargetSteps :
      LF.DetailedMultiStoreSteps
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        targetLabels
        targetAfter)
    (hStates :
      Correctness.ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      Correctness.ConcreteDetailedBackwardStepsCompatible
        declaredVariables
        messageServers
        sourceBefore
        hTargetSteps) :
    ∃ sourceLabels sourceAfter,
      DTR.DetailedWeakSteps
          declaredVariables
          messageServers
          sourceBefore
          sourceLabels
          sourceAfter ∧
        Correctness.ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        Correctness.ConcreteDetailedStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧
        Correctness.ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) := by

  exact
    Correctness.concreteDetailedSteps_backward_of_compatible
      hTargetSteps
      hStates
      hCompatible

end DetailedFiniteWeakExecution
end Tests
end Relico
