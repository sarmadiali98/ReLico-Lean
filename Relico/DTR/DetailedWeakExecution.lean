import Relico.Common.WeakExecution
import Relico.DTR.DetailedWeakSemantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Finite executions whose individual transitions use the detailed DTR weak-step
relation.
-/
abbrev DetailedWeakSteps
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (source :
      DTR.DetailedMultiStoreState messageServers)
    (labels : List DTR.DetailedMultiStoreLabel)
    (target :
      DTR.DetailedMultiStoreState messageServers) :
    Prop :=
  Common.WeakSteps
    (DTR.DetailedMultiStoreStep
      declaredVariables
      messageServers)
    DTR.DetailedMultiStoreLabel.isTau
    source
    labels
    target

/--
Every finite exact detailed DTR execution is also a finite weak execution with
the same representative labels.
-/
theorem detailedMultiStoreSteps_to_weakSteps
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

  induction hSteps with

  | refl state =>
      exact
        Common.WeakSteps.refl state

  | cons hStep hRemaining inductionHypothesis =>
      exact
        Common.WeakSteps.cons
          (DTR.detailedWeakStep_of_step hStep)
          inductionHypothesis

/--
Detailed DTR weak executions compose.
-/
theorem detailedWeakSteps_append
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
    Common.WeakSteps.append
      left
      right

end DTR
end Relico
