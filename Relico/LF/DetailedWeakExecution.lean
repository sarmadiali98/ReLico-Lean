import Relico.Common.WeakExecution
import Relico.LF.DetailedWeakSemantics

set_option autoImplicit false

namespace Relico
namespace LF

/--
Finite executions whose individual transitions use the detailed generated-LF
weak-step relation.
-/
abbrev DetailedWeakSteps
    (declaredVariables : List VarName)
    (logicalActions : List ActionName)
    (messageReactions : List LF.Reaction)
    (source :
      LF.DetailedMultiStoreState messageReactions)
    (labels : List LF.DetailedMultiStoreLabel)
    (target :
      LF.DetailedMultiStoreState messageReactions) :
    Prop :=
  Common.WeakSteps
    (LF.DetailedMultiStoreStep
      declaredVariables
      logicalActions
      messageReactions)
    LF.DetailedMultiStoreLabel.isTau
    source
    labels
    target

/--
Every finite exact detailed generated-LF execution is also a finite weak
execution with the same representative labels.
-/
theorem detailedMultiStoreSteps_to_weakSteps
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

  induction hSteps with

  | refl state =>
      exact
        Common.WeakSteps.refl state

  | cons hStep hRemaining inductionHypothesis =>
      exact
        Common.WeakSteps.cons
          (LF.detailedWeakStep_of_step hStep)
          inductionHypothesis

/--
Detailed generated-LF weak executions compose.
-/
theorem detailedWeakSteps_append
    {declaredVariables : List VarName}
    {logicalActions : List ActionName}
    {messageReactions : List LF.Reaction}
    {source middle target :
      LF.DetailedMultiStoreState messageReactions}
    {leftLabels rightLabels :
      List LF.DetailedMultiStoreLabel}
    (left :
      LF.DetailedWeakSteps
        declaredVariables
        logicalActions
        messageReactions
        source
        leftLabels
        middle)
    (right :
      LF.DetailedWeakSteps
        declaredVariables
        logicalActions
        messageReactions
        middle
        rightLabels
        target) :
    LF.DetailedWeakSteps
      declaredVariables
      logicalActions
      messageReactions
      source
      (leftLabels ++ rightLabels)
      target := by

  exact
    Common.WeakSteps.append
      left
      right

end LF
end Relico
