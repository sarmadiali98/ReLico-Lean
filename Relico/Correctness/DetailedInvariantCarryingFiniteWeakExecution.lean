import Relico.Correctness.DetailedInvariantCarryingForwardMatch

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Finite forward correspondence obtained by repeatedly selecting the canonical
invariant-carrying generated-LF weak match.

Unlike `concreteDetailedSteps_forward_of_compatible`, this theorem does not
quantify over every possible continuation match. It recurses only through the
destination selected by `concreteDetailedForwardInvariantMatch`.
-/
theorem concreteDetailedSteps_forward_chosen
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers}
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
      ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hSourceInvariant :
      ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceBefore)
    (hTargetInvariant :
      ConcreteDetailedTargetRuntimeInvariant
        messageServers
        targetBefore)
    (hMessageBodiesWellFormed :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.MultiStoreWellFormed
            declaredVariables
            (DTR.messageServerNames
              messageServers)
            messageServer.body)
    (hMessageBodiesTiming :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.PriorityTimingWellFormed
            messageServer.body) :
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
        ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        ConcreteDetailedStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧
        ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) ∧
        ConcreteDetailedSourceRuntimeInvariant
          declaredVariables
          messageServers
          sourceAfter ∧
        ConcreteDetailedTargetRuntimeInvariant
          messageServers
          targetAfter := by

  induction hSourceSteps generalizing targetBefore with

  | refl sourceState =>
      exact
        ⟨[],
         targetBefore,
         Common.WeakSteps.refl
           targetBefore,
         ConcreteDetailedWeakLabelTraceCorresponds.nil,
         hStates,
         ConcreteDetailedObservableTraceCorresponds.nil,
         hSourceInvariant,
         hTargetInvariant⟩

  | cons hHead hTail inductionHypothesis =>

      rcases
          concreteDetailedForwardInvariantMatch
            hHead
            hStates
            hSourceInvariant
            hTargetInvariant
            hMessageBodiesWellFormed
            hMessageBodiesTiming
        with
          ⟨targetHeadLabel,
           targetMiddle,
           hTargetHead,
           hHeadLabels,
           hMiddleStates,
           hMiddleSourceInvariant,
           hMiddleTargetInvariant⟩

      rcases
          inductionHypothesis
            hMiddleStates
            hMiddleSourceInvariant
            hMiddleTargetInvariant
        with
          ⟨targetRemainingLabels,
           targetAfter,
           hTargetTail,
           hTailLabels,
           hFinalStates,
           _hObservableTail,
           hFinalSourceInvariant,
           hFinalTargetInvariant⟩

      have hTrace :
          ConcreteDetailedWeakLabelTraceCorresponds
            (_ :: _)
            (targetHeadLabel ::
              targetRemainingLabels) :=

        ConcreteDetailedWeakLabelTraceCorresponds.cons
          hHeadLabels
          hTailLabels

      exact
        ⟨targetHeadLabel ::
            targetRemainingLabels,
         targetAfter,
         Common.WeakSteps.cons
           hTargetHead
           hTargetTail,
         hTrace,
         hFinalStates,
         hTrace.observableProjection,
         hFinalSourceInvariant,
         hFinalTargetInvariant⟩

/--
Finite backward correspondence obtained by repeatedly selecting the
invariant-carrying DTR weak match for each exact generated-LF step.

The recursion follows only the destination selected by
`concreteDetailedBackwardInvariantMatch`; no universal continuation
compatibility predicate is required.
-/
theorem concreteDetailedSteps_backward_chosen
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore :
      DTR.DetailedMultiStoreState
        messageServers}
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
      ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hSourceInvariant :
      ConcreteDetailedSourceRuntimeInvariant
        declaredVariables
        messageServers
        sourceBefore)
    (hTargetInvariant :
      ConcreteDetailedTargetRuntimeInvariant
        messageServers
        targetBefore)
    (hMessageBodiesWellFormed :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.MultiStoreWellFormed
            declaredVariables
            (DTR.messageServerNames
              messageServers)
            messageServer.body)
    (hMessageBodiesTiming :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.PriorityTimingWellFormed
            messageServer.body) :
    ∃ sourceLabels sourceAfter,
      DTR.DetailedWeakSteps
          declaredVariables
          messageServers
          sourceBefore
          sourceLabels
          sourceAfter ∧
        ConcreteDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        ConcreteDetailedStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧
        ConcreteDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) ∧
        ConcreteDetailedSourceRuntimeInvariant
          declaredVariables
          messageServers
          sourceAfter ∧
        ConcreteDetailedTargetRuntimeInvariant
          messageServers
          targetAfter := by

  induction hTargetSteps generalizing sourceBefore with

  | refl targetState =>
      exact
        ⟨[],
         sourceBefore,
         Common.WeakSteps.refl
           sourceBefore,
         ConcreteDetailedWeakLabelTraceCorresponds.nil,
         hStates,
         ConcreteDetailedObservableTraceCorresponds.nil,
         hSourceInvariant,
         hTargetInvariant⟩

  | cons hHead hTail inductionHypothesis =>

      rcases
          concreteDetailedBackwardInvariantMatch
            hHead
            hStates
            hSourceInvariant
            hTargetInvariant
            hMessageBodiesWellFormed
            hMessageBodiesTiming
        with
          ⟨sourceHeadLabel,
           sourceMiddle,
           hSourceHead,
           hHeadLabels,
           hMiddleStates,
           hMiddleSourceInvariant,
           hMiddleTargetInvariant⟩

      rcases
          inductionHypothesis
            hMiddleStates
            hMiddleSourceInvariant
            hMiddleTargetInvariant
        with
          ⟨sourceRemainingLabels,
           sourceAfter,
           hSourceTail,
           hTailLabels,
           hFinalStates,
           _hObservableTail,
           hFinalSourceInvariant,
           hFinalTargetInvariant⟩

      have hTrace :
          ConcreteDetailedWeakLabelTraceCorresponds
            (sourceHeadLabel ::
              sourceRemainingLabels)
            (_ :: _) :=

        ConcreteDetailedWeakLabelTraceCorresponds.cons
          hHeadLabels
          hTailLabels

      exact
        ⟨sourceHeadLabel ::
            sourceRemainingLabels,
         sourceAfter,
         Common.WeakSteps.cons
           hSourceHead
           hSourceTail,
         hTrace,
         hFinalStates,
         hTrace.observableProjection,
         hFinalSourceInvariant,
         hFinalTargetInvariant⟩

end Correctness
end Relico
