import Relico.Correctness.DirectLFDetailedFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between one paper-level detailed DTR observable and one
paper-level generated-LF observable in the DirectLF runtime model.

Metric-time advancement preserves both endpoints. Consumption preserves the
generated action name and logical occurrence time.
-/
inductive DirectLFDetailedObservableCorresponds :
    DTR.DetailedMultiStoreObservable →
    LF.DetailedMultiStoreObservable →
    Prop where

  | timeAdvance
      {sourceBefore sourceAfter :
        LogicalTime}
      {targetBefore targetAfter :
        LogicalTime}
      (beforeTime :
        targetBefore =
          sourceBefore)
      (afterTime :
        targetAfter =
          sourceAfter) :
      DirectLFDetailedObservableCorresponds
        (.timeAdvance
          sourceBefore
          sourceAfter)
        (.timeAdvance
          targetBefore
          targetAfter)

  | consume
      {sourceName : MsgName}
      {sourceTime : LogicalTime}
      {targetName : ActionName}
      {targetTime : LogicalTime}
      (actionName :
        targetName =
          Translation.actionNameFor
            sourceName)
      (logicalTime :
        targetTime =
          sourceTime) :
      DirectLFDetailedObservableCorresponds
        (.consume
          sourceName
          sourceTime)
        (.consume
          targetName
          targetTime)

/--
Correspondence between optional observable projections of DirectLF detailed
labels.

DTR statement execution, generated-LF statement execution, and generated-LF
microstep progression all project to `none`.
-/
inductive DirectLFDetailedObservableOptionCorresponds :
    Option DTR.DetailedMultiStoreObservable →
    Option LF.DetailedMultiStoreObservable →
    Prop where

  | none :
      DirectLFDetailedObservableOptionCorresponds
        none
        none

  | some
      {sourceObservable :
        DTR.DetailedMultiStoreObservable}
      {targetObservable :
        LF.DetailedMultiStoreObservable}
      (observable :
        DirectLFDetailedObservableCorresponds
          sourceObservable
          targetObservable) :
      DirectLFDetailedObservableOptionCorresponds
        (some sourceObservable)
        (some targetObservable)

/--
DirectLF detailed-label correspondence preserves optional observable
projection.
-/
theorem DirectLFDetailedLabelCorresponds.observableOption
    {sourceLabel :
      DTR.DetailedMultiStoreLabel}
    {targetLabel :
      LF.DetailedMultiStoreLabel}
    (hLabels :
      DirectLFDetailedLabelCorresponds
        sourceLabel
        targetLabel) :
    DirectLFDetailedObservableOptionCorresponds
      sourceLabel.toObservable
      targetLabel.toObservable := by

  cases hLabels with

  | tau =>
      exact
        DirectLFDetailedObservableOptionCorresponds.none

  | microstep before after =>
      exact
        DirectLFDetailedObservableOptionCorresponds.none

  | timeAdvance beforeTime afterTime =>
      exact
        DirectLFDetailedObservableOptionCorresponds.some
          (DirectLFDetailedObservableCorresponds.timeAdvance
            beforeTime
            afterTime)

  | consume hOccurrence hReaction =>
      exact
        DirectLFDetailedObservableOptionCorresponds.some
          (DirectLFDetailedObservableCorresponds.consume
            hOccurrence.actionName
            hOccurrence.logicalTime)

/--
Pointwise correspondence between finite DirectLF observable traces.
-/
inductive DirectLFDetailedObservableTraceCorresponds :
    List DTR.DetailedMultiStoreObservable →
    List LF.DetailedMultiStoreObservable →
    Prop where

  | nil :
      DirectLFDetailedObservableTraceCorresponds
        []
        []

  | cons
      {sourceObservable :
        DTR.DetailedMultiStoreObservable}
      {targetObservable :
        LF.DetailedMultiStoreObservable}
      {sourceRemaining :
        List DTR.DetailedMultiStoreObservable}
      {targetRemaining :
        List LF.DetailedMultiStoreObservable}
      (head :
        DirectLFDetailedObservableCorresponds
          sourceObservable
          targetObservable)
      (tail :
        DirectLFDetailedObservableTraceCorresponds
          sourceRemaining
          targetRemaining) :
      DirectLFDetailedObservableTraceCorresponds
        (sourceObservable :: sourceRemaining)
        (targetObservable :: targetRemaining)

namespace DirectLFDetailedObservableTraceCorresponds

/--
Corresponding DirectLF observable traces have equal lengths.
-/
theorem length_eq
    {sourceObservables :
      List DTR.DetailedMultiStoreObservable}
    {targetObservables :
      List LF.DetailedMultiStoreObservable}
    (hTrace :
      DirectLFDetailedObservableTraceCorresponds
        sourceObservables
        targetObservables) :
    sourceObservables.length =
      targetObservables.length := by

  induction hTrace with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

/--
DirectLF observable-trace correspondence composes over concatenation.
-/
theorem append
    {sourceLeft sourceRight :
      List DTR.DetailedMultiStoreObservable}
    {targetLeft targetRight :
      List LF.DetailedMultiStoreObservable}
    (left :
      DirectLFDetailedObservableTraceCorresponds
        sourceLeft
        targetLeft)
    (right :
      DirectLFDetailedObservableTraceCorresponds
        sourceRight
        targetRight) :
    DirectLFDetailedObservableTraceCorresponds
      (sourceLeft ++ sourceRight)
      (targetLeft ++ targetRight) := by

  induction left with

  | nil =>
      simpa using right

  | cons head tail inductionHypothesis =>
      exact
        DirectLFDetailedObservableTraceCorresponds.cons
          head
          inductionHypothesis

end DirectLFDetailedObservableTraceCorresponds

/--
Pointwise DirectLF weak-label correspondence preserves the paper-level
observable projection.

DTR `tau`, LF `tau`, and LF `microstepAdvance` disappear. Metric-time
advancement and consumption remain observable.
-/
theorem DirectLFDetailedWeakLabelTraceCorresponds.observableProjection
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    (hTrace :
      DirectLFDetailedWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    DirectLFDetailedObservableTraceCorresponds
      (DTR.detailedObservableTrace
        sourceLabels)
      (LF.detailedObservableTrace
        targetLabels) := by

  induction hTrace with

  | nil =>
      exact
        DirectLFDetailedObservableTraceCorresponds.nil

  | cons head tail inductionHypothesis =>
      cases head with

      | tau =>
          simpa using
            inductionHypothesis

      | microstep before after =>
          simpa using
            inductionHypothesis

      | timeAdvance beforeTime afterTime =>
          simpa using
            DirectLFDetailedObservableTraceCorresponds.cons
              (DirectLFDetailedObservableCorresponds.timeAdvance
                beforeTime
                afterTime)
              inductionHypothesis

      | consume hOccurrence hReaction =>
          simpa using
            DirectLFDetailedObservableTraceCorresponds.cons
              (DirectLFDetailedObservableCorresponds.consume
                hOccurrence.actionName
                hOccurrence.logicalTime)
              inductionHypothesis

/--
Observable-enhanced conditional finite forward correspondence for exact
DirectLF source executions.
-/
theorem directLFDetailedSteps_forward_observable_of_compatible
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
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      DirectLFDetailedForwardStepsCompatible
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
        DirectLFDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        DirectLFDetailedRuntimeStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧
        DirectLFDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) := by

  rcases
      directLFDetailedSteps_forward_of_compatible
        hSourceSteps
        hStates
        hCompatible
    with
      ⟨targetLabels,
       targetAfter,
       hTargetSteps,
       hLabels,
       hFinalStates⟩

  exact
    ⟨targetLabels,
     targetAfter,
     hTargetSteps,
     hLabels,
     hFinalStates,
     hLabels.observableProjection⟩

/--
Observable-enhanced conditional finite backward correspondence for exact
generated-LF DirectLF executions.
-/
theorem directLFDetailedSteps_backward_observable_of_compatible
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
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      DirectLFDetailedBackwardStepsCompatible
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
        DirectLFDetailedWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        DirectLFDetailedRuntimeStateCorresponds
          messageServers
          sourceAfter
          targetAfter ∧
        DirectLFDetailedObservableTraceCorresponds
          (DTR.detailedObservableTrace
            sourceLabels)
          (LF.detailedObservableTrace
            targetLabels) := by

  rcases
      directLFDetailedSteps_backward_of_compatible
        hTargetSteps
        hStates
        hCompatible
    with
      ⟨sourceLabels,
       sourceAfter,
       hSourceSteps,
       hLabels,
       hFinalStates⟩

  exact
    ⟨sourceLabels,
     sourceAfter,
     hSourceSteps,
     hLabels,
     hFinalStates,
     hLabels.observableProjection⟩

end Correctness
end Relico
