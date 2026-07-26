import Relico.DTR.DetailedWeakExecution
import Relico.LF.DetailedWeakExecution
import Relico.Correctness.DetailedPhaseWeakBisimulation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between one paper-level detailed DTR observable and one
paper-level generated-LF observable.
-/
inductive ConcreteDetailedObservableCorresponds :
    DTR.DetailedMultiStoreObservable →
    LF.DetailedMultiStoreObservable →
    Prop where

  | timeAdvance
      {sourceBefore sourceAfter : LogicalTime}
      {targetBefore targetAfter : LogicalTime}
      (beforeTime :
        targetBefore =
          sourceBefore)
      (afterTime :
        targetAfter =
          sourceAfter) :
      ConcreteDetailedObservableCorresponds
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
      ConcreteDetailedObservableCorresponds
        (.consume
          sourceName
          sourceTime)
        (.consume
          targetName
          targetTime)

/--
Correspondence between optional observable projections of two detailed
labels. Internal labels correspond through the `none` constructor.
-/
inductive ConcreteDetailedObservableOptionCorresponds :
    Option DTR.DetailedMultiStoreObservable →
    Option LF.DetailedMultiStoreObservable →
    Prop where

  | none :
      ConcreteDetailedObservableOptionCorresponds
        none
        none

  | some
      {sourceObservable :
        DTR.DetailedMultiStoreObservable}
      {targetObservable :
        LF.DetailedMultiStoreObservable}
      (observable :
        ConcreteDetailedObservableCorresponds
          sourceObservable
          targetObservable) :
      ConcreteDetailedObservableOptionCorresponds
        (some sourceObservable)
        (some targetObservable)

/--
Concrete detailed label correspondence preserves optional observable
projection.
-/
theorem ConcreteDetailedLabelCorresponds.observableOption
    {sourceLabel : DTR.DetailedMultiStoreLabel}
    {targetLabel : LF.DetailedMultiStoreLabel}
    (hLabels :
      ConcreteDetailedLabelCorresponds
        sourceLabel
        targetLabel) :
    ConcreteDetailedObservableOptionCorresponds
      sourceLabel.toObservable
      targetLabel.toObservable := by

  cases hLabels with

  | tau =>
      exact
        ConcreteDetailedObservableOptionCorresponds.none

  | microstep before after =>
      exact
        ConcreteDetailedObservableOptionCorresponds.none

  | timeAdvance beforeTime afterTime =>
      exact
        ConcreteDetailedObservableOptionCorresponds.some
          (ConcreteDetailedObservableCorresponds.timeAdvance
            beforeTime
            afterTime)

  | consume hOccurrence hReaction =>
      exact
        ConcreteDetailedObservableOptionCorresponds.some
          (ConcreteDetailedObservableCorresponds.consume
            hOccurrence.actionName
            hOccurrence.logicalTime)

/--
Pointwise correspondence between finite sequences of detailed weak labels.
-/
inductive ConcreteDetailedWeakLabelTraceCorresponds :
    List DTR.DetailedMultiStoreLabel →
    List LF.DetailedMultiStoreLabel →
    Prop where

  | nil :
      ConcreteDetailedWeakLabelTraceCorresponds
        []
        []

  | cons
      {sourceLabel : DTR.DetailedMultiStoreLabel}
      {targetLabel : LF.DetailedMultiStoreLabel}
      {sourceRemaining :
        List DTR.DetailedMultiStoreLabel}
      {targetRemaining :
        List LF.DetailedMultiStoreLabel}
      (head :
        ConcreteDetailedLabelCorresponds
          sourceLabel
          targetLabel)
      (tail :
        ConcreteDetailedWeakLabelTraceCorresponds
          sourceRemaining
          targetRemaining) :
      ConcreteDetailedWeakLabelTraceCorresponds
        (sourceLabel :: sourceRemaining)
        (targetLabel :: targetRemaining)

namespace ConcreteDetailedWeakLabelTraceCorresponds

/--
Pointwise detailed weak-label correspondence composes over concatenation.
-/
theorem append
    {sourceLeft sourceRight :
      List DTR.DetailedMultiStoreLabel}
    {targetLeft targetRight :
      List LF.DetailedMultiStoreLabel}
    (left :
      ConcreteDetailedWeakLabelTraceCorresponds
        sourceLeft
        targetLeft)
    (right :
      ConcreteDetailedWeakLabelTraceCorresponds
        sourceRight
        targetRight) :
    ConcreteDetailedWeakLabelTraceCorresponds
      (sourceLeft ++ sourceRight)
      (targetLeft ++ targetRight) := by

  induction left with

  | nil =>
      simpa using right

  | cons head tail inductionHypothesis =>
      exact
        ConcreteDetailedWeakLabelTraceCorresponds.cons
          head
          inductionHypothesis

end ConcreteDetailedWeakLabelTraceCorresponds

/--
Pointwise correspondence between finite paper-level observable traces.
-/
inductive ConcreteDetailedObservableTraceCorresponds :
    List DTR.DetailedMultiStoreObservable →
    List LF.DetailedMultiStoreObservable →
    Prop where

  | nil :
      ConcreteDetailedObservableTraceCorresponds
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
        ConcreteDetailedObservableCorresponds
          sourceObservable
          targetObservable)
      (tail :
        ConcreteDetailedObservableTraceCorresponds
          sourceRemaining
          targetRemaining) :
      ConcreteDetailedObservableTraceCorresponds
        (sourceObservable :: sourceRemaining)
        (targetObservable :: targetRemaining)

namespace ConcreteDetailedObservableTraceCorresponds

/--
Observable trace correspondence composes over concatenation.
-/
theorem append
    {sourceLeft sourceRight :
      List DTR.DetailedMultiStoreObservable}
    {targetLeft targetRight :
      List LF.DetailedMultiStoreObservable}
    (left :
      ConcreteDetailedObservableTraceCorresponds
        sourceLeft
        targetLeft)
    (right :
      ConcreteDetailedObservableTraceCorresponds
        sourceRight
        targetRight) :
    ConcreteDetailedObservableTraceCorresponds
      (sourceLeft ++ sourceRight)
      (targetLeft ++ targetRight) := by

  induction left with

  | nil =>
      simpa using right

  | cons head tail inductionHypothesis =>
      exact
        ConcreteDetailedObservableTraceCorresponds.cons
          head
          inductionHypothesis

end ConcreteDetailedObservableTraceCorresponds

/--
Corresponding finite weak-label traces have corresponding paper-level
observable projections.

DTR `tau`, LF `tau`, and LF `microstepAdvance` disappear from their respective
observable traces. Metric-time advancement and consumption remain related.
-/
theorem ConcreteDetailedWeakLabelTraceCorresponds.observableProjection
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    (hTrace :
      ConcreteDetailedWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    ConcreteDetailedObservableTraceCorresponds
      (DTR.detailedObservableTrace
        sourceLabels)
      (LF.detailedObservableTrace
        targetLabels) := by

  induction hTrace with

  | nil =>
      exact
        ConcreteDetailedObservableTraceCorresponds.nil

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
            ConcreteDetailedObservableTraceCorresponds.cons
              (ConcreteDetailedObservableCorresponds.timeAdvance
                beforeTime
                afterTime)
              inductionHypothesis

      | consume hOccurrence hReaction =>
          simpa using
            ConcreteDetailedObservableTraceCorresponds.cons
              (ConcreteDetailedObservableCorresponds.consume
                hOccurrence.actionName
                hOccurrence.logicalTime)
              inductionHypothesis

end Correctness
end Relico
