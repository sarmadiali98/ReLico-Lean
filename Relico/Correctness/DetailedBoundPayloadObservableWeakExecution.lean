import Relico.Correctness.DetailedBoundPayloadFiniteWeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between one paper-level payload-aware source observable and one
paper-level generated-LF observable.

Consumption preserves the generated action name, logical occurrence time, and
complete ordered payload.
-/
inductive DetailedBoundPayloadObservableCorresponds :
    DTR.DetailedBoundPayloadObservable →
    LF.DetailedBoundPayloadObservable →
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
      DetailedBoundPayloadObservableCorresponds
        (.timeAdvance
          sourceBefore
          sourceAfter)
        (.timeAdvance
          targetBefore
          targetAfter)

  | consume
      {sourceName : MsgName}
      {sourceTime : LogicalTime}
      {sourcePayload : Payload}
      {targetName : ActionName}
      {targetTime : LogicalTime}
      {targetPayload : Payload}
      (actionName :
        targetName =
          Translation.actionNameFor
            sourceName)
      (logicalTime :
        targetTime =
          sourceTime)
      (payload :
        targetPayload =
          sourcePayload) :
      DetailedBoundPayloadObservableCorresponds
        (.consume
          sourceName
          sourceTime
          sourcePayload)
        (.consume
          targetName
          targetTime
          targetPayload)

/--
Correspondence between the optional observable projections of two detailed
bound-payload labels.

Internal source `tau`, target `tau`, and generated-LF microstep administration
all project to `none`.
-/
inductive DetailedBoundPayloadObservableOptionCorresponds :
    Option DTR.DetailedBoundPayloadObservable →
    Option LF.DetailedBoundPayloadObservable →
    Prop where

  | none :
      DetailedBoundPayloadObservableOptionCorresponds
        none
        none

  | some
      {sourceObservable :
        DTR.DetailedBoundPayloadObservable}
      {targetObservable :
        LF.DetailedBoundPayloadObservable}
      (observable :
        DetailedBoundPayloadObservableCorresponds
          sourceObservable
          targetObservable) :
      DetailedBoundPayloadObservableOptionCorresponds
        (some sourceObservable)
        (some targetObservable)

/--
Detailed payload-aware label correspondence preserves optional observable
projection.
-/
theorem DetailedBoundPayloadLabelCorresponds.observableOption
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {targetLabel :
      LF.DetailedBoundPayloadLabel}
    (hLabels :
      DetailedBoundPayloadLabelCorresponds
        sourceLabel
        targetLabel) :
    DetailedBoundPayloadObservableOptionCorresponds
      sourceLabel.toObservable
      targetLabel.toObservable := by

  cases hLabels with

  | tau =>
      exact
        DetailedBoundPayloadObservableOptionCorresponds.none

  | microstep before after =>
      exact
        DetailedBoundPayloadObservableOptionCorresponds.none

  | timeAdvance beforeTime afterTime =>
      exact
        DetailedBoundPayloadObservableOptionCorresponds.some
          (DetailedBoundPayloadObservableCorresponds.timeAdvance
            beforeTime
            afterTime)

  | consume occurrence =>
      exact
        DetailedBoundPayloadObservableOptionCorresponds.some
          (DetailedBoundPayloadObservableCorresponds.consume
            occurrence.occurrence.actionName
            occurrence.occurrence.logicalTime
            occurrence.payload)

/--
Pointwise correspondence between finite payload-aware paper-level observable
traces.
-/
inductive DetailedBoundPayloadObservableTraceCorresponds :
    List DTR.DetailedBoundPayloadObservable →
    List LF.DetailedBoundPayloadObservable →
    Prop where

  | nil :
      DetailedBoundPayloadObservableTraceCorresponds
        []
        []

  | cons
      {sourceObservable :
        DTR.DetailedBoundPayloadObservable}
      {targetObservable :
        LF.DetailedBoundPayloadObservable}
      {sourceRemaining :
        List DTR.DetailedBoundPayloadObservable}
      {targetRemaining :
        List LF.DetailedBoundPayloadObservable}
      (head :
        DetailedBoundPayloadObservableCorresponds
          sourceObservable
          targetObservable)
      (tail :
        DetailedBoundPayloadObservableTraceCorresponds
          sourceRemaining
          targetRemaining) :
      DetailedBoundPayloadObservableTraceCorresponds
        (sourceObservable :: sourceRemaining)
        (targetObservable :: targetRemaining)

namespace DetailedBoundPayloadObservableTraceCorresponds

/--
Corresponding payload-aware observable traces have equal lengths.
-/
theorem length_eq
    {sourceObservables :
      List DTR.DetailedBoundPayloadObservable}
    {targetObservables :
      List LF.DetailedBoundPayloadObservable}
    (hTrace :
      DetailedBoundPayloadObservableTraceCorresponds
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
Payload-aware observable trace correspondence composes over concatenation.
-/
theorem append
    {sourceLeft sourceRight :
      List DTR.DetailedBoundPayloadObservable}
    {targetLeft targetRight :
      List LF.DetailedBoundPayloadObservable}
    (left :
      DetailedBoundPayloadObservableTraceCorresponds
        sourceLeft
        targetLeft)
    (right :
      DetailedBoundPayloadObservableTraceCorresponds
        sourceRight
        targetRight) :
    DetailedBoundPayloadObservableTraceCorresponds
      (sourceLeft ++ sourceRight)
      (targetLeft ++ targetRight) := by

  induction left with

  | nil =>
      simpa using right

  | cons head tail inductionHypothesis =>
      exact
        DetailedBoundPayloadObservableTraceCorresponds.cons
          head
          inductionHypothesis

end DetailedBoundPayloadObservableTraceCorresponds

/--
Pointwise detailed bound-payload weak-label correspondence preserves the
paper-level observable projection.

Source `tau`, target `tau`, and generated-LF `microstepAdvance` disappear.
Metric-time advancement and payload-bearing consumption remain observable.
-/
theorem DetailedBoundPayloadWeakLabelTraceCorresponds.observableProjection
    {sourceLabels :
      List DTR.DetailedBoundPayloadLabel}
    {targetLabels :
      List LF.DetailedBoundPayloadLabel}
    (hTrace :
      DetailedBoundPayloadWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    DetailedBoundPayloadObservableTraceCorresponds
      (DTR.detailedBoundPayloadObservableTrace
        sourceLabels)
      (LF.detailedBoundPayloadObservableTrace
        targetLabels) := by

  induction hTrace with

  | nil =>
      exact
        DetailedBoundPayloadObservableTraceCorresponds.nil

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
            DetailedBoundPayloadObservableTraceCorresponds.cons
              (DetailedBoundPayloadObservableCorresponds.timeAdvance
                beforeTime
                afterTime)
              inductionHypothesis

      | consume occurrence =>
          simpa using
            DetailedBoundPayloadObservableTraceCorresponds.cons
              (DetailedBoundPayloadObservableCorresponds.consume
                occurrence.occurrence.actionName
                occurrence.occurrence.logicalTime
                occurrence.payload)
              inductionHypothesis

/--
Observable-enhanced conditional finite forward correspondence for exact
detailed source bound-payload executions.
-/
theorem detailedBoundPayloadSteps_forward_observable_of_compatible
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState server}
    {sourceLabels :
      List DTR.DetailedBoundPayloadLabel}
    {targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    (hSourceSteps :
      DTR.DetailedBoundPayloadSteps
        server
        sourceBefore
        sourceLabels
        sourceAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hCompatible :
      DetailedBoundPayloadForwardStepsCompatible
        server
        hSourceSteps
        targetBefore) :
    ∃ targetLabels targetAfter,
      LF.DetailedBoundPayloadWeakSteps
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          targetLabels
          targetAfter ∧
        DetailedBoundPayloadWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧
        DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            sourceLabels)
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) := by

  rcases
      detailedBoundPayloadSteps_forward_of_compatible
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
detailed generated-LF bound-payload executions.
-/
theorem detailedBoundPayloadSteps_backward_observable_of_compatible
    {server : DTR.PayloadMessageServer}
    {sourceBefore :
      DTR.DetailedBoundPayloadState server}
    {targetBefore targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    {targetLabels :
      List LF.DetailedBoundPayloadLabel}
    (hTargetSteps :
      LF.DetailedBoundPayloadSteps
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        targetLabels
        targetAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hCompatible :
      DetailedBoundPayloadBackwardStepsCompatible
        server
        sourceBefore
        hTargetSteps) :
    ∃ sourceLabels sourceAfter,
      DTR.DetailedBoundPayloadWeakSteps
          server
          sourceBefore
          sourceLabels
          sourceAfter ∧
        DetailedBoundPayloadWeakLabelTraceCorresponds
          sourceLabels
          targetLabels ∧
        DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧
        DetailedBoundPayloadObservableTraceCorresponds
          (DTR.detailedBoundPayloadObservableTrace
            sourceLabels)
          (LF.detailedBoundPayloadObservableTrace
            targetLabels) := by

  rcases
      detailedBoundPayloadSteps_backward_of_compatible
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
