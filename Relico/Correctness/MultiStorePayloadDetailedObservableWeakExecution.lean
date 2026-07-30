import Relico.Correctness.MultiStorePayloadDetailedFiniteWeakExecution

set_option autoImplicit false

namespace Relico

namespace DTR

/--
Observable events of the payload-aware multi-store detailed DTR semantics.

Statement execution is silent. Metric-time advancement and payload
consumption are observable.
-/
inductive DetailedMultiStorePayloadObservable where

  | timeAdvance
      (before after : LogicalTime)

  | consume
      (message : PendingMessage)
      (server : MultiStorePayloadMessageServer)

/--
Partial projection from detailed DTR labels to observable events.
-/
def DetailedMultiStorePayloadLabel.toObservable :
    DetailedMultiStorePayloadLabel →
      Option DetailedMultiStorePayloadObservable

  | .tau =>
      none

  | .timeAdvance before after =>
      some
        (.timeAdvance before after)

  | .consume message server =>
      some
        (.consume message server)

/--
Observable trace obtained by removing silent detailed DTR labels.
-/
def detailedMultiStorePayloadObservableTrace
    (labels :
      List DetailedMultiStorePayloadLabel) :
    List DetailedMultiStorePayloadObservable :=

  labels.filterMap
    DetailedMultiStorePayloadLabel.toObservable

end DTR

namespace LF

/--
Observable events of the generated payload-aware multi-store LF semantics.

Statement execution and microstep advancement are silent. Metric-time
advancement and payload consumption are observable.
-/
inductive DetailedMultiStorePayloadObservable where

  | timeAdvance
      (before after : LogicalTime)

  | consume
      (action : PendingAction)
      (reaction : MultiStorePayloadReaction)

/--
Partial projection from detailed LF labels to observable events.
-/
def DetailedMultiStorePayloadLabel.toObservable :
    DetailedMultiStorePayloadLabel →
      Option DetailedMultiStorePayloadObservable

  | .tau =>
      none

  | .timeAdvance before after =>
      some
        (.timeAdvance before after)

  | .microstepAdvance _before _after =>
      none

  | .consume action reaction =>
      some
        (.consume action reaction)

/--
Observable trace obtained by removing silent detailed LF labels.
-/
def detailedMultiStorePayloadObservableTrace
    (labels :
      List DetailedMultiStorePayloadLabel) :
    List DetailedMultiStorePayloadObservable :=

  labels.filterMap
    DetailedMultiStorePayloadLabel.toObservable

end LF

namespace Correctness

/--
Exact observable-event correspondence for the payload-aware multi-store
detailed semantics.
-/
inductive MultiStorePayloadDetailedObservableCorresponds :
    DTR.DetailedMultiStorePayloadObservable →
      LF.DetailedMultiStorePayloadObservable →
        Prop where

  | timeAdvance
      {sourceBefore sourceAfter :
        LogicalTime}
      {targetBefore targetAfter :
        LogicalTime}
      (hBefore :
        targetBefore = sourceBefore)
      (hAfter :
        targetAfter = sourceAfter) :
      MultiStorePayloadDetailedObservableCorresponds
        (.timeAdvance
          sourceBefore
          sourceAfter)
        (.timeAdvance
          targetBefore
          targetAfter)

  | consume
      {sourceMessage :
        DTR.PendingMessage}
      {sourceServer :
        DTR.MultiStorePayloadMessageServer}
      {targetAction :
        LF.PendingAction}
      {targetReaction :
        LF.MultiStorePayloadReaction}
      (hPending :
        PendingPayloadCorresponds
          sourceMessage
          targetAction)
      (hReaction :
        targetReaction =
          Translation.compileMultiStorePayloadReaction
            sourceServer) :
      MultiStorePayloadDetailedObservableCorresponds
        (.consume
          sourceMessage
          sourceServer)
        (.consume
          targetAction
          targetReaction)

/--
Correspondence for partial observable projections.
-/
inductive MultiStorePayloadDetailedObservableOptionCorresponds :
    Option DTR.DetailedMultiStorePayloadObservable →
      Option LF.DetailedMultiStorePayloadObservable →
        Prop where

  | none :
      MultiStorePayloadDetailedObservableOptionCorresponds
        none
        none

  | some
      {sourceObservable :
        DTR.DetailedMultiStorePayloadObservable}
      {targetObservable :
        LF.DetailedMultiStorePayloadObservable}
      (hObservables :
        MultiStorePayloadDetailedObservableCorresponds
          sourceObservable
          targetObservable) :
      MultiStorePayloadDetailedObservableOptionCorresponds
        (some sourceObservable)
        (some targetObservable)

/--
Pointwise correspondence between projected observable traces.
-/
inductive MultiStorePayloadDetailedObservableTraceCorresponds :
    List DTR.DetailedMultiStorePayloadObservable →
      List LF.DetailedMultiStorePayloadObservable →
        Prop where

  | nil :
      MultiStorePayloadDetailedObservableTraceCorresponds
        []
        []

  | cons
      {sourceObservable :
        DTR.DetailedMultiStorePayloadObservable}
      {targetObservable :
        LF.DetailedMultiStorePayloadObservable}
      {sourceRemaining :
        List DTR.DetailedMultiStorePayloadObservable}
      {targetRemaining :
        List LF.DetailedMultiStorePayloadObservable}
      (hHead :
        MultiStorePayloadDetailedObservableCorresponds
          sourceObservable
          targetObservable)
      (hTail :
        MultiStorePayloadDetailedObservableTraceCorresponds
          sourceRemaining
          targetRemaining) :
      MultiStorePayloadDetailedObservableTraceCorresponds
        (sourceObservable :: sourceRemaining)
        (targetObservable :: targetRemaining)

/--
A corresponding pair of detailed labels has corresponding partial
observable projections.
-/
theorem MultiStorePayloadDetailedLabelCorresponds.observableOption
    {sourceLabel :
      DTR.DetailedMultiStorePayloadLabel}
    {targetLabel :
      LF.DetailedMultiStorePayloadLabel}
    (hLabels :
      MultiStorePayloadDetailedLabelCorresponds
        sourceLabel
        targetLabel) :
    MultiStorePayloadDetailedObservableOptionCorresponds
      sourceLabel.toObservable
      targetLabel.toObservable := by

  cases hLabels with

  | tau =>
      exact
        MultiStorePayloadDetailedObservableOptionCorresponds.none

  | microstep before after =>
      exact
        MultiStorePayloadDetailedObservableOptionCorresponds.none

  | timeAdvance hBefore hAfter =>
      exact
        MultiStorePayloadDetailedObservableOptionCorresponds.some
          (MultiStorePayloadDetailedObservableCorresponds.timeAdvance
            hBefore
            hAfter)

  | consume hPending hReaction =>
      exact
        MultiStorePayloadDetailedObservableOptionCorresponds.some
          (MultiStorePayloadDetailedObservableCorresponds.consume
            hPending
            hReaction)

/--
Exact weak-label trace correspondence implies exact correspondence of the
filtered observable traces.
-/
theorem
    MultiStorePayloadDetailedWeakLabelTraceCorresponds.observableProjection
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    {targetLabels :
      List LF.DetailedMultiStorePayloadLabel}
    (hTrace :
      MultiStorePayloadDetailedWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    MultiStorePayloadDetailedObservableTraceCorresponds
      (DTR.detailedMultiStorePayloadObservableTrace
        sourceLabels)
      (LF.detailedMultiStorePayloadObservableTrace
        targetLabels) := by

  induction hTrace with

  | nil =>
      exact
        MultiStorePayloadDetailedObservableTraceCorresponds.nil

  | cons hLabels hRemaining inductionHypothesis =>
      cases hLabels with

      | tau =>
          simpa
            [ DTR.detailedMultiStorePayloadObservableTrace,
              LF.detailedMultiStorePayloadObservableTrace,
              DTR.DetailedMultiStorePayloadLabel.toObservable,
              LF.DetailedMultiStorePayloadLabel.toObservable ]
            using inductionHypothesis

      | microstep before after =>
          simpa
            [ DTR.detailedMultiStorePayloadObservableTrace,
              LF.detailedMultiStorePayloadObservableTrace,
              DTR.DetailedMultiStorePayloadLabel.toObservable,
              LF.DetailedMultiStorePayloadLabel.toObservable ]
            using inductionHypothesis

      | timeAdvance hBefore hAfter =>
          simpa
            [ DTR.detailedMultiStorePayloadObservableTrace,
              LF.detailedMultiStorePayloadObservableTrace,
              DTR.DetailedMultiStorePayloadLabel.toObservable,
              LF.DetailedMultiStorePayloadLabel.toObservable ]
            using
              MultiStorePayloadDetailedObservableTraceCorresponds.cons
                (MultiStorePayloadDetailedObservableCorresponds.timeAdvance
                  hBefore
                  hAfter)
                inductionHypothesis

      | consume hPending hReaction =>
          simpa
            [ DTR.detailedMultiStorePayloadObservableTrace,
              LF.detailedMultiStorePayloadObservableTrace,
              DTR.DetailedMultiStorePayloadLabel.toObservable,
              LF.DetailedMultiStorePayloadLabel.toObservable ]
            using
              MultiStorePayloadDetailedObservableTraceCorresponds.cons
                (MultiStorePayloadDetailedObservableCorresponds.consume
                  hPending
                  hReaction)
                inductionHypothesis

/--
Corresponding observable traces have equal lengths.
-/
theorem
    MultiStorePayloadDetailedObservableTraceCorresponds.length_eq
    {sourceObservables :
      List DTR.DetailedMultiStorePayloadObservable}
    {targetObservables :
      List LF.DetailedMultiStorePayloadObservable}
    (hTrace :
      MultiStorePayloadDetailedObservableTraceCorresponds
        sourceObservables
        targetObservables) :
    sourceObservables.length =
      targetObservables.length := by

  induction hTrace with

  | nil =>
      rfl

  | cons hHead hTail inductionHypothesis =>
      simp only [List.length_cons]
      exact congrArg Nat.succ inductionHypothesis

/--
Observable trace correspondence is closed under concatenation.
-/
theorem
    MultiStorePayloadDetailedObservableTraceCorresponds.append
    {sourceLeft sourceRight :
      List DTR.DetailedMultiStorePayloadObservable}
    {targetLeft targetRight :
      List LF.DetailedMultiStorePayloadObservable}
    (left :
      MultiStorePayloadDetailedObservableTraceCorresponds
        sourceLeft
        targetLeft)
    (right :
      MultiStorePayloadDetailedObservableTraceCorresponds
        sourceRight
        targetRight) :
    MultiStorePayloadDetailedObservableTraceCorresponds
      (sourceLeft ++ sourceRight)
      (targetLeft ++ targetRight) := by

  induction left with

  | nil =>
      simpa using right

  | cons hHead hTail inductionHypothesis =>
      simp only [List.cons_append]

      exact
        MultiStorePayloadDetailedObservableTraceCorresponds.cons
          hHead
          inductionHypothesis

/--
Conditional forward observable-trace correspondence for a finite
payload-aware multi-store DTR execution.

The theorem reuses the published C5B finite weak-execution theorem and
projects its exact weak-label trace to observable events.
-/
theorem multiStorePayloadDetailedSteps_forward_observable_of_compatible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStorePayloadState messageServers}
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    {targetBefore :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
    (hSourceSteps :
      DTR.DetailedMultiStorePayloadSteps
        messageServers
        sourceBefore
        sourceLabels
        sourceAfter)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      MultiStorePayloadDetailedForwardStepsCompatible
        messageServers
        hSourceSteps
        targetBefore) :
    ∃
      targetLabels
      targetAfter,
      LF.DetailedMultiStorePayloadWeakSteps
          (Translation.compileMultiStorePayloadMessageReactions
            messageServers)
          targetBefore
          targetLabels
          targetAfter ∧
        MultiStorePayloadDetailedWeakLabelTraceCorresponds
            sourceLabels
            targetLabels ∧
          MultiStorePayloadDetailedRuntimeStateCorresponds
              messageServers
              sourceAfter
              targetAfter ∧
            MultiStorePayloadDetailedObservableTraceCorresponds
              (DTR.detailedMultiStorePayloadObservableTrace
                sourceLabels)
              (LF.detailedMultiStorePayloadObservableTrace
                targetLabels) := by

  rcases
    multiStorePayloadDetailedSteps_forward_of_compatible
      hSourceSteps
      hStates
      hCompatible
    with
    ⟨ targetLabels,
      targetAfter,
      hTargetSteps,
      hLabelTrace,
      hFinalStates ⟩

  exact
    ⟨ targetLabels,
      targetAfter,
      hTargetSteps,
      hLabelTrace,
      hFinalStates,
      hLabelTrace.observableProjection ⟩

/--
Conditional backward observable-trace correspondence for a finite
payload-aware generated-LF execution.

The theorem reuses the published C5B backward finite theorem and projects
its exact weak-label trace to observable events.
-/
theorem multiStorePayloadDetailedSteps_backward_observable_of_compatible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore :
      DTR.DetailedMultiStorePayloadState messageServers}
    {targetBefore targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
    {targetLabels :
      List LF.DetailedMultiStorePayloadLabel}
    (hTargetSteps :
      LF.DetailedMultiStorePayloadSteps
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        targetLabels
        targetAfter)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      MultiStorePayloadDetailedBackwardStepsCompatible
        messageServers
        sourceBefore
        hTargetSteps) :
    ∃
      sourceLabels
      sourceAfter,
      DTR.DetailedMultiStorePayloadWeakSteps
          messageServers
          sourceBefore
          sourceLabels
          sourceAfter ∧
        MultiStorePayloadDetailedWeakLabelTraceCorresponds
            sourceLabels
            targetLabels ∧
          MultiStorePayloadDetailedRuntimeStateCorresponds
              messageServers
              sourceAfter
              targetAfter ∧
            MultiStorePayloadDetailedObservableTraceCorresponds
              (DTR.detailedMultiStorePayloadObservableTrace
                sourceLabels)
              (LF.detailedMultiStorePayloadObservableTrace
                targetLabels) := by

  rcases
    multiStorePayloadDetailedSteps_backward_of_compatible
      hTargetSteps
      hStates
      hCompatible
    with
    ⟨ sourceLabels,
      sourceAfter,
      hSourceSteps,
      hLabelTrace,
      hFinalStates ⟩

  exact
    ⟨ sourceLabels,
      sourceAfter,
      hSourceSteps,
      hLabelTrace,
      hFinalStates,
      hLabelTrace.observableProjection ⟩


end Correctness
end Relico
