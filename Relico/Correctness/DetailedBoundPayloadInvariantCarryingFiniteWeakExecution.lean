import Relico.Correctness.DetailedBoundPayloadInvariantMatches
import Relico.Correctness.DetailedBoundPayloadObservableWeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
A selected generated-LF weak match carrying every property required to recurse
on the source destination.

The package includes endpoint state correspondence, both phase-aware runtime
invariants, and canonical forward phase alignment.
-/
def DetailedBoundPayloadForwardInvariantMatch
    (server : DTR.PayloadMessageServer)
    (sourceLabel :
      DTR.DetailedBoundPayloadLabel)
    (sourceAfter :
      DTR.DetailedBoundPayloadState
        server)
    (targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)) :
    Prop :=

  ∃ targetLabel :
      LF.DetailedBoundPayloadLabel,

    ∃ targetAfter :
        LF.DetailedBoundPayloadState
          (Translation.compilePayloadMessageServer
            server),

      LF.DetailedBoundPayloadWeakStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          targetLabel
          targetAfter ∧

        DetailedBoundPayloadLabelCorresponds
          sourceLabel
          targetLabel ∧

        DetailedBoundPayloadStateCorresponds
          server
          sourceAfter
          targetAfter ∧

        DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter

/--
One exact source detailed transition preserves the phase-aware source timing
invariant when the declared payload message-server body satisfies the internal
positive-delay restriction.
-/
theorem detailedBoundPayloadSourceRuntimeInvariant_preserved
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    (hSourceStep :
      DTR.DetailedBoundPayloadStep
        server
        sourceBefore
        sourceLabel
        sourceAfter)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body)
    (hSourceInvariant :
      DetailedBoundPayloadSourceRuntimeInvariant
        server
        sourceBefore) :
    DetailedBoundPayloadSourceRuntimeInvariant
      server
      sourceAfter := by

  cases hSourceStep with

  | statement hStatement =>
      exact
        detailedBoundPayloadSourceRuntimeInvariant_stable.mpr
          (boundPayloadStep_preserves_priorityTimingWellFormed
            hStatement
            (detailedBoundPayloadSourceRuntimeInvariant_stable.mp
              hSourceInvariant))

  | timeAdvance hSourceDispatch hFuture =>
      exact
        detailedBoundPayloadSourceRuntimeInvariant_dispatchReady.mpr
          (boundPayloadDispatch_establishes_priorityTimingWellFormed
            hSourceDispatch
            hServerTiming)

  | consumeReady hSourceDispatch =>
      exact
        detailedBoundPayloadSourceRuntimeInvariant_stable.mpr
          (detailedBoundPayloadSourceRuntimeInvariant_dispatchReady.mp
            hSourceInvariant)

  | consumeNow hSourceDispatch hSameTime =>
      exact
        detailedBoundPayloadSourceRuntimeInvariant_stable.mpr
          (boundPayloadDispatch_establishes_priorityTimingWellFormed
            hSourceDispatch
            hServerTiming)

/--
Construct the canonical invariant-carrying generated-LF weak match for one
exact detailed source transition.
-/
theorem detailedBoundPayloadForwardInvariantMatch
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    (hSourceStep :
      DTR.DetailedBoundPayloadStep
        server
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hSourceInvariant :
      DetailedBoundPayloadSourceRuntimeInvariant
        server
        sourceBefore)
    (hTargetInvariant :
      DetailedBoundPayloadTargetRuntimeInvariant
        server
        targetBefore)
    (hCanonical :
      DetailedBoundPayloadForwardCanonicalPhase
        sourceBefore
        targetBefore)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
    DetailedBoundPayloadForwardInvariantMatch
      server
      sourceLabel
      sourceAfter
      targetBefore := by

  cases hSourceStep with

  | statement hSourceStatement =>
      rename_i
        sourceBeforeState
        sourceAfterState
        sourceStatementLabel

      cases hStates with

      | stable hStable =>
          rename_i targetBeforeState

          have hSourceTiming :=
            detailedBoundPayloadSourceRuntimeInvariant_stable.mp
              hSourceInvariant

          have hTargetRuntime :=
            detailedBoundPayloadTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          rcases
              boundPayloadStep_forward_preserves_runtimeInvariants
                hSourceStatement
                hStable
                hSourceTiming
                hTargetRuntime
            with
              ⟨targetStatementLabel,
               targetAfterState,
               hTargetStatement,
               hStatementLabels,
               hFinalStates,
               hFinalSourceTiming,
               hFinalTargetRuntime⟩

          exact
            ⟨LF.DetailedBoundPayloadLabel.tau,
             LF.DetailedBoundPayloadState.stable
               targetAfterState,
             LF.detailedBoundPayloadStatement_is_weak
               hTargetStatement,
             DetailedBoundPayloadLabelCorresponds.tau,
             DetailedBoundPayloadStateCorresponds.stable
               hFinalStates,
             detailedBoundPayloadSourceRuntimeInvariant_stable.mpr
               hFinalSourceTiming,
             detailedBoundPayloadTargetRuntimeInvariant_stable.mpr
               hFinalTargetRuntime,
             detailedBoundPayloadForwardCanonicalPhase_stable⟩

      | sameTimeMicrostepAhead
          sourceDispatch
          hSourceSameTime
          hTargetSameTime
          hLaterMicrostep
          hWitness =>

          simp [
            DetailedBoundPayloadForwardCanonicalPhase
          ] at hCanonical

  | timeAdvance hSourceDispatch hSourceFuture =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage

      cases hStates with

      | stable hStable =>
          rename_i targetBeforeState

          have hTargetRuntime :=
            detailedBoundPayloadTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          rcases
              boundPayloadDispatch_forward_preserves_runtimeInvariants
                hSourceDispatch
                hStable
                hServerTiming
                hTargetRuntime
            with
              ⟨selectedAction,
               targetAfterState,
               hTargetDispatch,
               hSelectedOccurrence,
               hAfterStates,
               hFinalSourceTiming,
               hFinalTargetRuntime⟩

          have hTargetFuture :
              targetBeforeState.currentTag.time <
                targetAfterState.currentTag.time := by

            calc
              targetBeforeState.currentTag.time =
                  sourceBeforeState.currentTime :=
                hStable.currentTime

              _ <
                  sourceAfterState.currentTime :=
                hSourceFuture

              _ =
                  targetAfterState.currentTag.time :=
                hAfterStates.currentTime.symm

          have hWitness :
              DetailedBoundPayloadDispatchWitnessCorresponds
                server
                sourceBeforeState
                selectedMessage
                sourceAfterState
                targetBeforeState
                selectedAction
                targetAfterState := {
            beforeState :=
              hStable

            selectedOccurrence :=
              hSelectedOccurrence

            afterState :=
              hAfterStates
          }

          have hTargetDetailedStep :
              LF.DetailedBoundPayloadStep
                (Translation.compilePayloadMessageServer
                  server)
                (.stable targetBeforeState)
                (.timeAdvance
                  targetBeforeState.currentTag.time
                  targetAfterState.currentTag.time)
                (.afterTime
                  targetBeforeState
                  selectedAction
                  targetAfterState
                  hTargetDispatch) :=

            LF.DetailedBoundPayloadStep.timeAdvance
              hTargetDispatch
              hTargetFuture

          exact
            ⟨LF.DetailedBoundPayloadLabel.timeAdvance
                targetBeforeState.currentTag.time
                targetAfterState.currentTag.time,
             LF.DetailedBoundPayloadState.afterTime
               targetBeforeState
               selectedAction
               targetAfterState
               hTargetDispatch,
             LF.detailedBoundPayloadTimeAdvance_is_weak
               hTargetDetailedStep,
             DetailedBoundPayloadLabelCorresponds.timeAdvance
               hStable.currentTime
               hAfterStates.currentTime,
             DetailedBoundPayloadStateCorresponds.futureAfterTime
               hSourceFuture
               hTargetFuture
               hWitness,
             detailedBoundPayloadSourceRuntimeInvariant_dispatchReady.mpr
               hFinalSourceTiming,
             detailedBoundPayloadTargetRuntimeInvariant_afterTime.mpr
               hFinalTargetRuntime,
             detailedBoundPayloadForwardCanonicalPhase_futureAfterTime⟩

      | sameTimeMicrostepAhead
          sourceDispatch
          hSourceSameTime
          hTargetSameTime
          hLaterMicrostep
          hWitness =>

          simp [
            DetailedBoundPayloadForwardCanonicalPhase
          ] at hCanonical

  | consumeReady hSourceDispatch =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage

      cases targetBefore with

      | stable targetBeforeState =>
          cases hStates

      | afterTime
          targetBeforeState
          selectedAction
          targetAfterState
          targetDispatch =>

          cases hStates with

          | futureAfterTime
              hSourceFuture
              hTargetFuture
              hWitness =>

              have hFinalSourceTiming :=
                detailedBoundPayloadSourceRuntimeInvariant_dispatchReady.mp
                  hSourceInvariant

              have hFinalTargetRuntime :=
                detailedBoundPayloadTargetRuntimeInvariant_afterTime.mp
                  hTargetInvariant

              rcases
                  Nat.eq_zero_or_pos
                    targetAfterState.currentTag.microstep
                with
                  hZero |
                  hPositive

              · have hTargetDetailedStep :
                    LF.DetailedBoundPayloadStep
                      (Translation.compilePayloadMessageServer
                        server)
                      (.afterTime
                        targetBeforeState
                        selectedAction
                        targetAfterState
                        targetDispatch)
                      (.consume selectedAction)
                      (.stable targetAfterState) :=

                  LF.DetailedBoundPayloadStep.consumeAfterTimeZero
                    targetDispatch
                    hZero

                exact
                  ⟨LF.DetailedBoundPayloadLabel.consume
                      selectedAction,
                   LF.DetailedBoundPayloadState.stable
                     targetAfterState,
                   LF.detailedBoundPayloadConsume_is_weak
                     hTargetDetailedStep,
                   DetailedBoundPayloadLabelCorresponds.consume
                     hWitness.selectedOccurrence,
                   DetailedBoundPayloadStateCorresponds.stable
                     hWitness.afterState,
                   detailedBoundPayloadSourceRuntimeInvariant_stable.mpr
                     hFinalSourceTiming,
                   detailedBoundPayloadTargetRuntimeInvariant_stable.mpr
                     hFinalTargetRuntime,
                   detailedBoundPayloadForwardCanonicalPhase_stable⟩

              · have hMicrostepDetailedStep :
                    LF.DetailedBoundPayloadStep
                      (Translation.compilePayloadMessageServer
                        server)
                      (.afterTime
                        targetBeforeState
                        selectedAction
                        targetAfterState
                        targetDispatch)
                      (.microstepAdvance
                        {
                          time :=
                            targetAfterState.currentTag.time

                          microstep :=
                            0
                        }
                        targetAfterState.currentTag)
                      (.dispatchReady
                        targetBeforeState
                        selectedAction
                        targetAfterState
                        targetDispatch) :=

                  LF.DetailedBoundPayloadStep.microstepAfterTime
                    targetDispatch
                    hPositive

                have hInternalPrefix :
                    LF.DetailedBoundPayloadTauSteps
                      (Translation.compilePayloadMessageServer
                        server)
                      (.afterTime
                        targetBeforeState
                        selectedAction
                        targetAfterState
                        targetDispatch)
                      (.dispatchReady
                        targetBeforeState
                        selectedAction
                        targetAfterState
                        targetDispatch) :=

                  LF.detailedBoundPayloadMicrostep_to_tauSteps
                    hMicrostepDetailedStep

                have hConsumeDetailedStep :
                    LF.DetailedBoundPayloadStep
                      (Translation.compilePayloadMessageServer
                        server)
                      (.dispatchReady
                        targetBeforeState
                        selectedAction
                        targetAfterState
                        targetDispatch)
                      (.consume selectedAction)
                      (.stable targetAfterState) :=

                  LF.DetailedBoundPayloadStep.consumeReady
                    targetDispatch

                have hTargetWeakStep :
                    LF.DetailedBoundPayloadWeakStep
                      (Translation.compilePayloadMessageServer
                        server)
                      (.afterTime
                        targetBeforeState
                        selectedAction
                        targetAfterState
                        targetDispatch)
                      (.consume selectedAction)
                      (.stable targetAfterState) := by

                  exact
                    Common.WeakStep.visible
                      (LF.detailedBoundPayload_consume_visible
                        selectedAction)
                      hInternalPrefix
                      hConsumeDetailedStep
                      (Common.TauSteps.refl
                        (LF.DetailedBoundPayloadState.stable
                          targetAfterState))

                exact
                  ⟨LF.DetailedBoundPayloadLabel.consume
                      selectedAction,
                   LF.DetailedBoundPayloadState.stable
                     targetAfterState,
                   hTargetWeakStep,
                   DetailedBoundPayloadLabelCorresponds.consume
                     hWitness.selectedOccurrence,
                   DetailedBoundPayloadStateCorresponds.stable
                     hWitness.afterState,
                   detailedBoundPayloadSourceRuntimeInvariant_stable.mpr
                     hFinalSourceTiming,
                   detailedBoundPayloadTargetRuntimeInvariant_stable.mpr
                     hFinalTargetRuntime,
                   detailedBoundPayloadForwardCanonicalPhase_stable⟩

      | dispatchReady
          targetBeforeState
          selectedAction
          targetAfterState
          targetDispatch =>

          cases hStates with

          | futureReady
              hSourceFuture
              hTargetFuture
              hPositiveMicrostep
              hWitness =>

              have hFinalSourceTiming :=
                detailedBoundPayloadSourceRuntimeInvariant_dispatchReady.mp
                  hSourceInvariant

              have hFinalTargetRuntime :=
                detailedBoundPayloadTargetRuntimeInvariant_dispatchReady.mp
                  hTargetInvariant

              have hTargetDetailedStep :
                  LF.DetailedBoundPayloadStep
                    (Translation.compilePayloadMessageServer
                      server)
                    (.dispatchReady
                      targetBeforeState
                      selectedAction
                      targetAfterState
                      targetDispatch)
                    (.consume selectedAction)
                    (.stable targetAfterState) :=

                LF.DetailedBoundPayloadStep.consumeReady
                  targetDispatch

              exact
                ⟨LF.DetailedBoundPayloadLabel.consume
                    selectedAction,
                 LF.DetailedBoundPayloadState.stable
                   targetAfterState,
                 LF.detailedBoundPayloadConsume_is_weak
                   hTargetDetailedStep,
                 DetailedBoundPayloadLabelCorresponds.consume
                   hWitness.selectedOccurrence,
                 DetailedBoundPayloadStateCorresponds.stable
                   hWitness.afterState,
                 detailedBoundPayloadSourceRuntimeInvariant_stable.mpr
                   hFinalSourceTiming,
                 detailedBoundPayloadTargetRuntimeInvariant_stable.mpr
                   hFinalTargetRuntime,
                 detailedBoundPayloadForwardCanonicalPhase_stable⟩

  | consumeNow hSourceDispatch hSourceSameTime =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage

      cases hStates with

      | stable hStable =>
          rename_i targetBeforeState

          have hTargetRuntime :=
            detailedBoundPayloadTargetRuntimeInvariant_stable.mp
              hTargetInvariant

          rcases
              boundPayloadDispatch_forward_preserves_runtimeInvariants
                hSourceDispatch
                hStable
                hServerTiming
                hTargetRuntime
            with
              ⟨selectedAction,
               targetAfterState,
               hTargetDispatch,
               hSelectedOccurrence,
               hAfterStates,
               hFinalSourceTiming,
               hFinalTargetRuntime⟩

          have hSameTargetTime :
              targetBeforeState.currentTag.time =
                targetAfterState.currentTag.time := by

            calc
              targetBeforeState.currentTag.time =
                  sourceBeforeState.currentTime :=
                hStable.currentTime

              _ =
                  sourceAfterState.currentTime :=
                hSourceSameTime

              _ =
                  targetAfterState.currentTag.time :=
                hAfterStates.currentTime.symm

          have hMicrostepOrder :
              targetBeforeState.currentTag.microstep ≤
                targetAfterState.currentTag.microstep :=

            lfBoundPayloadDispatch_microstep_le_of_sameTime
              hTargetDispatch
              hSameTargetTime

          rcases
              Nat.lt_or_eq_of_le
                hMicrostepOrder
            with
              hLaterMicrostep |
              hSameMicrostep

          · have hMicrostepDetailedStep :
                LF.DetailedBoundPayloadStep
                  (Translation.compilePayloadMessageServer
                    server)
                  (.stable targetBeforeState)
                  (.microstepAdvance
                    targetBeforeState.currentTag
                    targetAfterState.currentTag)
                  (.dispatchReady
                    targetBeforeState
                    selectedAction
                    targetAfterState
                    hTargetDispatch) :=

              LF.DetailedBoundPayloadStep.microstepSameTime
                hTargetDispatch
                hSameTargetTime
                hLaterMicrostep

            have hInternalPrefix :
                LF.DetailedBoundPayloadTauSteps
                  (Translation.compilePayloadMessageServer
                    server)
                  (.stable targetBeforeState)
                  (.dispatchReady
                    targetBeforeState
                    selectedAction
                    targetAfterState
                    hTargetDispatch) :=

              LF.detailedBoundPayloadMicrostep_to_tauSteps
                hMicrostepDetailedStep

            have hConsumeDetailedStep :
                LF.DetailedBoundPayloadStep
                  (Translation.compilePayloadMessageServer
                    server)
                  (.dispatchReady
                    targetBeforeState
                    selectedAction
                    targetAfterState
                    hTargetDispatch)
                  (.consume selectedAction)
                  (.stable targetAfterState) :=

              LF.DetailedBoundPayloadStep.consumeReady
                hTargetDispatch

            have hTargetWeakStep :
                LF.DetailedBoundPayloadWeakStep
                  (Translation.compilePayloadMessageServer
                    server)
                  (.stable targetBeforeState)
                  (.consume selectedAction)
                  (.stable targetAfterState) := by

              exact
                Common.WeakStep.visible
                  (LF.detailedBoundPayload_consume_visible
                    selectedAction)
                  hInternalPrefix
                  hConsumeDetailedStep
                  (Common.TauSteps.refl
                    (LF.DetailedBoundPayloadState.stable
                      targetAfterState))

            exact
              ⟨LF.DetailedBoundPayloadLabel.consume
                  selectedAction,
               LF.DetailedBoundPayloadState.stable
                 targetAfterState,
               hTargetWeakStep,
               DetailedBoundPayloadLabelCorresponds.consume
                 hSelectedOccurrence,
               DetailedBoundPayloadStateCorresponds.stable
                 hAfterStates,
               detailedBoundPayloadSourceRuntimeInvariant_stable.mpr
                 hFinalSourceTiming,
               detailedBoundPayloadTargetRuntimeInvariant_stable.mpr
                 hFinalTargetRuntime,
               detailedBoundPayloadForwardCanonicalPhase_stable⟩

          · have hSameTargetTag :
                targetBeforeState.currentTag =
                  targetAfterState.currentTag := by

              cases hBeforeTag :
                  targetBeforeState.currentTag

              cases hAfterTag :
                  targetAfterState.currentTag

              simp_all

            have hTargetDetailedStep :
                LF.DetailedBoundPayloadStep
                  (Translation.compilePayloadMessageServer
                    server)
                  (.stable targetBeforeState)
                  (.consume selectedAction)
                  (.stable targetAfterState) :=

              LF.DetailedBoundPayloadStep.consumeNow
                hTargetDispatch
                hSameTargetTag

            exact
              ⟨LF.DetailedBoundPayloadLabel.consume
                  selectedAction,
               LF.DetailedBoundPayloadState.stable
                 targetAfterState,
               LF.detailedBoundPayloadConsume_is_weak
                 hTargetDetailedStep,
               DetailedBoundPayloadLabelCorresponds.consume
                 hSelectedOccurrence,
               DetailedBoundPayloadStateCorresponds.stable
                 hAfterStates,
               detailedBoundPayloadSourceRuntimeInvariant_stable.mpr
                 hFinalSourceTiming,
               detailedBoundPayloadTargetRuntimeInvariant_stable.mpr
                 hFinalTargetRuntime,
               detailedBoundPayloadForwardCanonicalPhase_stable⟩

      | sameTimeMicrostepAhead
          sourceDispatch
          hSourceSameTime
          hTargetSameTime
          hLaterMicrostep
          hWitness =>

          simp [
            DetailedBoundPayloadForwardCanonicalPhase
          ] at hCanonical

/--
Finite forward correspondence obtained by recursively following only the
canonical invariant-carrying weak match selected for each exact source step.

No universal continuation compatibility predicate is required.
-/
theorem detailedBoundPayloadSteps_forward_with_invariants
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState
        server}
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
    (hSourceInvariant :
      DetailedBoundPayloadSourceRuntimeInvariant
        server
        sourceBefore)
    (hTargetInvariant :
      DetailedBoundPayloadTargetRuntimeInvariant
        server
        targetBefore)
    (hCanonical :
      DetailedBoundPayloadForwardCanonicalPhase
        sourceBefore
        targetBefore)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
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
            targetLabels) ∧

        DetailedBoundPayloadSourceRuntimeInvariant
          server
          sourceAfter ∧

        DetailedBoundPayloadTargetRuntimeInvariant
          server
          targetAfter ∧

        DetailedBoundPayloadForwardCanonicalPhase
          sourceAfter
          targetAfter := by

  induction hSourceSteps generalizing targetBefore with

  | refl sourceState =>
      exact
        ⟨[],
         targetBefore,
         Common.WeakSteps.refl
           targetBefore,
         DetailedBoundPayloadWeakLabelTraceCorresponds.nil,
         hStates,
         DetailedBoundPayloadObservableTraceCorresponds.nil,
         hSourceInvariant,
         hTargetInvariant,
         hCanonical⟩

  | cons hHead hTail inductionHypothesis =>

      rcases
          detailedBoundPayloadForwardInvariantMatch
            hHead
            hStates
            hSourceInvariant
            hTargetInvariant
            hCanonical
            hServerTiming
        with
          ⟨targetHeadLabel,
           targetMiddle,
           hTargetHead,
           hHeadLabels,
           hMiddleStates,
           hMiddleSourceInvariant,
           hMiddleTargetInvariant,
           hMiddleCanonical⟩

      rcases
          inductionHypothesis
            hMiddleStates
            hMiddleSourceInvariant
            hMiddleTargetInvariant
            hMiddleCanonical
        with
          ⟨targetRemainingLabels,
           targetAfter,
           hTargetTail,
           hTailLabels,
           hFinalStates,
           hObservableTail,
           hFinalSourceInvariant,
           hFinalTargetInvariant,
           hFinalCanonical⟩

      have hTrace :
          DetailedBoundPayloadWeakLabelTraceCorresponds
            (_ :: _)
            (targetHeadLabel ::
              targetRemainingLabels) :=

        DetailedBoundPayloadWeakLabelTraceCorresponds.cons
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
         hFinalTargetInvariant,
         hFinalCanonical⟩

end Correctness
end Relico
