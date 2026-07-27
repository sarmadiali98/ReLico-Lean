import Relico.Correctness.BoundPayloadDispatch
import Relico.Correctness.DetailedBoundPayloadWeakFoundation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
One payload-aware forward weak-simulation match.

The package contains a generated-LF weak transition, payload-aware detailed
label correspondence, and preservation of phase-indexed state
correspondence.
-/
def DetailedBoundPayloadForwardMatch
    (server : DTR.PayloadMessageServer)
    (sourceLabel :
      DTR.DetailedBoundPayloadLabel)
    (sourceAfter :
      DTR.DetailedBoundPayloadState server)
    (targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)) :
    Prop :=
  ∃ targetLabel : LF.DetailedBoundPayloadLabel,
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
          targetAfter

/--
A generated-LF bound-payload dispatch preserves complete-tag order.
-/
theorem lfBoundPayloadDispatch_tagOrder
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.BoundPayloadDispatchStep
        reaction
        before
        selectedAction
        after) :
    LF.Tag.PrecedesOrEqual
      before.currentTag
      after.currentTag := by

  cases hDispatch with

  | fire
      currentTag
      stateValue
      parameters
      pendingActions
      remainingActions
      selectedAction
      boundParameters
      hRemoved
      hEarliest
      hNotPast
      hTrigger
      hBind =>

      exact hNotPast

/--
At equal metric time, a generated-LF bound-payload dispatch cannot move to an
earlier microstep.
-/
theorem lfBoundPayloadDispatch_microstep_le_of_sameTime
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.BoundPayloadDispatchStep
        reaction
        before
        selectedAction
        after)
    (hSameTime :
      before.currentTag.time =
        after.currentTag.time) :
    before.currentTag.microstep ≤
      after.currentTag.microstep := by

  have hOrder :
      LF.Tag.PrecedesOrEqual
        before.currentTag
        after.currentTag :=
    lfBoundPayloadDispatch_tagOrder
      hDispatch

  change
    before.currentTag.time <
          after.currentTag.time ∨
      (before.currentTag.time =
            after.currentTag.time ∧
        before.currentTag.microstep ≤
          after.currentTag.microstep)
    at hOrder

  rcases hOrder with
    hEarlier | hSame

  · exact
      False.elim
        ((Nat.ne_of_lt hEarlier)
          hSameTime)

  · exact hSame.2

/--
Forward weak simulation for one parameter-aware source statement step.

The corresponding generated-LF scheduling statement is internal at the
detailed level.
-/
theorem detailedBoundPayload_statement_forward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {sourceLabel : DTR.BoundPayloadLabel}
    {targetBefore : LF.BoundPayloadState}
    (hSourceStep :
      DTR.BoundPayloadStep
        server.name
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DetailedBoundPayloadForwardMatch
      server
      .tau
      (.stable sourceAfter)
      (.stable targetBefore) := by

  have hStable :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore :=
    DetailedBoundPayloadStateCorresponds.stable_iff.mp
      hStates

  rcases
      boundPayloadStep_forward
        hStable
        hSourceStep
    with
      ⟨targetLabel,
       targetAfter,
       hTargetStep,
       _hStatementLabels,
       hFinalStates⟩

  exact
    ⟨
      .tau,
      .stable targetAfter,
      LF.detailedBoundPayloadStatement_is_weak
        hTargetStep,
      DetailedBoundPayloadLabelCorresponds.tau,
      DetailedBoundPayloadStateCorresponds.stable
        hFinalStates
    ⟩

/--
Forward weak simulation for the visible metric-time phase of a future
payload-bearing source dispatch.
-/
theorem detailedBoundPayload_timeAdvance_forward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {targetBefore : LF.BoundPayloadState}
    (hSourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter)
    (hFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore))
    (hCompatible :
      BoundPayloadForwardDispatchCompatible
        selectedMessage
        sourceAfter.pendingMessages
        targetBefore) :
    DetailedBoundPayloadForwardMatch
      server
      (.timeAdvance
        sourceBefore.currentTime
        sourceAfter.currentTime)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceAfter
        hSourceDispatch)
      (.stable targetBefore) := by

  have hStable :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore :=
    DetailedBoundPayloadStateCorresponds.stable_iff.mp
      hStates

  rcases
      boundPayloadDispatch_forward_of_compatible
        hSourceDispatch
        hStable
        hCompatible
    with
      ⟨selectedAction,
       targetAfter,
       hTargetDispatch,
       hSelectedOccurrence,
       hAfterStates⟩

  have hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time := by

    calc
      targetBefore.currentTag.time =
          sourceBefore.currentTime :=
        hStable.currentTime

      _ <
          sourceAfter.currentTime :=
        hFuture

      _ =
          targetAfter.currentTag.time :=
        hAfterStates.currentTime.symm

  have hWitness :
      DetailedBoundPayloadDispatchWitnessCorresponds
        server
        sourceBefore
        selectedMessage
        sourceAfter
        targetBefore
        selectedAction
        targetAfter := {
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
        (.stable targetBefore)
        (.timeAdvance
          targetBefore.currentTag.time
          targetAfter.currentTag.time)
        (.afterTime
          targetBefore
          selectedAction
          targetAfter
          hTargetDispatch) :=
    LF.DetailedBoundPayloadStep.timeAdvance
      hTargetDispatch
      hTargetFuture

  exact
    ⟨
      .timeAdvance
        targetBefore.currentTag.time
        targetAfter.currentTag.time,
      .afterTime
        targetBefore
        selectedAction
        targetAfter
        hTargetDispatch,
      LF.detailedBoundPayloadTimeAdvance_is_weak
        hTargetDetailedStep,
      DetailedBoundPayloadLabelCorresponds.timeAdvance
        hStable.currentTime
        hAfterStates.currentTime,
      DetailedBoundPayloadStateCorresponds.futureAfterTime
        hFuture
        hTargetFuture
        hWitness
    ⟩

/--
Forward weak simulation for source consumption when generated LF is
immediately after a visible future metric-time transition.

A positive destination microstep is absorbed into the internal prefix of the
weak visible consumption transition.
-/
theorem detailedBoundPayload_consume_afterTime_forward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)) :
    DetailedBoundPayloadForwardMatch
      server
      (.consume selectedMessage)
      (.stable sourceAfter)
      (.afterTime
        targetBefore
        selectedAction
        targetAfter
        targetDispatch) := by

  cases hStates with

  | futureAfterTime
      _hSourceFuture
      _hTargetFuture
      hWitness =>

      rcases
          Nat.eq_zero_or_pos
            targetAfter.currentTag.microstep
        with
          hZero |
          hPositive

      · have hTargetDetailedStep :
            LF.DetailedBoundPayloadStep
              (Translation.compilePayloadMessageServer
                server)
              (.afterTime
                targetBefore
                selectedAction
                targetAfter
                targetDispatch)
              (.consume selectedAction)
              (.stable targetAfter) :=
          LF.DetailedBoundPayloadStep.consumeAfterTimeZero
            targetDispatch
            hZero

        exact
          ⟨
            .consume selectedAction,
            .stable targetAfter,
            LF.detailedBoundPayloadConsume_is_weak
              hTargetDetailedStep,
            DetailedBoundPayloadLabelCorresponds.consume
              hWitness.selectedOccurrence,
            DetailedBoundPayloadStateCorresponds.stable
              hWitness.afterState
          ⟩

      · have hMicrostepDetailedStep :
            LF.DetailedBoundPayloadStep
              (Translation.compilePayloadMessageServer
                server)
              (.afterTime
                targetBefore
                selectedAction
                targetAfter
                targetDispatch)
              (.microstepAdvance
                {
                  time :=
                    targetAfter.currentTag.time

                  microstep :=
                    0
                }
                targetAfter.currentTag)
              (.dispatchReady
                targetBefore
                selectedAction
                targetAfter
                targetDispatch) :=
          LF.DetailedBoundPayloadStep.microstepAfterTime
            targetDispatch
            hPositive

        have hInternalPrefix :
            LF.DetailedBoundPayloadTauSteps
              (Translation.compilePayloadMessageServer
                server)
              (.afterTime
                targetBefore
                selectedAction
                targetAfter
                targetDispatch)
              (.dispatchReady
                targetBefore
                selectedAction
                targetAfter
                targetDispatch) :=
          LF.detailedBoundPayloadMicrostep_to_tauSteps
            hMicrostepDetailedStep

        have hConsumeDetailedStep :
            LF.DetailedBoundPayloadStep
              (Translation.compilePayloadMessageServer
                server)
              (.dispatchReady
                targetBefore
                selectedAction
                targetAfter
                targetDispatch)
              (.consume selectedAction)
              (.stable targetAfter) :=
          LF.DetailedBoundPayloadStep.consumeReady
            targetDispatch

        have hTargetWeakStep :
            LF.DetailedBoundPayloadWeakStep
              (Translation.compilePayloadMessageServer
                server)
              (.afterTime
                targetBefore
                selectedAction
                targetAfter
                targetDispatch)
              (.consume selectedAction)
              (.stable targetAfter) := by

          exact
            Common.WeakStep.visible
              (LF.detailedBoundPayload_consume_visible
                selectedAction)
              hInternalPrefix
              hConsumeDetailedStep
              (Common.TauSteps.refl
                (LF.DetailedBoundPayloadState.stable
                  targetAfter))

        exact
          ⟨
            .consume selectedAction,
            .stable targetAfter,
            hTargetWeakStep,
            DetailedBoundPayloadLabelCorresponds.consume
              hWitness.selectedOccurrence,
            DetailedBoundPayloadStateCorresponds.stable
              hWitness.afterState
          ⟩

/--
Forward weak simulation for payload-bearing source consumption when both
semantic layers are already dispatch-ready.
-/
theorem detailedBoundPayload_consume_ready_forward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {sourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter}
    {targetBefore targetAfter :
      LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    {targetDispatch :
      LF.BoundPayloadDispatchStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        selectedAction
        targetAfter}
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceAfter
          sourceDispatch)
        (.dispatchReady
          targetBefore
          selectedAction
          targetAfter
          targetDispatch)) :
    DetailedBoundPayloadForwardMatch
      server
      (.consume selectedMessage)
      (.stable sourceAfter)
      (.dispatchReady
        targetBefore
        selectedAction
        targetAfter
        targetDispatch) := by

  cases hStates with

  | futureReady
      _hSourceFuture
      _hTargetFuture
      _hPositiveMicrostep
      hWitness =>

      have hTargetDetailedStep :
          LF.DetailedBoundPayloadStep
            (Translation.compilePayloadMessageServer
              server)
            (.dispatchReady
              targetBefore
              selectedAction
              targetAfter
              targetDispatch)
            (.consume selectedAction)
            (.stable targetAfter) :=
        LF.DetailedBoundPayloadStep.consumeReady
          targetDispatch

      exact
        ⟨
          .consume selectedAction,
          .stable targetAfter,
          LF.detailedBoundPayloadConsume_is_weak
            hTargetDetailedStep,
          DetailedBoundPayloadLabelCorresponds.consume
            hWitness.selectedOccurrence,
          DetailedBoundPayloadStateCorresponds.stable
            hWitness.afterState
        ⟩

/--
Forward weak simulation for a same-metric-time payload-bearing source
consumption.

Generated LF either consumes at the current complete tag or first advances
internally to a later microstep. Both cases form one weak visible consumption
match.
-/
theorem detailedBoundPayload_consumeNow_forward_weak
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {targetBefore : LF.BoundPayloadState}
    (hSourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter)
    (hSameSourceTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        (.stable sourceBefore)
        (.stable targetBefore))
    (hCompatible :
      BoundPayloadForwardDispatchCompatible
        selectedMessage
        sourceAfter.pendingMessages
        targetBefore) :
    DetailedBoundPayloadForwardMatch
      server
      (.consume selectedMessage)
      (.stable sourceAfter)
      (.stable targetBefore) := by

  have hStable :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore :=
    DetailedBoundPayloadStateCorresponds.stable_iff.mp
      hStates

  rcases
      boundPayloadDispatch_forward_of_compatible
        hSourceDispatch
        hStable
        hCompatible
    with
      ⟨selectedAction,
       targetAfter,
       hTargetDispatch,
       hSelectedOccurrence,
       hAfterStates⟩

  have hWitness :
      DetailedBoundPayloadDispatchWitnessCorresponds
        server
        sourceBefore
        selectedMessage
        sourceAfter
        targetBefore
        selectedAction
        targetAfter := {
    beforeState :=
      hStable

    selectedOccurrence :=
      hSelectedOccurrence

    afterState :=
      hAfterStates
  }

  have hSameTargetTime :
      targetBefore.currentTag.time =
        targetAfter.currentTag.time := by

    calc
      targetBefore.currentTag.time =
          sourceBefore.currentTime :=
        hStable.currentTime

      _ =
          sourceAfter.currentTime :=
        hSameSourceTime

      _ =
          targetAfter.currentTag.time :=
        hAfterStates.currentTime.symm

  have hMicrostepOrder :
      targetBefore.currentTag.microstep ≤
        targetAfter.currentTag.microstep :=
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
          (.stable targetBefore)
          (.microstepAdvance
            targetBefore.currentTag
            targetAfter.currentTag)
          (.dispatchReady
            targetBefore
            selectedAction
            targetAfter
            hTargetDispatch) :=
      LF.DetailedBoundPayloadStep.microstepSameTime
        hTargetDispatch
        hSameTargetTime
        hLaterMicrostep

    have hInternalPrefix :
        LF.DetailedBoundPayloadTauSteps
          (Translation.compilePayloadMessageServer
            server)
          (.stable targetBefore)
          (.dispatchReady
            targetBefore
            selectedAction
            targetAfter
            hTargetDispatch) :=
      LF.detailedBoundPayloadMicrostep_to_tauSteps
        hMicrostepDetailedStep

    have hConsumeDetailedStep :
        LF.DetailedBoundPayloadStep
          (Translation.compilePayloadMessageServer
            server)
          (.dispatchReady
            targetBefore
            selectedAction
            targetAfter
            hTargetDispatch)
          (.consume selectedAction)
          (.stable targetAfter) :=
      LF.DetailedBoundPayloadStep.consumeReady
        hTargetDispatch

    have hTargetWeakStep :
        LF.DetailedBoundPayloadWeakStep
          (Translation.compilePayloadMessageServer
            server)
          (.stable targetBefore)
          (.consume selectedAction)
          (.stable targetAfter) := by

      exact
        Common.WeakStep.visible
          (LF.detailedBoundPayload_consume_visible
            selectedAction)
          hInternalPrefix
          hConsumeDetailedStep
          (Common.TauSteps.refl
            (LF.DetailedBoundPayloadState.stable
              targetAfter))

    exact
      ⟨
        .consume selectedAction,
        .stable targetAfter,
        hTargetWeakStep,
        DetailedBoundPayloadLabelCorresponds.consume
          hSelectedOccurrence,
        DetailedBoundPayloadStateCorresponds.stable
          hAfterStates
      ⟩

  · have hSameTargetTag :
        targetBefore.currentTag =
          targetAfter.currentTag := by

      cases hBeforeTag :
          targetBefore.currentTag

      cases hAfterTag :
          targetAfter.currentTag

      simp_all

    have hTargetDetailedStep :
        LF.DetailedBoundPayloadStep
          (Translation.compilePayloadMessageServer
            server)
          (.stable targetBefore)
          (.consume selectedAction)
          (.stable targetAfter) :=
      LF.DetailedBoundPayloadStep.consumeNow
        hTargetDispatch
        hSameTargetTag

    exact
      ⟨
        .consume selectedAction,
        .stable targetAfter,
        LF.detailedBoundPayloadConsume_is_weak
          hTargetDetailedStep,
        DetailedBoundPayloadLabelCorresponds.consume
          hSelectedOccurrence,
        DetailedBoundPayloadStateCorresponds.stable
          hAfterStates
      ⟩

/--
Every payload-aware forward match contains a generated-LF destination state
corresponding to the source destination state.
-/
theorem DetailedBoundPayloadForwardMatch.target_corresponds
    {server : DTR.PayloadMessageServer}
    {sourceLabel :
      DTR.DetailedBoundPayloadLabel}
    {sourceAfter :
      DTR.DetailedBoundPayloadState server}
    {targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    (hMatch :
      DetailedBoundPayloadForwardMatch
        server
        sourceLabel
        sourceAfter
        targetBefore) :
    ∃ targetAfter :
        LF.DetailedBoundPayloadState
          (Translation.compilePayloadMessageServer
            server),
      DetailedBoundPayloadStateCorresponds
        server
        sourceAfter
        targetAfter := by

  rcases hMatch with
    ⟨_targetLabel,
     targetAfter,
     _hWeakStep,
     _hLabels,
     hStates⟩

  exact
    ⟨targetAfter,
     hStates⟩


end Correctness
end Relico
