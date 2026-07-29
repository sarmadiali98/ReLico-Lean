import Relico.DTR.DetailedMultiStorePayloadWeakSemantics
import Relico.LF.DetailedMultiStorePayloadWeakSemantics
import Relico.Correctness.MultiStorePayloadDetailedRuntimeLabelCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
A same-metric-time payload dispatch cannot decrease the LF microstep.

This follows directly from the payload dispatch's complete-tag not-past
premise. No scheduling or dispatch rule is strengthened.
-/
theorem lfMultiStorePayloadDispatch_microstep_le_of_sameTime
    {messageReactions :
      List LF.MultiStorePayloadReaction}
    {before after :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hDispatch :
      LF.MultiStorePayloadDispatchStep
        messageReactions
        before
        selectedAction
        selectedReaction
        after)
    (hSameTime :
      before.currentTag.time =
        after.currentTag.time) :
    before.currentTag.microstep ≤
      after.currentTag.microstep := by

  cases hDispatch with

  | fire
      currentTag
      _stateStore
      _parameters
      _pendingActions
      _remainingActions
      selectedAction
      _selectedReaction
      _boundParameters
      _hReactionDeclared
      _hRemoved
      _hPriorityEligible
      hNotPast
      _hTrigger
      _hBind =>

      change
        currentTag.microstep ≤
          selectedAction.tag.microstep

      change
        currentTag.time =
          selectedAction.tag.time
        at hSameTime

      unfold
        LF.Tag.PrecedesOrEqual
        at hNotPast

      rcases hNotPast with
        hEarlierTime |
        hSameMetricTime

      · rw [hSameTime] at hEarlierTime

        exact
          False.elim
            ((Nat.lt_irrefl _)
              hEarlierTime)

      · exact
          hSameMetricTime.2

/--
Forward payload-aware weak matching for one detailed dispatch-phase label.

The matching LF weak step retains exact payload-aware label correspondence and
ends in a detailed runtime state corresponding to the DTR destination.
-/
def MultiStorePayloadDetailedForwardMatch
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceLabel :
      DTR.DetailedMultiStorePayloadLabel)
    (sourceAfter :
      DTR.DetailedMultiStorePayloadState
        messageServers)
    (targetBefore :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)) :
    Prop :=

  ∃ targetLabel targetAfter,
    LF.DetailedMultiStorePayloadWeakStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        targetLabel
        targetAfter ∧
      MultiStorePayloadDetailedLabelCorresponds
          sourceLabel
          targetLabel ∧
        MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          sourceAfter
          targetAfter

/--
Backward payload-aware weak matching for one detailed dispatch-phase label.

The matching DTR weak step retains exact payload-aware label correspondence
and ends in a state corresponding to the LF destination.
-/
def MultiStorePayloadDetailedBackwardMatch
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (targetLabel :
      LF.DetailedMultiStorePayloadLabel)
    (targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers))
    (sourceBefore :
      DTR.DetailedMultiStorePayloadState
        messageServers) :
    Prop :=

  ∃ sourceLabel sourceAfter,
    DTR.DetailedMultiStorePayloadWeakStep
        messageServers
        sourceBefore
        sourceLabel
        sourceAfter ∧
      MultiStorePayloadDetailedLabelCorresponds
          sourceLabel
          targetLabel ∧
        MultiStorePayloadDetailedRuntimeStateCorresponds
          messageServers
          sourceAfter
          targetAfter

/--
Every forward match exposes a corresponding generated-LF destination.
-/
theorem MultiStorePayloadDetailedForwardMatch.target_corresponds
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceLabel :
      DTR.DetailedMultiStorePayloadLabel}
    {sourceAfter :
      DTR.DetailedMultiStorePayloadState
        messageServers}
    {targetBefore :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
    (hMatch :
      MultiStorePayloadDetailedForwardMatch
        messageServers
        sourceLabel
        sourceAfter
        targetBefore) :
    ∃ targetAfter,
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        sourceAfter
        targetAfter := by

  rcases hMatch with
    ⟨_targetLabel,
     targetAfter,
     _targetStep,
     _labels,
     states⟩

  exact
    ⟨targetAfter,
     states⟩

/--
Every backward match exposes a corresponding DTR destination.
-/
theorem MultiStorePayloadDetailedBackwardMatch.source_corresponds
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {targetLabel :
      LF.DetailedMultiStorePayloadLabel}
    {targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
    {sourceBefore :
      DTR.DetailedMultiStorePayloadState
        messageServers}
    (hMatch :
      MultiStorePayloadDetailedBackwardMatch
        messageServers
        targetLabel
        targetAfter
        sourceBefore) :
    ∃ sourceAfter,
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        sourceAfter
        targetAfter := by

  rcases hMatch with
    ⟨_sourceLabel,
     sourceAfter,
     _sourceStep,
     _labels,
     states⟩

  exact
    ⟨sourceAfter,
     states⟩

/--
Forward weak matching for visible future metric-time advancement.
-/
theorem multiStorePayloadDetailedRuntime_timeAdvance_forward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetBefore :
      LF.MultiStorePayloadState}
    (hSourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    MultiStorePayloadDetailedForwardMatch
      messageServers
      (.timeAdvance
        sourceBefore.currentTime
        sourceAfter.currentTime)
      (.dispatchReady
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        hSourceDispatch)
      (.stable targetBefore) := by

  have hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    multiStorePayloadDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     hWitness⟩ :=
      multiStorePayloadDetailedRuntime_dispatch_forward
        hSourceDispatch
        hRuntime

  have hTimes :=
    multiStorePayloadDetailedRuntimeDispatchWitness_times
      hWitness

  have hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time := by

    calc
      targetBefore.currentTag.time =
          sourceBefore.currentTime :=
        hTimes.1

      _ <
          sourceAfter.currentTime :=
        hFuture

      _ =
          targetAfter.currentTag.time :=
        hTimes.2.symm

  exact
    ⟨.timeAdvance
       targetBefore.currentTag.time
       targetAfter.currentTag.time,
     .afterTime
       targetBefore
       selectedAction
       (Translation.compileMultiStorePayloadReaction
         selectedServer)
       targetAfter
       hTargetDispatch,
     LF.detailedMultiStorePayloadTimeAdvance_is_weak
       (LF.DetailedMultiStorePayloadStep.timeAdvance
         hTargetDispatch
         hTargetFuture),
     MultiStorePayloadDetailedLabelCorresponds.timeAdvance
       hTimes.1
       hTimes.2,
     multiStorePayloadDetailedRuntime_futureAfterTime
       hFuture
       hWitness⟩

/--
Forward weak matching for consumption while LF is in its future `afterTime`
phase.

A positive destination microstep is absorbed into the weak LF prefix.
-/
theorem multiStorePayloadDetailedRuntime_consume_afterTime_forward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {sourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.dispatchReady
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    MultiStorePayloadDetailedForwardMatch
      messageServers
      (.consume
        selectedMessage
        selectedServer)
      (.stable sourceAfter)
      (.afterTime
        targetBefore
        selectedAction
        selectedReaction
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

      · exact
          ⟨.consume
             selectedAction
             selectedReaction,
           .stable targetAfter,
           LF.detailedMultiStorePayloadConsume_is_weak
             (LF.DetailedMultiStorePayloadStep.consumeAfterTimeZero
               targetDispatch
               hZero),
           MultiStorePayloadDetailedLabelCorresponds.consume
             hWitness.selectedOccurrence
             hWitness.selectedHandler,
           MultiStorePayloadDetailedRuntimeStateCorresponds.stable
             hWitness.afterState⟩

      · exact
          ⟨.consume
             selectedAction
             selectedReaction,
           .stable targetAfter,
           LF.detailedMultiStorePayloadConsumeAfterTimePositive_is_weak
             targetDispatch
             hPositive,
           MultiStorePayloadDetailedLabelCorresponds.consume
             hWitness.selectedOccurrence
             hWitness.selectedHandler,
           MultiStorePayloadDetailedRuntimeStateCorresponds.stable
             hWitness.afterState⟩

/--
Forward weak matching for consumption when both systems are dispatch-ready.
-/
theorem multiStorePayloadDetailedRuntime_consume_ready_forward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {sourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.dispatchReady
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          sourceDispatch)
        (.dispatchReady
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    MultiStorePayloadDetailedForwardMatch
      messageServers
      (.consume
        selectedMessage
        selectedServer)
      (.stable sourceAfter)
      (.dispatchReady
        targetBefore
        selectedAction
        selectedReaction
        targetAfter
        targetDispatch) := by

  cases hStates with

  | futureReady
      _hSourceFuture
      _hTargetFuture
      _hPositiveMicrostep
      hWitness =>

      exact
        ⟨.consume
           selectedAction
           selectedReaction,
         .stable targetAfter,
         LF.detailedMultiStorePayloadConsume_is_weak
           (LF.DetailedMultiStorePayloadStep.consumeReady
             targetDispatch),
         MultiStorePayloadDetailedLabelCorresponds.consume
           hWitness.selectedOccurrence
           hWitness.selectedHandler,
         MultiStorePayloadDetailedRuntimeStateCorresponds.stable
           hWitness.afterState⟩

/--
Forward weak matching for a same-metric-time DTR dispatch.

LF either consumes at the same complete tag or advances through one internal
microstep before consuming.
-/
theorem multiStorePayloadDetailedRuntime_consumeNow_forward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {targetBefore :
      LF.MultiStorePayloadState}
    (hSourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hSameSourceTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    MultiStorePayloadDetailedForwardMatch
      messageServers
      (.consume
        selectedMessage
        selectedServer)
      (.stable sourceAfter)
      (.stable targetBefore) := by

  have hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    multiStorePayloadDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     hWitness⟩ :=
      multiStorePayloadDetailedRuntime_dispatch_forward
        hSourceDispatch
        hRuntime

  have hTimes :=
    multiStorePayloadDetailedRuntimeDispatchWitness_times
      hWitness

  have hSameTargetTime :
      targetBefore.currentTag.time =
        targetAfter.currentTag.time := by

    calc
      targetBefore.currentTag.time =
          sourceBefore.currentTime :=
        hTimes.1

      _ =
          sourceAfter.currentTime :=
        hSameSourceTime

      _ =
          targetAfter.currentTag.time :=
        hTimes.2.symm

  have hMicrostepOrder :
      targetBefore.currentTag.microstep ≤
        targetAfter.currentTag.microstep :=
    lfMultiStorePayloadDispatch_microstep_le_of_sameTime
      hTargetDispatch
      hSameTargetTime

  rcases
      Nat.lt_or_eq_of_le
        hMicrostepOrder
    with
      hLaterMicrostep |
      hSameMicrostep

  · exact
      ⟨.consume
         selectedAction
         (Translation.compileMultiStorePayloadReaction
           selectedServer),
       .stable targetAfter,
       LF.detailedMultiStorePayloadSameTimeMicrostepThenConsume_is_weak
         hTargetDispatch
         hSameTargetTime
         hLaterMicrostep,
       MultiStorePayloadDetailedLabelCorresponds.consume
         hWitness.selectedOccurrence
         hWitness.selectedHandler,
       MultiStorePayloadDetailedRuntimeStateCorresponds.stable
         hWitness.afterState⟩

  · exact
      ⟨.consume
         selectedAction
         (Translation.compileMultiStorePayloadReaction
           selectedServer),
       .stable targetAfter,
       LF.detailedMultiStorePayloadConsume_is_weak
         (LF.DetailedMultiStorePayloadStep.consumeNow
           hTargetDispatch
           hSameTargetTime
           hSameMicrostep),
       MultiStorePayloadDetailedLabelCorresponds.consume
         hWitness.selectedOccurrence
         hWitness.selectedHandler,
       MultiStorePayloadDetailedRuntimeStateCorresponds.stable
         hWitness.afterState⟩

/--
Backward weak matching for visible future metric-time advancement.
-/
theorem multiStorePayloadDetailedRuntime_timeAdvance_backward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    MultiStorePayloadDetailedBackwardMatch
      messageServers
      (.timeAdvance
        targetBefore.currentTag.time
        targetAfter.currentTag.time)
      (.afterTime
        targetBefore
        selectedAction
        selectedReaction
        targetAfter
        hTargetDispatch)
      (.stable sourceBefore) := by

  have hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    multiStorePayloadDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hSourceDispatch,
     hWitness⟩ :=
      multiStorePayloadDetailedRuntime_dispatch_backward
        hTargetDispatch
        hRuntime

  have hTimes :=
    multiStorePayloadDetailedRuntimeDispatchWitness_times
      hWitness

  have hSourceFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime := by

    calc
      sourceBefore.currentTime =
          targetBefore.currentTag.time :=
        hTimes.1.symm

      _ <
          targetAfter.currentTag.time :=
        hTargetFuture

      _ =
          sourceAfter.currentTime :=
        hTimes.2

  exact
    ⟨.timeAdvance
       sourceBefore.currentTime
       sourceAfter.currentTime,
     .dispatchReady
       sourceBefore
       selectedMessage
       selectedServer
       sourceAfter
       hSourceDispatch,
     DTR.detailedMultiStorePayloadTimeAdvance_is_weak
       (DTR.DetailedMultiStorePayloadStep.timeAdvance
         hSourceDispatch
         hSourceFuture),
     MultiStorePayloadDetailedLabelCorresponds.timeAdvance
       hTimes.1
       hTimes.2,
     multiStorePayloadDetailedRuntime_futureAfterTime
       hSourceFuture
       hWitness⟩

/--
Backward weak matching for the target-only microstep after future metric-time
advancement. DTR stutters in its dispatch-ready phase.
-/
theorem multiStorePayloadDetailedRuntime_microstepAfterTime_backward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {sourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hPositiveMicrostep :
      0 <
        targetAfter.currentTag.microstep)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.dispatchReady
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    MultiStorePayloadDetailedBackwardMatch
      messageServers
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
        selectedReaction
        targetAfter
        targetDispatch)
      (.dispatchReady
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        sourceDispatch) := by

  cases hStates with

  | futureAfterTime
      hSourceFuture
      _hTargetFuture
      hWitness =>

      exact
        ⟨.tau,
         .dispatchReady
           sourceBefore
           selectedMessage
           selectedServer
           sourceAfter
           sourceDispatch,
         DTR.detailedMultiStorePayloadWeakTau_refl
           (.dispatchReady
             sourceBefore
             selectedMessage
             selectedServer
             sourceAfter
             sourceDispatch),
         MultiStorePayloadDetailedLabelCorresponds.microstep
           {
             time :=
               targetAfter.currentTag.time

             microstep :=
               0
           }
           targetAfter.currentTag,
         multiStorePayloadDetailedRuntime_futureReady
           hSourceFuture
           hPositiveMicrostep
           hWitness⟩

/--
Backward weak matching for a same-time LF microstep from stable states.
-/
theorem multiStorePayloadDetailedRuntime_microstepSameTime_backward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hTargetSameTime :
      targetBefore.currentTag.time =
        targetAfter.currentTag.time)
    (hLaterMicrostep :
      targetBefore.currentTag.microstep <
        targetAfter.currentTag.microstep)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    MultiStorePayloadDetailedBackwardMatch
      messageServers
      (.microstepAdvance
        targetBefore.currentTag
        targetAfter.currentTag)
      (.dispatchReady
        targetBefore
        selectedAction
        selectedReaction
        targetAfter
        hTargetDispatch)
      (.stable sourceBefore) := by

  have hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    multiStorePayloadDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hSourceDispatch,
     hWitness⟩ :=
      multiStorePayloadDetailedRuntime_dispatch_backward
        hTargetDispatch
        hRuntime

  have hTimes :=
    multiStorePayloadDetailedRuntimeDispatchWitness_times
      hWitness

  have hSourceSameTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime := by

    calc
      sourceBefore.currentTime =
          targetBefore.currentTag.time :=
        hTimes.1.symm

      _ =
          targetAfter.currentTag.time :=
        hTargetSameTime

      _ =
          sourceAfter.currentTime :=
        hTimes.2

  exact
    ⟨.tau,
     .stable sourceBefore,
     DTR.detailedMultiStorePayloadWeakTau_refl
       (.stable sourceBefore),
     MultiStorePayloadDetailedLabelCorresponds.microstep
       targetBefore.currentTag
       targetAfter.currentTag,
     multiStorePayloadDetailedRuntime_sameTimeMicrostepAhead
       hSourceDispatch
       hSourceSameTime
       hLaterMicrostep
       hWitness⟩

/--
Backward weak matching for LF consumption immediately after future time
advancement at destination microstep zero.
-/
theorem multiStorePayloadDetailedRuntime_consumeAfterTimeZero_backward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {sourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (_hZeroMicrostep :
      targetAfter.currentTag.microstep =
        0)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.dispatchReady
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    MultiStorePayloadDetailedBackwardMatch
      messageServers
      (.consume
        selectedAction
        selectedReaction)
      (.stable targetAfter)
      (.dispatchReady
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        sourceDispatch) := by

  cases hStates with

  | futureAfterTime
      _hSourceFuture
      _hTargetFuture
      hWitness =>

      exact
        ⟨.consume
           selectedMessage
           selectedServer,
         .stable sourceAfter,
         DTR.detailedMultiStorePayloadConsume_is_weak
           (DTR.DetailedMultiStorePayloadStep.consumeReady
             sourceDispatch),
         MultiStorePayloadDetailedLabelCorresponds.consume
           hWitness.selectedOccurrence
           hWitness.selectedHandler,
         MultiStorePayloadDetailedRuntimeStateCorresponds.stable
           hWitness.afterState⟩

/--
Backward weak matching for LF consumption from a future dispatch-ready phase.
-/
theorem multiStorePayloadDetailedRuntime_consumeReadyFuture_backward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {selectedMessage :
      DTR.PendingMessage}
    {selectedServer :
      DTR.MultiStorePayloadMessageServer}
    {sourceDispatch :
      DTR.MultiStorePayloadDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.dispatchReady
          sourceBefore
          selectedMessage
          selectedServer
          sourceAfter
          sourceDispatch)
        (.dispatchReady
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    MultiStorePayloadDetailedBackwardMatch
      messageServers
      (.consume
        selectedAction
        selectedReaction)
      (.stable targetAfter)
      (.dispatchReady
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter
        sourceDispatch) := by

  cases hStates with

  | futureReady
      _hSourceFuture
      _hTargetFuture
      _hPositiveMicrostep
      hWitness =>

      exact
        ⟨.consume
           selectedMessage
           selectedServer,
         .stable sourceAfter,
         DTR.detailedMultiStorePayloadConsume_is_weak
           (DTR.DetailedMultiStorePayloadStep.consumeReady
             sourceDispatch),
         MultiStorePayloadDetailedLabelCorresponds.consume
           hWitness.selectedOccurrence
           hWitness.selectedHandler,
         MultiStorePayloadDetailedRuntimeStateCorresponds.stable
           hWitness.afterState⟩

/--
Backward weak matching for LF consumption after a same-time target-only
microstep. DTR consumes directly from its stable phase.
-/
theorem multiStorePayloadDetailedRuntime_consumeReadySameTime_backward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    {targetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.dispatchReady
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    MultiStorePayloadDetailedBackwardMatch
      messageServers
      (.consume
        selectedAction
        selectedReaction)
      (.stable targetAfter)
      (.stable sourceBefore) := by

  cases hStates with

  | sameTimeMicrostepAhead
      sourceDispatch
      hSourceSameTime
      _hTargetSameTime
      _hLaterMicrostep
      hWitness =>

      exact
        ⟨.consume
           _
           _,
         .stable _,
         DTR.detailedMultiStorePayloadConsume_is_weak
           (DTR.DetailedMultiStorePayloadStep.consumeNow
             sourceDispatch
             hSourceSameTime),
         MultiStorePayloadDetailedLabelCorresponds.consume
           hWitness.selectedOccurrence
           hWitness.selectedHandler,
         MultiStorePayloadDetailedRuntimeStateCorresponds.stable
           hWitness.afterState⟩

/--
Backward weak matching for direct LF consumption at the current complete tag.
-/
theorem multiStorePayloadDetailedRuntime_consumeNow_backward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    {selectedAction :
      LF.PendingAction}
    {selectedReaction :
      LF.MultiStorePayloadReaction}
    (hTargetDispatch :
      LF.MultiStorePayloadDispatchStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hTargetSameTime :
      targetBefore.currentTag.time =
        targetAfter.currentTag.time)
    (_hTargetSameMicrostep :
      targetBefore.currentTag.microstep =
        targetAfter.currentTag.microstep)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    MultiStorePayloadDetailedBackwardMatch
      messageServers
      (.consume
        selectedAction
        selectedReaction)
      (.stable targetAfter)
      (.stable sourceBefore) := by

  have hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    multiStorePayloadDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedMessage,
     selectedServer,
     sourceAfter,
     hSourceDispatch,
     hWitness⟩ :=
      multiStorePayloadDetailedRuntime_dispatch_backward
        hTargetDispatch
        hRuntime

  have hTimes :=
    multiStorePayloadDetailedRuntimeDispatchWitness_times
      hWitness

  have hSourceSameTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime := by

    calc
      sourceBefore.currentTime =
          targetBefore.currentTag.time :=
        hTimes.1.symm

      _ =
          targetAfter.currentTag.time :=
        hTargetSameTime

      _ =
          sourceAfter.currentTime :=
        hTimes.2

  exact
    ⟨.consume
       selectedMessage
       selectedServer,
     .stable sourceAfter,
     DTR.detailedMultiStorePayloadConsume_is_weak
       (DTR.DetailedMultiStorePayloadStep.consumeNow
         hSourceDispatch
         hSourceSameTime),
     MultiStorePayloadDetailedLabelCorresponds.consume
       hWitness.selectedOccurrence
       hWitness.selectedHandler,
     MultiStorePayloadDetailedRuntimeStateCorresponds.stable
       hWitness.afterState⟩

end Correctness
end Relico
