import Relico.Correctness.DirectLFDetailedRuntimeStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
DirectLF correspondence between one detailed DTR label and one detailed
generated-LF label.

Internal statement transitions correspond directly. Pure LF microstep
progression corresponds to DTR internal stuttering.

Visible time transitions may use syntactically different time expressions,
but the two endpoints must denote the same metric times.

Visible consumption transitions relate the selected pending occurrence and
the selected generated reaction.
-/
inductive DirectLFDetailedLabelCorresponds :
    DTR.DetailedMultiStoreLabel →
    LF.DetailedMultiStoreLabel →
    Prop where

  | tau :
      DirectLFDetailedLabelCorresponds
        DTR.DetailedMultiStoreLabel.tau
        LF.DetailedMultiStoreLabel.tau

  | microstep
      (before after : LF.Tag) :
      DirectLFDetailedLabelCorresponds
        DTR.DetailedMultiStoreLabel.tau
        (LF.DetailedMultiStoreLabel.microstepAdvance
          before
          after)

  | timeAdvance
      {sourceBefore sourceAfter : LogicalTime}
      {targetBefore targetAfter : LogicalTime}
      (hBeforeTime :
        targetBefore =
          sourceBefore)
      (hAfterTime :
        targetAfter =
          sourceAfter) :
      DirectLFDetailedLabelCorresponds
        (DTR.DetailedMultiStoreLabel.timeAdvance
          sourceBefore
          sourceAfter)
        (LF.DetailedMultiStoreLabel.timeAdvance
          targetBefore
          targetAfter)

  | consume
      {sourceMessage : DTR.PendingMessage}
      {sourceServer : DTR.MessageServer}
      {targetAction : LF.PendingAction}
      {targetReaction : LF.Reaction}
      (hOccurrence :
        PendingCorresponds
          sourceMessage
          targetAction)
      (hReaction :
        targetReaction =
          Translation.compileMessageReaction
            sourceServer) :
      DirectLFDetailedLabelCorresponds
        (DTR.DetailedMultiStoreLabel.consume
          sourceMessage
          sourceServer)
        (LF.DetailedMultiStoreLabel.consume
          targetAction
          targetReaction)

/--
One DirectLF runtime forward weak-simulation match.

The structure packages:

- the generated-LF weak label;
- the generated-LF destination state;
- the weak generated-LF execution;
- label correspondence;
- preservation of detailed state correspondence.
-/
def DirectLFDetailedForwardMatch
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (sourceLabel : DTR.DetailedMultiStoreLabel)
    (sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers)
    (targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)) :
    Prop :=
  ∃ targetLabel : LF.DetailedMultiStoreLabel,
    ∃ targetAfter :
        LF.DetailedMultiStoreState
          (Translation.compileMessageReactions
            messageServers),
      LF.DetailedWeakStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          targetLabel
          targetAfter ∧
        DirectLFDetailedLabelCorresponds
          sourceLabel
          targetLabel ∧
        DirectLFDetailedRuntimeStateCorresponds
          messageServers
          sourceAfter
          targetAfter

/--
Forward weak simulation for an internal DTR statement transition.

The DirectLF runtime statement theorem supplies one matching LF statement
transition. Both detailed labels are internal.
-/

theorem directLFDetailedRuntime_statement_forward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {sourceLabel : DTR.Label}
    {targetBefore : LF.StoreState}
    (hSourceStep :
      DTR.MultiStoreStep
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hStatementAppend :
      DirectLFStatementAppendCompatible
        messageServers
        sourceBefore
        targetBefore) :
    DirectLFDetailedForwardMatch
      declaredVariables
      messageServers
      DTR.DetailedMultiStoreLabel.tau
      (.stable sourceAfter)
      (.stable targetBefore) := by

  have hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    directLFDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨_targetLabel,
     targetAfter,
     hTargetStep,
     _hLabels,
     hAfter⟩ :=
      directLF_multiStore_step_forward_runtime
        hSourceStep
        hRuntime
        hStatementAppend

  have hDetailedStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        (.stable targetBefore)
        .tau
        (.stable targetAfter) :=
    LF.DetailedMultiStoreStep.statement
      hTargetStep

  exact
    ⟨LF.DetailedMultiStoreLabel.tau,
     .stable targetAfter,
     LF.detailedWeakStep_of_step
       hDetailedStep,
     DirectLFDetailedLabelCorresponds.tau,
     DetailedStateCorresponds.stable
       hAfter⟩

/--
Forward weak simulation for the visible time-progression phase of a future
DTR dispatch.

The DirectLF runtime dispatch theorem constructs the corresponding LF
dispatch. Existing stable-state correspondence proves that both metric-time
endpoints are equal.
-/

theorem directLFDetailedRuntime_timeAdvance_forward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {targetBefore : LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime)
    (hStates :
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DirectLFDetailedForwardMatch
      declaredVariables
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
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    directLFDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     hWitness⟩ :=
      directLFDetailedRuntime_dispatch_forward
        hSourceDispatch
        hRuntime

  have hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time := by

    calc
      targetBefore.currentTag.time =
          sourceBefore.currentTime :=
        hWitness.beforeState.states.currentTime

      _ <
          sourceAfter.currentTime :=
        hFuture

      _ =
          targetAfter.currentTag.time :=
        hWitness.afterState.states.currentTime.symm

  have hTargetDetailedStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        (.stable targetBefore)
        (.timeAdvance
          targetBefore.currentTag.time
          targetAfter.currentTag.time)
        (.afterTime
          targetBefore
          selectedAction
          (Translation.compileMessageReaction
            selectedServer)
          targetAfter
          hTargetDispatch) :=
    LF.DetailedMultiStoreStep.timeAdvance
      hTargetDispatch
      hTargetFuture

  exact
    ⟨.timeAdvance
       targetBefore.currentTag.time
       targetAfter.currentTag.time,
     .afterTime
       targetBefore
       selectedAction
       (Translation.compileMessageReaction
         selectedServer)
       targetAfter
       hTargetDispatch,
     LF.detailedTimeAdvance_is_weak
       hTargetDetailedStep,
     DirectLFDetailedLabelCorresponds.timeAdvance
       hWitness.beforeState.states.currentTime
       hWitness.afterState.states.currentTime,
     directLFDetailedRuntime_futureAfterTime
       hFuture
       hWitness⟩

/--
Forward weak simulation for DTR consumption when LF is immediately after its
visible future metric-time transition.

When the LF destination microstep is zero, reaction firing occurs directly.

When the destination microstep is positive, LF first performs one internal
microstep transition. That internal prefix is absorbed by the weak visible
consumption transition.
-/
theorem directLFDetailedRuntime_consume_afterTime_forward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hStates :
      DirectLFDetailedRuntimeStateCorresponds
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
    DirectLFDetailedForwardMatch
      declaredVariables
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

      · have hTargetDetailedStep :
            LF.DetailedMultiStoreStep
              declaredVariables
              (Translation.compileLogicalActions
                messageServers)
              (Translation.compileMessageReactions
                messageServers)
              (.afterTime
                targetBefore
                selectedAction
                selectedReaction
                targetAfter
                targetDispatch)
              (.consume
                selectedAction
                selectedReaction)
              (.stable targetAfter) :=
          LF.DetailedMultiStoreStep.consumeAfterTimeZero
            targetDispatch
            hZero

        exact
          ⟨
            .consume
              selectedAction
              selectedReaction,
            .stable targetAfter,
            LF.detailedConsume_is_weak
              hTargetDetailedStep,
            DirectLFDetailedLabelCorresponds.consume
              hWitness.selectedOccurrence
              hWitness.selectedHandler,
            DetailedStateCorresponds.stable
              hWitness.afterState
          ⟩

      · have hMicrostepDetailedStep :
            LF.DetailedMultiStoreStep
              declaredVariables
              (Translation.compileLogicalActions
                messageServers)
              (Translation.compileMessageReactions
                messageServers)
              (.afterTime
                targetBefore
                selectedAction
                selectedReaction
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
                selectedReaction
                targetAfter
                targetDispatch) :=
          LF.DetailedMultiStoreStep.microstepAfterTime
            targetDispatch
            hPositive

        have hInternalPrefix :
            LF.DetailedTauSteps
              declaredVariables
              (Translation.compileLogicalActions
                messageServers)
              (Translation.compileMessageReactions
                messageServers)
              (.afterTime
                targetBefore
                selectedAction
                selectedReaction
                targetAfter
                targetDispatch)
              (.dispatchReady
                targetBefore
                selectedAction
                selectedReaction
                targetAfter
                targetDispatch) :=
          LF.detailedMicrostep_to_tauSteps
            hMicrostepDetailedStep

        have hConsumeDetailedStep :
            LF.DetailedMultiStoreStep
              declaredVariables
              (Translation.compileLogicalActions
                messageServers)
              (Translation.compileMessageReactions
                messageServers)
              (.dispatchReady
                targetBefore
                selectedAction
                selectedReaction
                targetAfter
                targetDispatch)
              (.consume
                selectedAction
                selectedReaction)
              (.stable targetAfter) :=
          LF.DetailedMultiStoreStep.consumeReady
            targetDispatch

        have hTargetWeakStep :
            LF.DetailedWeakStep
              declaredVariables
              (Translation.compileLogicalActions
                messageServers)
              (Translation.compileMessageReactions
                messageServers)
              (.afterTime
                targetBefore
                selectedAction
                selectedReaction
                targetAfter
                targetDispatch)
              (.consume
                selectedAction
                selectedReaction)
              (.stable targetAfter) := by

          exact
            Common.WeakStep.visible
              (LF.detailedConsume_visible
                selectedAction
                selectedReaction)
              hInternalPrefix
              hConsumeDetailedStep
              (Common.TauSteps.refl
              (LF.DetailedMultiStoreState.stable
                targetAfter))

        exact
          ⟨
            .consume
              selectedAction
              selectedReaction,
            .stable targetAfter,
            hTargetWeakStep,
            DirectLFDetailedLabelCorresponds.consume
              hWitness.selectedOccurrence
              hWitness.selectedHandler,
            DetailedStateCorresponds.stable
              hWitness.afterState
          ⟩

/--
Forward weak simulation for DTR consumption when both semantic layers are
already dispatch-ready.

LF performs the corresponding visible reaction-firing transition directly.
-/
theorem directLFDetailedRuntime_consume_ready_forward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    {targetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter}
    (hStates :
      DirectLFDetailedRuntimeStateCorresponds
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
    DirectLFDetailedForwardMatch
      declaredVariables
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

      have hTargetDetailedStep :
          LF.DetailedMultiStoreStep
            declaredVariables
            (Translation.compileLogicalActions
              messageServers)
            (Translation.compileMessageReactions
              messageServers)
            (.dispatchReady
              targetBefore
              selectedAction
              selectedReaction
              targetAfter
              targetDispatch)
            (.consume
              selectedAction
              selectedReaction)
            (.stable targetAfter) :=
        LF.DetailedMultiStoreStep.consumeReady
          targetDispatch

      exact
        ⟨
          .consume
            selectedAction
            selectedReaction,
          .stable targetAfter,
          LF.detailedConsume_is_weak
            hTargetDetailedStep,
          DirectLFDetailedLabelCorresponds.consume
            hWitness.selectedOccurrence
            hWitness.selectedHandler,
          DetailedStateCorresponds.stable
            hWitness.afterState
        ⟩

/--
Forward weak simulation for a same-metric-time DTR consumption transition.

The corresponding LF dispatch either fires at the current complete tag or
first advances internally to a later microstep.

Both possibilities produce one weak visible LF consumption transition.
-/

theorem directLFDetailedRuntime_consumeNow_forward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {selectedServer : DTR.MessageServer}
    {targetBefore : LF.StoreState}
    (hSourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        selectedServer
        sourceAfter)
    (hSameSourceTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime)
    (hStates :
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DirectLFDetailedForwardMatch
      declaredVariables
      messageServers
      (.consume
        selectedMessage
        selectedServer)
      (.stable sourceAfter)
      (.stable targetBefore) := by

  have hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    directLFDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     hWitness⟩ :=
      directLFDetailedRuntime_dispatch_forward
        hSourceDispatch
        hRuntime

  have hSameTargetTime :
      targetBefore.currentTag.time =
        targetAfter.currentTag.time := by

    calc
      targetBefore.currentTag.time =
          sourceBefore.currentTime :=
        hWitness.beforeState.states.currentTime

      _ =
          sourceAfter.currentTime :=
        hSameSourceTime

      _ =
          targetAfter.currentTag.time :=
        hWitness.afterState.states.currentTime.symm

  have hMicrostepOrder :
      targetBefore.currentTag.microstep ≤
        targetAfter.currentTag.microstep :=
    lfMultiStoreDispatch_microstep_le_of_sameTime
      hTargetDispatch
      hSameTargetTime

  rcases
      Nat.lt_or_eq_of_le
        hMicrostepOrder
    with
      hLaterMicrostep |
      hSameMicrostep

  · have hMicrostepDetailedStep :
        LF.DetailedMultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          (.stable targetBefore)
          (.microstepAdvance
            targetBefore.currentTag
            targetAfter.currentTag)
          (.dispatchReady
            targetBefore
            selectedAction
            (Translation.compileMessageReaction
              selectedServer)
            targetAfter
            hTargetDispatch) :=
      LF.DetailedMultiStoreStep.microstepSameTime
        hTargetDispatch
        hSameTargetTime
        hLaterMicrostep

    have hInternalPrefix :
        LF.DetailedTauSteps
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          (.stable targetBefore)
          (.dispatchReady
            targetBefore
            selectedAction
            (Translation.compileMessageReaction
              selectedServer)
            targetAfter
            hTargetDispatch) :=
      LF.detailedMicrostep_to_tauSteps
        hMicrostepDetailedStep

    have hConsumeDetailedStep :
        LF.DetailedMultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          (.dispatchReady
            targetBefore
            selectedAction
            (Translation.compileMessageReaction
              selectedServer)
            targetAfter
            hTargetDispatch)
          (.consume
            selectedAction
            (Translation.compileMessageReaction
              selectedServer))
          (.stable targetAfter) :=
      LF.DetailedMultiStoreStep.consumeReady
        hTargetDispatch

    have hTargetWeakStep :
        LF.DetailedWeakStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          (.stable targetBefore)
          (.consume
            selectedAction
            (Translation.compileMessageReaction
              selectedServer))
          (.stable targetAfter) := by

      exact
        Common.WeakStep.visible
          (LF.detailedConsume_visible
            selectedAction
            (Translation.compileMessageReaction
              selectedServer))
          hInternalPrefix
          hConsumeDetailedStep
          (Common.TauSteps.refl
            (LF.DetailedMultiStoreState.stable
              targetAfter))

    exact
      ⟨.consume
         selectedAction
         (Translation.compileMessageReaction
           selectedServer),
       .stable targetAfter,
       hTargetWeakStep,
       DirectLFDetailedLabelCorresponds.consume
         hWitness.selectedOccurrence
         hWitness.selectedHandler,
       DetailedStateCorresponds.stable
         hWitness.afterState⟩

  · have hTargetDetailedStep :
        LF.DetailedMultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          (.stable targetBefore)
          (.consume
            selectedAction
            (Translation.compileMessageReaction
              selectedServer))
          (.stable targetAfter) :=
      LF.DetailedMultiStoreStep.consumeNow
        hTargetDispatch
        hSameTargetTime
        hSameMicrostep

    exact
      ⟨.consume
         selectedAction
         (Translation.compileMessageReaction
           selectedServer),
       .stable targetAfter,
       LF.detailedConsume_is_weak
         hTargetDetailedStep,
       DirectLFDetailedLabelCorresponds.consume
         hWitness.selectedOccurrence
         hWitness.selectedHandler,
       DetailedStateCorresponds.stable
         hWitness.afterState⟩

/--
Every DirectLF runtime forward match contains a generated-LF destination state that
corresponds to the source destination state.
-/
theorem DirectLFDetailedForwardMatch.target_corresponds
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceLabel : DTR.DetailedMultiStoreLabel}
    {sourceAfter :
      DTR.DetailedMultiStoreState
        messageServers}
    {targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    (hMatch :
      DirectLFDetailedForwardMatch
        declaredVariables
        messageServers
        sourceLabel
        sourceAfter
        targetBefore) :
    ∃ targetAfter :
        LF.DetailedMultiStoreState
          (Translation.compileMessageReactions
            messageServers),
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
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
