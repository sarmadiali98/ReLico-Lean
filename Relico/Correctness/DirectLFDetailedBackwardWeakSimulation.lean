import Relico.Correctness.DirectLFDetailedForwardWeakSimulation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
One DirectLF runtime backward weak-simulation match.

The proposition packages a DTR weak transition matching one generated-LF
detailed label and preserves DirectLF detailed runtime-state correspondence.
-/
def DirectLFDetailedBackwardMatch
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (targetLabel : LF.DetailedMultiStoreLabel)
    (targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers))
    (sourceBefore :
      DTR.DetailedMultiStoreState
        messageServers) :
    Prop :=
  ∃ sourceLabel : DTR.DetailedMultiStoreLabel,
    ∃ sourceAfter :
        DTR.DetailedMultiStoreState
          messageServers,
      DTR.DetailedWeakStep
          declaredVariables
          messageServers
          sourceBefore
          sourceLabel
          sourceAfter ∧
        DirectLFDetailedLabelCorresponds
          sourceLabel
          targetLabel ∧
        DirectLFDetailedRuntimeStateCorresponds
          messageServers
          sourceAfter
          targetAfter

/--
Backward weak simulation for one generated-LF statement transition.
-/

theorem directLFDetailedRuntime_statement_backward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {targetLabel : LF.Label}
    (hTargetStep :
      LF.MultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hStatementAppend :
      DirectLFStatementAppendCompatible
        messageServers
        sourceBefore
        targetBefore)
    (hSourceBodyWellFormed :
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceBefore.activeBody) :
    DirectLFDetailedBackwardMatch
      declaredVariables
      messageServers
      LF.DetailedMultiStoreLabel.tau
      (.stable targetAfter)
      (.stable sourceBefore) := by

  have hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    directLFDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨_sourceLabel,
     sourceAfter,
     hSourceStep,
     _hLabels,
     hAfter⟩ :=
      directLF_multiStore_step_backward_runtime
        hTargetStep
        hRuntime
        hStatementAppend
        hSourceBodyWellFormed

  have hDetailedStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        (.stable sourceBefore)
        .tau
        (.stable sourceAfter) :=
    DTR.DetailedMultiStoreStep.statement
      hSourceStep

  exact
    ⟨DTR.DetailedMultiStoreLabel.tau,
     DTR.DetailedMultiStoreState.stable
       sourceAfter,
     DTR.detailedWeakStep_of_step
       hDetailedStep,
     DirectLFDetailedLabelCorresponds.tau,
     directLFDetailedRuntime_stable_iff.mpr
       hAfter⟩

/--
Backward weak simulation for visible LF metric-time progression.

The established backward dispatch theorem reconstructs the selected source
message and server. Stable-state correspondence then identifies both metric
time endpoints.
-/

theorem directLFDetailedRuntime_timeAdvance_backward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hTargetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        selectedAction
        selectedReaction
        targetAfter)
    (hTargetFuture :
      targetBefore.currentTag.time <
        targetAfter.currentTag.time)
    (hStates :
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DirectLFDetailedBackwardMatch
      declaredVariables
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
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    directLFDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedMessage,
     sourceServer,
     sourceAfter,
     hSourceDispatch,
     hWitness⟩ :=
      directLFDetailedRuntime_dispatch_backward
        hTargetDispatch
        hRuntime

  have hSourceFuture :
      sourceBefore.currentTime <
        sourceAfter.currentTime := by

    calc
      sourceBefore.currentTime =
          targetBefore.currentTag.time :=
        hWitness.beforeState.states.currentTime.symm

      _ <
          targetAfter.currentTag.time :=
        hTargetFuture

      _ =
          sourceAfter.currentTime :=
        hWitness.afterState.states.currentTime

  have hSourceDetailedStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        (.stable sourceBefore)
        (.timeAdvance
          sourceBefore.currentTime
          sourceAfter.currentTime)
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter
          hSourceDispatch) :=
    DTR.DetailedMultiStoreStep.timeAdvance
      hSourceDispatch
      hSourceFuture

  exact
    ⟨DTR.DetailedMultiStoreLabel.timeAdvance
       sourceBefore.currentTime
       sourceAfter.currentTime,
     DTR.DetailedMultiStoreState.dispatchReady
       sourceBefore
       selectedMessage
       sourceServer
       sourceAfter
       hSourceDispatch,
     DTR.detailedTimeAdvance_is_weak
       hSourceDetailedStep,
     DirectLFDetailedLabelCorresponds.timeAdvance
       hWitness.beforeState.states.currentTime
       hWitness.afterState.states.currentTime,
     directLFDetailedRuntime_futureAfterTime
       hSourceFuture
       hWitness⟩

/--
Backward matching for the internal LF microstep following future metric-time
progression.

DTR remains in its dispatch-ready phase and performs a reflexive weak-τ step.
-/

theorem directLFDetailedRuntime_microstepAfterTime_backward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {sourceServer : DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        sourceServer
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
    (hPositiveMicrostep :
      0 <
        targetAfter.currentTag.microstep)
    (hStates :
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    DirectLFDetailedBackwardMatch
      declaredVariables
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
        sourceServer
        sourceAfter
        sourceDispatch) := by

  cases hStates with

  | futureAfterTime
      hSourceFuture
      _hTargetFuture
      hWitness =>

      exact
        ⟨DTR.DetailedMultiStoreLabel.tau,
         DTR.DetailedMultiStoreState.dispatchReady
           sourceBefore
           selectedMessage
           sourceServer
           sourceAfter
           sourceDispatch,
         DTR.detailedWeakTau_refl
           (DTR.DetailedMultiStoreState.dispatchReady
             sourceBefore
             selectedMessage
             sourceServer
             sourceAfter
             sourceDispatch),
         DirectLFDetailedLabelCorresponds.microstep
           {
             time :=
               targetAfter.currentTag.time
             microstep :=
               0
           }
           targetAfter.currentTag,
         directLFDetailedRuntime_futureReady
           hSourceFuture
           hPositiveMicrostep
           hWitness⟩

/--
Backward matching for a same-time LF microstep transition from a stable state.

The generated-LF dispatch is reconstructed as a source dispatch. DTR then
stutters while LF advances internally to its dispatch-ready phase.
-/

theorem directLFDetailedRuntime_microstepSameTime_backward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hTargetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
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
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DirectLFDetailedBackwardMatch
      declaredVariables
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
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    directLFDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedMessage,
     sourceServer,
     sourceAfter,
     hSourceDispatch,
     hWitness⟩ :=
      directLFDetailedRuntime_dispatch_backward
        hTargetDispatch
        hRuntime

  have hSourceSameTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime := by

    calc
      sourceBefore.currentTime =
          targetBefore.currentTag.time :=
        hWitness.beforeState.states.currentTime.symm

      _ =
          targetAfter.currentTag.time :=
        hTargetSameTime

      _ =
          sourceAfter.currentTime :=
        hWitness.afterState.states.currentTime

  exact
    ⟨DTR.DetailedMultiStoreLabel.tau,
     DTR.DetailedMultiStoreState.stable
       sourceBefore,
     DTR.detailedWeakTau_refl
       (DTR.DetailedMultiStoreState.stable
         sourceBefore),
     DirectLFDetailedLabelCorresponds.microstep
       targetBefore.currentTag
       targetAfter.currentTag,
     directLFDetailedRuntime_sameTimeMicrostepAhead
       hSourceDispatch
       hSourceSameTime
       hLaterMicrostep
       hWitness⟩

/--
Backward matching for LF consumption directly after a future time transition
whose destination microstep is zero.
-/

theorem directLFDetailedRuntime_consumeAfterTimeZero_backward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {sourceServer : DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        sourceServer
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
    (_hZeroMicrostep :
      targetAfter.currentTag.microstep =
        0)
    (hStates :
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        (.dispatchReady
          sourceBefore
          selectedMessage
          sourceServer
          sourceAfter
          sourceDispatch)
        (.afterTime
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    DirectLFDetailedBackwardMatch
      declaredVariables
      messageServers
      (.consume
        selectedAction
        selectedReaction)
      (.stable targetAfter)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceServer
        sourceAfter
        sourceDispatch) := by

  cases hStates with

  | futureAfterTime
      _hSourceFuture
      _hTargetFuture
      hWitness =>

      have hSourceDetailedStep :
          DTR.DetailedMultiStoreStep
            declaredVariables
            messageServers
            (.dispatchReady
              sourceBefore
              selectedMessage
              sourceServer
              sourceAfter
              sourceDispatch)
            (.consume
              selectedMessage
              sourceServer)
            (.stable sourceAfter) :=
        DTR.DetailedMultiStoreStep.consumeReady
          sourceDispatch

      exact
        ⟨DTR.DetailedMultiStoreLabel.consume
           selectedMessage
           sourceServer,
         DTR.DetailedMultiStoreState.stable
           sourceAfter,
         DTR.detailedConsume_is_weak
           hSourceDetailedStep,
         DirectLFDetailedLabelCorresponds.consume
           hWitness.selectedOccurrence
           hWitness.selectedHandler,
         directLFDetailedRuntime_stable_iff.mpr
           hWitness.afterState⟩

/--
Backward matching for LF consumption from a future dispatch-ready phase.
-/

theorem directLFDetailedRuntime_consumeReadyFuture_backward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    {sourceServer : DTR.MessageServer}
    {sourceDispatch :
      DTR.MultiStoreDispatchStep
        messageServers
        sourceBefore
        selectedMessage
        sourceServer
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
          sourceServer
          sourceAfter
          sourceDispatch)
        (.dispatchReady
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    DirectLFDetailedBackwardMatch
      declaredVariables
      messageServers
      (.consume
        selectedAction
        selectedReaction)
      (.stable targetAfter)
      (.dispatchReady
        sourceBefore
        selectedMessage
        sourceServer
        sourceAfter
        sourceDispatch) := by

  cases hStates with

  | futureReady
      _hSourceFuture
      _hTargetFuture
      _hPositiveMicrostep
      hWitness =>

      have hSourceDetailedStep :
          DTR.DetailedMultiStoreStep
            declaredVariables
            messageServers
            (.dispatchReady
              sourceBefore
              selectedMessage
              sourceServer
              sourceAfter
              sourceDispatch)
            (.consume
              selectedMessage
              sourceServer)
            (.stable sourceAfter) :=
        DTR.DetailedMultiStoreStep.consumeReady
          sourceDispatch

      exact
        ⟨DTR.DetailedMultiStoreLabel.consume
           selectedMessage
           sourceServer,
         DTR.DetailedMultiStoreState.stable
           sourceAfter,
         DTR.detailedConsume_is_weak
           hSourceDetailedStep,
         DirectLFDetailedLabelCorresponds.consume
           hWitness.selectedOccurrence
           hWitness.selectedHandler,
         directLFDetailedRuntime_stable_iff.mpr
           hWitness.afterState⟩

/--
Backward matching for LF consumption from a same-time dispatch-ready phase.

The related DTR state is still stable, so DTR performs `consumeNow`.
-/

theorem directLFDetailedRuntime_consumeReadySameTime_backward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
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
        (.stable sourceBefore)
        (.dispatchReady
          targetBefore
          selectedAction
          selectedReaction
          targetAfter
          targetDispatch)) :
    DirectLFDetailedBackwardMatch
      declaredVariables
      messageServers
      (.consume
        selectedAction
        selectedReaction)
      (.stable targetAfter)
      (.stable sourceBefore) := by

  have hSourceData :
      ∃ sourceAfter : DTR.StoreState,
        ∃ selectedMessage : DTR.PendingMessage,
          ∃ sourceServer : DTR.MessageServer,
            ∃ sourceDispatch :
                DTR.MultiStoreDispatchStep
                  messageServers
                  sourceBefore
                  selectedMessage
                  sourceServer
                  sourceAfter,
              sourceBefore.currentTime =
                  sourceAfter.currentTime ∧
                DirectLFDetailedRuntimeDispatchWitnessCorresponds
                  messageServers
                  sourceBefore
                  selectedMessage
                  sourceServer
                  sourceAfter
                  targetBefore
                  selectedAction
                  selectedReaction
                  targetAfter := by

    cases hStates with

    | sameTimeMicrostepAhead
        sourceDispatch
        hSourceSameTime
        _hTargetSameTime
        _hLaterMicrostep
        hWitness =>

        exact
          ⟨_,
           _,
           _,
           sourceDispatch,
           hSourceSameTime,
           hWitness⟩

  rcases hSourceData with
    ⟨sourceAfter,
     selectedMessage,
     sourceServer,
     sourceDispatch,
     hSourceSameTime,
     hWitness⟩

  have hSourceDetailedStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        (.stable sourceBefore)
        (.consume
          selectedMessage
          sourceServer)
        (.stable sourceAfter) :=
    DTR.DetailedMultiStoreStep.consumeNow
      sourceDispatch
      hSourceSameTime

  exact
    ⟨DTR.DetailedMultiStoreLabel.consume
       selectedMessage
       sourceServer,
     DTR.DetailedMultiStoreState.stable
       sourceAfter,
     DTR.detailedConsume_is_weak
       hSourceDetailedStep,
     DirectLFDetailedLabelCorresponds.consume
       hWitness.selectedOccurrence
       hWitness.selectedHandler,
     directLFDetailedRuntime_stable_iff.mpr
       hWitness.afterState⟩

/--
Backward weak simulation for direct LF reaction firing at the current complete
tag.
-/

theorem directLFDetailedRuntime_consumeNow_backward_weak
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {selectedAction : LF.PendingAction}
    {selectedReaction : LF.Reaction}
    (hTargetDispatch :
      LF.MultiStoreDispatchStep
        (Translation.compileMessageReactions
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
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore)) :
    DirectLFDetailedBackwardMatch
      declaredVariables
      messageServers
      (.consume
        selectedAction
        selectedReaction)
      (.stable targetAfter)
      (.stable sourceBefore) := by

  have hRuntime :
      DirectLFRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    directLFDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨selectedMessage,
     sourceServer,
     sourceAfter,
     hSourceDispatch,
     hWitness⟩ :=
      directLFDetailedRuntime_dispatch_backward
        hTargetDispatch
        hRuntime

  have hSourceSameTime :
      sourceBefore.currentTime =
        sourceAfter.currentTime := by

    calc
      sourceBefore.currentTime =
          targetBefore.currentTag.time :=
        hWitness.beforeState.states.currentTime.symm

      _ =
          targetAfter.currentTag.time :=
        hTargetSameTime

      _ =
          sourceAfter.currentTime :=
        hWitness.afterState.states.currentTime

  have hSourceDetailedStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        (.stable sourceBefore)
        (.consume
          selectedMessage
          sourceServer)
        (.stable sourceAfter) :=
    DTR.DetailedMultiStoreStep.consumeNow
      hSourceDispatch
      hSourceSameTime

  exact
    ⟨DTR.DetailedMultiStoreLabel.consume
       selectedMessage
       sourceServer,
     DTR.DetailedMultiStoreState.stable
       sourceAfter,
     DTR.detailedConsume_is_weak
       hSourceDetailedStep,
     DirectLFDetailedLabelCorresponds.consume
       hWitness.selectedOccurrence
       hWitness.selectedHandler,
     directLFDetailedRuntime_stable_iff.mpr
       hWitness.afterState⟩

/--
Every DirectLF runtime backward match contains a DTR destination state corresponding
to the generated-LF destination state.
-/
theorem DirectLFDetailedBackwardMatch.source_corresponds
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {targetLabel : LF.DetailedMultiStoreLabel}
    {targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    {sourceBefore :
      DTR.DetailedMultiStoreState
        messageServers}
    (hMatch :
      DirectLFDetailedBackwardMatch
        declaredVariables
        messageServers
        targetLabel
        targetAfter
        sourceBefore) :
    ∃ sourceAfter :
        DTR.DetailedMultiStoreState
          messageServers,
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        sourceAfter
        targetAfter := by

  rcases hMatch with
    ⟨_sourceLabel,
     sourceAfter,
     _hWeakStep,
     _hLabels,
     hStates⟩

  exact
    ⟨sourceAfter,
     hStates⟩

end Correctness
end Relico
