import Relico.Correctness.DetailedObservableWeakExecution

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
The phase-specific premise needed to match one exact detailed DTR step from a
given generated-LF detailed state.

The predicate also excludes phase combinations not covered by the forward
interface. In particular, a same-time LF microstep-ahead state is not accepted
as the starting point of a forward source step.
-/
def ConcreteDetailedForwardPhaseCompatible
    {messageServers : List DTR.MessageServer}
    (sourceBefore :
      DTR.DetailedMultiStoreState messageServers)
    (sourceLabel :
      DTR.DetailedMultiStoreLabel)
    (sourceAfter :
      DTR.DetailedMultiStoreState messageServers)
    (targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)) :
    Prop :=

  match
      sourceBefore,
      sourceLabel,
      sourceAfter,
      targetBefore
    with

  | .stable _,
    .tau,
    .stable _,
    .stable _ =>
      True

  | .stable _,
    .timeAdvance _ _,
    .dispatchReady
      _
      selectedMessage
      _
      sourceAfterState
      _,
    .stable targetBeforeState =>
      StoreForwardDispatchCompatible
        selectedMessage
        sourceAfterState.pendingMessages
        targetBeforeState

  | .dispatchReady _ _ _ _ _,
    .consume _ _,
    .stable _,
    .afterTime _ _ _ _ _ =>
      True

  | .dispatchReady _ _ _ _ _,
    .consume _ _,
    .stable _,
    .dispatchReady _ _ _ _ _ =>
      True

  | .stable _,
    .consume selectedMessage _,
    .stable sourceAfterState,
    .stable targetBeforeState =>
      StoreForwardDispatchCompatible
        selectedMessage
        sourceAfterState.pendingMessages
        targetBeforeState

  | _, _, _, _ =>
      False

/--
The phase-specific premise needed to match one exact detailed generated-LF
step from a given DTR detailed state.

The structural source-body and target zero-microstep premises remain explicit.
They will be derived from model-level invariants in the following checkpoint.
-/
def ConcreteDetailedBackwardPhaseCompatible
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    (sourceBefore :
      DTR.DetailedMultiStoreState messageServers)
    (targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers))
    (targetLabel :
      LF.DetailedMultiStoreLabel)
    (targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)) :
    Prop :=

  match
      sourceBefore,
      targetBefore,
      targetLabel,
      targetAfter
    with

  | .stable sourceBeforeState,
    .stable _,
    .tau,
    .stable _ =>
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceBeforeState.activeBody

  | .stable _,
    .stable targetBeforeState,
    .timeAdvance _ _,
    .afterTime _ _ _ _ _ =>
      LF.StoreState.PendingMicrostepsZero
        targetBeforeState

  | .dispatchReady _ _ _ _ _,
    .afterTime _ _ _ _ _,
    .microstepAdvance _ _,
    .dispatchReady _ _ _ _ _ =>
      True

  | .dispatchReady _ _ _ _ _,
    .afterTime _ _ _ _ _,
    .consume _ _,
    .stable _ =>
      True

  | .stable _,
    .stable targetBeforeState,
    .microstepAdvance _ _,
    .dispatchReady _ _ _ _ _ =>
      LF.StoreState.PendingMicrostepsZero
        targetBeforeState

  | .dispatchReady _ _ _ _ _,
    .dispatchReady _ _ _ _ _,
    .consume _ _,
    .stable _ =>
      True

  | .stable _,
    .dispatchReady _ _ _ _ _,
    .consume _ _,
    .stable _ =>
      True

  | .stable _,
    .stable targetBeforeState,
    .consume _ _,
    .stable _ =>
      LF.StoreState.PendingMicrostepsZero
        targetBeforeState

  | _, _, _, _ =>
      False

/--
The phase-indexed interface lifts any phase-compatible exact DTR detailed step
to one generated-LF weak match.
-/
theorem ConcreteDetailedPhaseWeakBisimulation.forwardStep
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    (hBisimulation :
      ConcreteDetailedPhaseWeakBisimulation
        declaredVariables
        messageServers)
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState messageServers}
    {sourceLabel :
      DTR.DetailedMultiStoreLabel}
    {targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    (hSourceStep :
      DTR.DetailedMultiStoreStep
        declaredVariables
        messageServers
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      ConcreteDetailedForwardPhaseCompatible
        sourceBefore
        sourceLabel
        sourceAfter
        targetBefore) :
    ConcreteDetailedForwardMatch
      declaredVariables
      messageServers
      sourceLabel
      sourceAfter
      targetBefore := by

  cases hSourceStep with

  | statement hStatement =>
      cases targetBefore with

      | stable targetBeforeState =>
          exact
            hBisimulation.forwardStatementMatch
              _ _ _ _
              hStatement
              hStates

      | afterTime
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            ConcreteDetailedForwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            ConcreteDetailedForwardPhaseCompatible
          ] at hCompatible

  | timeAdvance hSourceDispatch hFuture =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage
        selectedServer

      cases targetBefore with

      | stable targetBeforeState =>
          have hScheduler :
              StoreForwardDispatchCompatible
                selectedMessage
                sourceAfterState.pendingMessages
                targetBeforeState := by

            simpa [
              ConcreteDetailedForwardPhaseCompatible
            ] using
              hCompatible

          exact
            hBisimulation.forwardTimeAdvanceMatch
              (sourceBefore :=
                sourceBeforeState)
              (sourceAfter :=
                sourceAfterState)
              (selectedMessage :=
                selectedMessage)
              (selectedServer :=
                selectedServer)
              (targetBefore :=
                targetBeforeState)
              (sourceDispatch :=
                hSourceDispatch)
              hFuture
              hStates
              hScheduler

      | afterTime
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            ConcreteDetailedForwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            ConcreteDetailedForwardPhaseCompatible
          ] at hCompatible

  | consumeReady hSourceDispatch =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage
        selectedServer

      cases targetBefore with

      | stable targetBeforeState =>
          simp [
            ConcreteDetailedForwardPhaseCompatible
          ] at hCompatible

      | afterTime
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          exact
            hBisimulation.forwardConsumeAfterTimeMatch
              (sourceBefore :=
                sourceBeforeState)
              (sourceAfter :=
                sourceAfterState)
              (selectedMessage :=
                selectedMessage)
              (selectedServer :=
                selectedServer)
              (sourceDispatch :=
                hSourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (selectedReaction :=
                selectedReaction)
              (targetDispatch :=
                targetDispatch)
              hStates

      | dispatchReady
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          exact
            hBisimulation.forwardConsumeReadyMatch
              (sourceBefore :=
                sourceBeforeState)
              (sourceAfter :=
                sourceAfterState)
              (selectedMessage :=
                selectedMessage)
              (selectedServer :=
                selectedServer)
              (sourceDispatch :=
                hSourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (selectedReaction :=
                selectedReaction)
              (targetDispatch :=
                targetDispatch)
              hStates

  | consumeNow hSourceDispatch hSameTime =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage
        selectedServer

      cases targetBefore with

      | stable targetBeforeState =>
          have hScheduler :
              StoreForwardDispatchCompatible
                selectedMessage
                sourceAfterState.pendingMessages
                targetBeforeState := by

            simpa [
              ConcreteDetailedForwardPhaseCompatible
            ] using
              hCompatible

          exact
            hBisimulation.forwardConsumeNowMatch
              (sourceBefore :=
                sourceBeforeState)
              (sourceAfter :=
                sourceAfterState)
              (selectedMessage :=
                selectedMessage)
              (selectedServer :=
                selectedServer)
              (targetBefore :=
                targetBeforeState)
              hSourceDispatch
              hSameTime
              hStates
              hScheduler

      | afterTime
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            ConcreteDetailedForwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            ConcreteDetailedForwardPhaseCompatible
          ] at hCompatible

/--
The phase-indexed interface lifts any phase-compatible exact generated-LF
detailed step to one DTR weak match.
-/
theorem ConcreteDetailedPhaseWeakBisimulation.backwardStep
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    (hBisimulation :
      ConcreteDetailedPhaseWeakBisimulation
        declaredVariables
        messageServers)
    {sourceBefore :
      DTR.DetailedMultiStoreState messageServers}
    {targetBefore targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    {targetLabel :
      LF.DetailedMultiStoreLabel}
    (hTargetStep :
      LF.DetailedMultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      ConcreteDetailedBackwardPhaseCompatible
        (declaredVariables :=
          declaredVariables)
        sourceBefore
        targetBefore
        targetLabel
        targetAfter) :
    ConcreteDetailedBackwardMatch
      declaredVariables
      messageServers
      targetLabel
      targetAfter
      sourceBefore := by

  cases hTargetStep with

  | statement hStatement =>
      cases sourceBefore with

      | stable sourceBeforeState =>
          have hSourceBody :
              DTR.Body.MultiStoreWellFormed
                declaredVariables
                (DTR.messageServerNames
                  messageServers)
                sourceBeforeState.activeBody := by

            simpa [
              ConcreteDetailedBackwardPhaseCompatible
            ] using
              hCompatible

          exact
            hBisimulation.backwardStatementMatch
              _ _ _ _
              hStatement
              hStates
              hSourceBody

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          simp [
            ConcreteDetailedBackwardPhaseCompatible
          ] at hCompatible

  | timeAdvance hTargetDispatch hFuture =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction
        selectedReaction

      cases sourceBefore with

      | stable sourceBeforeState =>
          exact
            hBisimulation.backwardTimeAdvanceMatch
              (sourceBefore :=
                sourceBeforeState)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (selectedReaction :=
                selectedReaction)
              (targetDispatch :=
                hTargetDispatch)
              hFuture
              hStates
              (by
                simpa [
                  ConcreteDetailedBackwardPhaseCompatible
                ] using
                  hCompatible)

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          simp [
            ConcreteDetailedBackwardPhaseCompatible
          ] at hCompatible

  | microstepAfterTime
      hTargetDispatch
      hPositiveMicrostep =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction
        selectedReaction

      cases sourceBefore with

      | stable sourceBeforeState =>
          simp [
            ConcreteDetailedBackwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          exact
            hBisimulation.backwardMicrostepAfterTimeMatch
              (sourceBefore :=
                sourceBeforeState)
              (sourceAfter :=
                sourceAfterState)
              (selectedMessage :=
                selectedMessage)
              (sourceServer :=
                selectedServer)
              (sourceDispatch :=
                sourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (selectedReaction :=
                selectedReaction)
              (targetDispatch :=
                hTargetDispatch)
              hPositiveMicrostep
              hStates

  | consumeAfterTimeZero
      hTargetDispatch
      hZeroMicrostep =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction
        selectedReaction

      cases sourceBefore with

      | stable sourceBeforeState =>
          simp [
            ConcreteDetailedBackwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          exact
            hBisimulation.backwardConsumeAfterTimeZeroMatch
              (sourceBefore :=
                sourceBeforeState)
              (sourceAfter :=
                sourceAfterState)
              (selectedMessage :=
                selectedMessage)
              (sourceServer :=
                selectedServer)
              (sourceDispatch :=
                sourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (selectedReaction :=
                selectedReaction)
              (targetDispatch :=
                hTargetDispatch)
              hZeroMicrostep
              hStates

  | microstepSameTime
      hTargetDispatch
      hSameTime
      hLaterMicrostep =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction
        selectedReaction

      cases sourceBefore with

      | stable sourceBeforeState =>
          exact
            hBisimulation.backwardMicrostepSameTimeMatch
              (sourceBefore :=
                sourceBeforeState)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (selectedReaction :=
                selectedReaction)
              (targetDispatch :=
                hTargetDispatch)
              hSameTime
              hLaterMicrostep
              hStates
              (by
                simpa [
                  ConcreteDetailedBackwardPhaseCompatible
                ] using
                  hCompatible)

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          simp [
            ConcreteDetailedBackwardPhaseCompatible
          ] at hCompatible

  | consumeReady hTargetDispatch =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction
        selectedReaction

      cases sourceBefore with

      | stable sourceBeforeState =>
          exact
            hBisimulation.backwardConsumeReadySameTimeMatch
              (sourceBefore :=
                sourceBeforeState)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (selectedReaction :=
                selectedReaction)
              (targetDispatch :=
                hTargetDispatch)
              hStates

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          exact
            hBisimulation.backwardConsumeReadyFutureMatch
              (sourceBefore :=
                sourceBeforeState)
              (sourceAfter :=
                sourceAfterState)
              (selectedMessage :=
                selectedMessage)
              (sourceServer :=
                selectedServer)
              (sourceDispatch :=
                sourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (selectedReaction :=
                selectedReaction)
              (targetDispatch :=
                hTargetDispatch)
              hStates

  | consumeNow
      hTargetDispatch
      hSameTime
      hSameMicrostep =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction
        selectedReaction

      cases sourceBefore with

      | stable sourceBeforeState =>
          exact
            hBisimulation.backwardConsumeNowMatch
              (sourceBefore :=
                sourceBeforeState)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (selectedReaction :=
                selectedReaction)
              hTargetDispatch
              hSameTime
              hSameMicrostep
              hStates
              (by
                simpa [
                  ConcreteDetailedBackwardPhaseCompatible
                ] using
                  hCompatible)

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          simp [
            ConcreteDetailedBackwardPhaseCompatible
          ] at hCompatible

/--
Compatibility evidence indexed by an exact finite DTR detailed-label
sequence.

For each possible first-step decomposition, it supplies the current
phase-specific premise and a continuation compatible with every weak target
match that preserves label and state correspondence.
-/
def ConcreteDetailedForwardLabelsCompatible
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState messageServers)
    (sourceLabels :
      List DTR.DetailedMultiStoreLabel)
    (targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)) :
    Prop :=

  match sourceLabels with

  | [] =>
      sourceBefore =
        sourceAfter

  | sourceLabel :: sourceRemainingLabels =>
      ∀ sourceMiddle,
        DTR.DetailedMultiStoreStep
            declaredVariables
            messageServers
            sourceBefore
            sourceLabel
            sourceMiddle →
        DTR.DetailedMultiStoreSteps
            declaredVariables
            messageServers
            sourceMiddle
            sourceRemainingLabels
            sourceAfter →
        ConcreteDetailedForwardPhaseCompatible
            sourceBefore
            sourceLabel
            sourceMiddle
            targetBefore ∧
          ∀ {targetLabel targetMiddle},
            LF.DetailedWeakStep
                declaredVariables
                (Translation.compileLogicalActions
                  messageServers)
                (Translation.compileMessageReactions
                  messageServers)
                targetBefore
                targetLabel
                targetMiddle →
            ConcreteDetailedLabelCorresponds
                sourceLabel
                targetLabel →
            ConcreteDetailedStateCorresponds
                messageServers
                sourceMiddle
                targetMiddle →
            ConcreteDetailedForwardLabelsCompatible
              declaredVariables
              messageServers
              sourceMiddle
              sourceAfter
              sourceRemainingLabels
              targetMiddle

termination_by sourceLabels.length

/--
Compatibility for one concrete exact finite DTR detailed execution.
-/
def ConcreteDetailedForwardStepsCompatible
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStoreState messageServers}
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    (_hSteps :
      DTR.DetailedMultiStoreSteps
        declaredVariables
        messageServers
        sourceBefore
        sourceLabels
        sourceAfter)
    (targetBefore :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)) :
    Prop :=

  ConcreteDetailedForwardLabelsCompatible
    declaredVariables
    messageServers
    sourceBefore
    sourceAfter
    sourceLabels
    targetBefore

/--
Compatibility evidence indexed by an exact finite generated-LF detailed-label
sequence.

For each possible first-step decomposition, it supplies the current backward
phase premise and a continuation compatible with every weak source match that
preserves label and state correspondence.
-/
def ConcreteDetailedBackwardLabelsCompatible
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (sourceBefore :
      DTR.DetailedMultiStoreState messageServers)
    (targetBefore targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers))
    (targetLabels :
      List LF.DetailedMultiStoreLabel) :
    Prop :=

  match targetLabels with

  | [] =>
      targetBefore =
        targetAfter

  | targetLabel :: targetRemainingLabels =>
      ∀ targetMiddle,
        LF.DetailedMultiStoreStep
            declaredVariables
            (Translation.compileLogicalActions
              messageServers)
            (Translation.compileMessageReactions
              messageServers)
            targetBefore
            targetLabel
            targetMiddle →
        LF.DetailedMultiStoreSteps
            declaredVariables
            (Translation.compileLogicalActions
              messageServers)
            (Translation.compileMessageReactions
              messageServers)
            targetMiddle
            targetRemainingLabels
            targetAfter →
        ConcreteDetailedBackwardPhaseCompatible
            (declaredVariables :=
              declaredVariables)
            sourceBefore
            targetBefore
            targetLabel
            targetMiddle ∧
          ∀ {sourceLabel sourceMiddle},
            DTR.DetailedWeakStep
                declaredVariables
                messageServers
                sourceBefore
                sourceLabel
                sourceMiddle →
            ConcreteDetailedLabelCorresponds
                sourceLabel
                targetLabel →
            ConcreteDetailedStateCorresponds
                messageServers
                sourceMiddle
                targetMiddle →
            ConcreteDetailedBackwardLabelsCompatible
              declaredVariables
              messageServers
              sourceMiddle
              targetMiddle
              targetAfter
              targetRemainingLabels

termination_by targetLabels.length

/--
Compatibility for one concrete exact finite generated-LF detailed execution.
-/
def ConcreteDetailedBackwardStepsCompatible
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (sourceBefore :
      DTR.DetailedMultiStoreState messageServers)
    {targetBefore targetAfter :
      LF.DetailedMultiStoreState
        (Translation.compileMessageReactions
          messageServers)}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    (_hSteps :
      LF.DetailedMultiStoreSteps
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        targetLabels
        targetAfter) :
    Prop :=

  ConcreteDetailedBackwardLabelsCompatible
    declaredVariables
    messageServers
    sourceBefore
    targetBefore
    targetAfter
    targetLabels

/--
Conditional finite forward correspondence for exact detailed DTR executions.

The constructed generated-LF execution is weak. Representative weak labels
correspond pointwise, final detailed states correspond, and their observable
projections correspond.
-/
theorem concreteDetailedSteps_forward_of_compatible
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
      ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      ConcreteDetailedForwardStepsCompatible
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
            targetLabels) := by

  let hBisimulation :=
    concreteDetailed_phaseWeakBisimulation
      declaredVariables
      messageServers

  induction hSourceSteps generalizing targetBefore with

  | refl sourceState =>
      exact
        ⟨[],
         targetBefore,
         Common.WeakSteps.refl
           targetBefore,
         ConcreteDetailedWeakLabelTraceCorresponds.nil,
         hStates,
         ConcreteDetailedObservableTraceCorresponds.nil⟩

  | cons hHead hTail inductionHypothesis =>
      unfold
        ConcreteDetailedForwardStepsCompatible
        at hCompatible

      simp only [
        ConcreteDetailedForwardLabelsCompatible
      ] at hCompatible

      rcases
          hCompatible
            _
            hHead
            hTail
        with
          ⟨hHeadCompatible,
           hContinuation⟩

      rcases
          hBisimulation.forwardStep
            hHead
            hStates
            hHeadCompatible
        with
          ⟨targetHeadLabel,
           targetMiddle,
           hTargetHead,
           hHeadLabels,
           hMiddleStates⟩

      have hTailCompatible :
          ConcreteDetailedForwardStepsCompatible
            declaredVariables
            messageServers
            hTail
            targetMiddle := by

        exact
          hContinuation
            hTargetHead
            hHeadLabels
            hMiddleStates

      rcases
          inductionHypothesis
            hMiddleStates
            hTailCompatible
        with
          ⟨targetRemainingLabels,
           targetAfter,
           hTargetTail,
           hTailLabels,
           hFinalStates,
           hObservableTail⟩

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
         hTrace.observableProjection⟩

/--
Conditional finite backward correspondence for exact detailed generated-LF
executions.

The recovered DTR execution is weak. Representative weak labels correspond
pointwise, final detailed states correspond, and their observable projections
correspond.
-/
theorem concreteDetailedSteps_backward_of_compatible
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
      ConcreteDetailedStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      ConcreteDetailedBackwardStepsCompatible
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
            targetLabels) := by

  let hBisimulation :=
    concreteDetailed_phaseWeakBisimulation
      declaredVariables
      messageServers

  induction hTargetSteps generalizing sourceBefore with

  | refl targetState =>
      exact
        ⟨[],
         sourceBefore,
         Common.WeakSteps.refl
           sourceBefore,
         ConcreteDetailedWeakLabelTraceCorresponds.nil,
         hStates,
         ConcreteDetailedObservableTraceCorresponds.nil⟩

  | cons hHead hTail inductionHypothesis =>
      unfold
        ConcreteDetailedBackwardStepsCompatible
        at hCompatible

      simp only [
        ConcreteDetailedBackwardLabelsCompatible
      ] at hCompatible

      rcases
          hCompatible
            _
            hHead
            hTail
        with
          ⟨hHeadCompatible,
           hContinuation⟩

      rcases
          hBisimulation.backwardStep
            hHead
            hStates
            hHeadCompatible
        with
          ⟨sourceHeadLabel,
           sourceMiddle,
           hSourceHead,
           hHeadLabels,
           hMiddleStates⟩

      have hTailCompatible :
          ConcreteDetailedBackwardStepsCompatible
            declaredVariables
            messageServers
            sourceMiddle
            hTail := by

        exact
          hContinuation
            hSourceHead
            hHeadLabels
            hMiddleStates

      rcases
          inductionHypothesis
            hMiddleStates
            hTailCompatible
        with
          ⟨sourceRemainingLabels,
           sourceAfter,
           hSourceTail,
           hTailLabels,
           hFinalStates,
           hObservableTail⟩

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
         hTrace.observableProjection⟩

end Correctness
end Relico
