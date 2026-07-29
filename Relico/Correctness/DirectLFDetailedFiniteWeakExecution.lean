import Relico.DTR.DetailedWeakExecution
import Relico.LF.DetailedWeakExecution
import Relico.Correctness.DirectLFDetailedPhaseWeakBisimulation

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Phase-specific premise for matching one exact DTR detailed step with the
ordinary generated-LF detailed semantics.

The predicate excludes unsupported phase combinations. Statement execution
also exposes the append condition required to preserve DirectLF selection
compatibility after scheduling a new occurrence.
-/
def DirectLFDetailedForwardPhaseCompatible
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

  | .stable sourceBeforeState,
    .tau,
    .stable _,
    .stable targetBeforeState =>
      DirectLFStatementAppendCompatible
        messageServers
        sourceBeforeState
        targetBeforeState

  | .stable _,
    .timeAdvance _ _,
    .dispatchReady _ _ _ _ _,
    .stable _ =>
      True

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
    .consume _ _,
    .stable _,
    .stable _ =>
      True

  | _, _, _, _ =>
      False

/--
Phase-specific premise for matching one exact generated-LF detailed step with a
DTR weak step.

For statement execution it exposes both the occurrence-append condition and
source-body well-formedness. All admitted scheduler and target-only microstep
phases require no additional positive-delay or zero-microstep restriction.
-/
def DirectLFDetailedBackwardPhaseCompatible
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
    .stable targetBeforeState,
    .tau,
    .stable _ =>
      DirectLFStatementAppendCompatible
          messageServers
          sourceBeforeState
          targetBeforeState ∧
        DTR.Body.MultiStoreWellFormed
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          sourceBeforeState.activeBody

  | .stable _,
    .stable _,
    .timeAdvance _ _,
    .afterTime _ _ _ _ _ =>
      True

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
    .stable _,
    .microstepAdvance _ _,
    .dispatchReady _ _ _ _ _ =>
      True

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
    .stable _,
    .consume _ _,
    .stable _ =>
      True

  | _, _, _, _ =>
      False

theorem DirectLFDetailedPhaseWeakBisimulation.forwardStep
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    (hBisimulation :
      DirectLFDetailedPhaseWeakBisimulation
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
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      DirectLFDetailedForwardPhaseCompatible
        sourceBefore
        sourceLabel
        sourceAfter
        targetBefore) :
    DirectLFDetailedForwardMatch
      declaredVariables
      messageServers
      sourceLabel
      sourceAfter
      targetBefore := by

  cases hSourceStep with

  | statement hStatement =>
      rename_i
        sourceBeforeState
        sourceAfterState
        sourceStatementLabel

      cases targetBefore with

      | stable targetBeforeState =>
          have hStatementAppend :
              DirectLFStatementAppendCompatible
                messageServers
                sourceBeforeState
                targetBeforeState := by

            simpa [
              DirectLFDetailedForwardPhaseCompatible
            ] using
              hCompatible

          exact
            hBisimulation.forwardStatementMatch
              hStatement
              hStates
              hStatementAppend

      | afterTime
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            DirectLFDetailedForwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            DirectLFDetailedForwardPhaseCompatible
          ] at hCompatible

  | timeAdvance hSourceDispatch hFuture =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage
        selectedServer

      cases targetBefore with

      | stable targetBeforeState =>
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
              (hSourceDispatch :=
                hSourceDispatch)
              hFuture
              hStates

      | afterTime
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            DirectLFDetailedForwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            DirectLFDetailedForwardPhaseCompatible
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
            DirectLFDetailedForwardPhaseCompatible
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

      | afterTime
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            DirectLFDetailedForwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          targetBeforeState
          selectedAction
          selectedReaction
          targetAfterState
          targetDispatch =>
          simp [
            DirectLFDetailedForwardPhaseCompatible
          ] at hCompatible

/--
The phase-indexed interface lifts any phase-compatible exact generated-LF
detailed step to one DTR weak match.
-/
theorem DirectLFDetailedPhaseWeakBisimulation.backwardStep
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    (hBisimulation :
      DirectLFDetailedPhaseWeakBisimulation
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
      DirectLFDetailedRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      DirectLFDetailedBackwardPhaseCompatible
        (declaredVariables :=
          declaredVariables)
        sourceBefore
        targetBefore
        targetLabel
        targetAfter) :
    DirectLFDetailedBackwardMatch
      declaredVariables
      messageServers
      targetLabel
      targetAfter
      sourceBefore := by

  cases hTargetStep with

  | statement hStatement =>
      rename_i
        targetBeforeState
        targetAfterState
        targetStatementLabel

      cases sourceBefore with

      | stable sourceBeforeState =>
          have hStatementData :
              DirectLFStatementAppendCompatible
                    messageServers
                    sourceBeforeState
                    targetBeforeState ∧
                DTR.Body.MultiStoreWellFormed
                  declaredVariables
                  (DTR.messageServerNames
                    messageServers)
                  sourceBeforeState.activeBody := by

            simpa [
              DirectLFDetailedBackwardPhaseCompatible
            ] using
              hCompatible

          rcases hStatementData with
            ⟨hStatementAppend,
             hSourceBody⟩

          exact
            hBisimulation.backwardStatementMatch
              hStatement
              hStates
              hStatementAppend
              hSourceBody

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          simp [
            DirectLFDetailedBackwardPhaseCompatible
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
              (hTargetDispatch :=
                hTargetDispatch)
              hFuture
              hStates

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          simp [
            DirectLFDetailedBackwardPhaseCompatible
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
            DirectLFDetailedBackwardPhaseCompatible
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
            DirectLFDetailedBackwardPhaseCompatible
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
              (hTargetDispatch :=
                hTargetDispatch)
              hSameTime
              hLaterMicrostep
              hStates

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          simp [
            DirectLFDetailedBackwardPhaseCompatible
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

      | dispatchReady
          sourceBeforeState
          selectedMessage
          selectedServer
          sourceAfterState
          sourceDispatch =>
          simp [
            DirectLFDetailedBackwardPhaseCompatible
          ] at hCompatible

/--
Pointwise correspondence between representative labels of a finite DTR weak
execution and a finite generated-LF weak execution.

A target-only LF microstep corresponds to a representative DTR tau label.
-/
inductive DirectLFDetailedWeakLabelTraceCorresponds :
    List DTR.DetailedMultiStoreLabel →
    List LF.DetailedMultiStoreLabel →
    Prop where

  | nil :
      DirectLFDetailedWeakLabelTraceCorresponds
        []
        []

  | cons
      {sourceLabel :
        DTR.DetailedMultiStoreLabel}
      {targetLabel :
        LF.DetailedMultiStoreLabel}
      {sourceRemaining :
        List DTR.DetailedMultiStoreLabel}
      {targetRemaining :
        List LF.DetailedMultiStoreLabel}
      (head :
        DirectLFDetailedLabelCorresponds
          sourceLabel
          targetLabel)
      (tail :
        DirectLFDetailedWeakLabelTraceCorresponds
          sourceRemaining
          targetRemaining) :
      DirectLFDetailedWeakLabelTraceCorresponds
        (sourceLabel :: sourceRemaining)
        (targetLabel :: targetRemaining)

namespace DirectLFDetailedWeakLabelTraceCorresponds

theorem length_eq
    {sourceLabels :
      List DTR.DetailedMultiStoreLabel}
    {targetLabels :
      List LF.DetailedMultiStoreLabel}
    (hTrace :
      DirectLFDetailedWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    sourceLabels.length =
      targetLabels.length := by

  induction hTrace with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

theorem append
    {sourceLeft sourceRight :
      List DTR.DetailedMultiStoreLabel}
    {targetLeft targetRight :
      List LF.DetailedMultiStoreLabel}
    (left :
      DirectLFDetailedWeakLabelTraceCorresponds
        sourceLeft
        targetLeft)
    (right :
      DirectLFDetailedWeakLabelTraceCorresponds
        sourceRight
        targetRight) :
    DirectLFDetailedWeakLabelTraceCorresponds
      (sourceLeft ++ sourceRight)
      (targetLeft ++ targetRight) := by

  induction left with

  | nil =>
      simpa using right

  | cons head tail inductionHypothesis =>
      exact
        DirectLFDetailedWeakLabelTraceCorresponds.cons
          head
          inductionHypothesis

end DirectLFDetailedWeakLabelTraceCorresponds

/--
Compatibility evidence indexed by an exact finite DTR detailed-label sequence.

For every possible first-step decomposition, it supplies the current DirectLF
forward phase premise and a continuation compatible with every corresponding
weak generated-LF match.
-/
def DirectLFDetailedForwardLabelsCompatible
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
        DirectLFDetailedForwardPhaseCompatible
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
            DirectLFDetailedLabelCorresponds
                sourceLabel
                targetLabel →
            DirectLFDetailedRuntimeStateCorresponds
                messageServers
                sourceMiddle
                targetMiddle →
            DirectLFDetailedForwardLabelsCompatible
              declaredVariables
              messageServers
              sourceMiddle
              sourceAfter
              sourceRemainingLabels
              targetMiddle

termination_by sourceLabels.length

/--
Compatibility for one exact finite DTR detailed execution.
-/
def DirectLFDetailedForwardStepsCompatible
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

  DirectLFDetailedForwardLabelsCompatible
    declaredVariables
    messageServers
    sourceBefore
    sourceAfter
    sourceLabels
    targetBefore

/--
Compatibility evidence indexed by an exact finite generated-LF detailed-label
sequence.

For every possible first-step decomposition, it supplies the current DirectLF
backward phase premise and a continuation compatible with every corresponding
weak DTR match.
-/
def DirectLFDetailedBackwardLabelsCompatible
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
        DirectLFDetailedBackwardPhaseCompatible
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
            DirectLFDetailedLabelCorresponds
                sourceLabel
                targetLabel →
            DirectLFDetailedRuntimeStateCorresponds
                messageServers
                sourceMiddle
                targetMiddle →
            DirectLFDetailedBackwardLabelsCompatible
              declaredVariables
              messageServers
              sourceMiddle
              targetMiddle
              targetAfter
              targetRemainingLabels

termination_by targetLabels.length

/--
Compatibility for one exact finite generated-LF detailed execution.
-/
def DirectLFDetailedBackwardStepsCompatible
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

  DirectLFDetailedBackwardLabelsCompatible
    declaredVariables
    messageServers
    sourceBefore
    targetBefore
    targetAfter
    targetLabels

/--
Conditional finite forward correspondence for an exact DTR detailed
execution.

The generated-LF execution is weak, representative labels correspond
pointwise, and final detailed runtime states correspond.
-/
theorem directLFDetailedSteps_forward_of_compatible
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
          targetAfter := by

  let hBisimulation :=
    directLFDetailedRuntime_phaseWeakBisimulation
      declaredVariables
      messageServers

  induction hSourceSteps generalizing targetBefore with

  | refl sourceState =>
      exact
        ⟨[],
         targetBefore,
         Common.WeakSteps.refl
           targetBefore,
         DirectLFDetailedWeakLabelTraceCorresponds.nil,
         hStates⟩

  | cons hHead hTail inductionHypothesis =>
      unfold
        DirectLFDetailedForwardStepsCompatible
        at hCompatible

      simp only [
        DirectLFDetailedForwardLabelsCompatible
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
          DirectLFDetailedForwardStepsCompatible
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
           hFinalStates⟩

      exact
        ⟨targetHeadLabel ::
            targetRemainingLabels,
         targetAfter,
         Common.WeakSteps.cons
           hTargetHead
           hTargetTail,
         DirectLFDetailedWeakLabelTraceCorresponds.cons
           hHeadLabels
           hTailLabels,
         hFinalStates⟩

/--
Conditional finite backward correspondence for an exact generated-LF detailed
execution.

The recovered DTR execution is weak, representative labels correspond
pointwise, and final detailed runtime states correspond.
-/
theorem directLFDetailedSteps_backward_of_compatible
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
          targetAfter := by

  let hBisimulation :=
    directLFDetailedRuntime_phaseWeakBisimulation
      declaredVariables
      messageServers

  induction hTargetSteps generalizing sourceBefore with

  | refl targetState =>
      exact
        ⟨[],
         sourceBefore,
         Common.WeakSteps.refl
           sourceBefore,
         DirectLFDetailedWeakLabelTraceCorresponds.nil,
         hStates⟩

  | cons hHead hTail inductionHypothesis =>
      unfold
        DirectLFDetailedBackwardStepsCompatible
        at hCompatible

      simp only [
        DirectLFDetailedBackwardLabelsCompatible
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
          DirectLFDetailedBackwardStepsCompatible
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
           hFinalStates⟩

      exact
        ⟨sourceHeadLabel ::
            sourceRemainingLabels,
         sourceAfter,
         Common.WeakSteps.cons
           hSourceHead
           hSourceTail,
         DirectLFDetailedWeakLabelTraceCorresponds.cons
           hHeadLabels
           hTailLabels,
         hFinalStates⟩

end Correctness
end Relico
