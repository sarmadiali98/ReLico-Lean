import Relico.Common.WeakExecution
import Relico.Correctness.DetailedBoundPayloadPhaseWeakBisimulation

set_option autoImplicit false

namespace Relico

namespace DTR

/--
Finite sequences of representative detailed bound-payload weak labels.
-/
abbrev DetailedBoundPayloadWeakSteps
    (server : DTR.PayloadMessageServer) :=
  Common.WeakSteps
    (DTR.DetailedBoundPayloadStep server)
    DTR.DetailedBoundPayloadLabel.isTau

end DTR

namespace LF

/--
Finite sequences of representative generated-LF detailed bound-payload weak
labels.
-/
abbrev DetailedBoundPayloadWeakSteps
    (reaction : LF.PayloadReaction) :=
  Common.WeakSteps
    (LF.DetailedBoundPayloadStep reaction)
    LF.DetailedBoundPayloadLabel.isTau

end LF

namespace Correctness

/--
Pointwise correspondence between finite sequences of representative detailed
bound-payload weak labels.
-/
inductive DetailedBoundPayloadWeakLabelTraceCorresponds :
    List DTR.DetailedBoundPayloadLabel →
    List LF.DetailedBoundPayloadLabel →
    Prop where

  | nil :
      DetailedBoundPayloadWeakLabelTraceCorresponds
        []
        []

  | cons
      {sourceLabel :
        DTR.DetailedBoundPayloadLabel}
      {targetLabel :
        LF.DetailedBoundPayloadLabel}
      {sourceRemaining :
        List DTR.DetailedBoundPayloadLabel}
      {targetRemaining :
        List LF.DetailedBoundPayloadLabel}
      (head :
        DetailedBoundPayloadLabelCorresponds
          sourceLabel
          targetLabel)
      (tail :
        DetailedBoundPayloadWeakLabelTraceCorresponds
          sourceRemaining
          targetRemaining) :
      DetailedBoundPayloadWeakLabelTraceCorresponds
        (sourceLabel :: sourceRemaining)
        (targetLabel :: targetRemaining)

namespace DetailedBoundPayloadWeakLabelTraceCorresponds

theorem length_eq
    {sourceLabels :
      List DTR.DetailedBoundPayloadLabel}
    {targetLabels :
      List LF.DetailedBoundPayloadLabel}
    (hTrace :
      DetailedBoundPayloadWeakLabelTraceCorresponds
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
      List DTR.DetailedBoundPayloadLabel}
    {targetLeft targetRight :
      List LF.DetailedBoundPayloadLabel}
    (left :
      DetailedBoundPayloadWeakLabelTraceCorresponds
        sourceLeft
        targetLeft)
    (right :
      DetailedBoundPayloadWeakLabelTraceCorresponds
        sourceRight
        targetRight) :
    DetailedBoundPayloadWeakLabelTraceCorresponds
      (sourceLeft ++ sourceRight)
      (targetLeft ++ targetRight) := by

  induction left with

  | nil =>
      simpa using right

  | cons head tail inductionHypothesis =>
      exact
        DetailedBoundPayloadWeakLabelTraceCorresponds.cons
          head
          inductionHypothesis

end DetailedBoundPayloadWeakLabelTraceCorresponds

/--
The phase-specific premise required to match one exact detailed source
bound-payload step from a generated-LF detailed phase.
-/
def DetailedBoundPayloadForwardPhaseCompatible
    {server : DTR.PayloadMessageServer}
    (sourceBefore :
      DTR.DetailedBoundPayloadState server)
    (sourceLabel :
      DTR.DetailedBoundPayloadLabel)
    (sourceAfter :
      DTR.DetailedBoundPayloadState server)
    (targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)) :
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
      sourceAfterState
      _,
    .stable targetBeforeState =>
      BoundPayloadForwardDispatchCompatible
        selectedMessage
        sourceAfterState.pendingMessages
        targetBeforeState

  | .dispatchReady _ _ _ _,
    .consume _,
    .stable _,
    .afterTime _ _ _ _ =>
      True

  | .dispatchReady _ _ _ _,
    .consume _,
    .stable _,
    .dispatchReady _ _ _ _ =>
      True

  | .stable _,
    .consume selectedMessage,
    .stable sourceAfterState,
    .stable targetBeforeState =>
      BoundPayloadForwardDispatchCompatible
        selectedMessage
        sourceAfterState.pendingMessages
        targetBeforeState

  | _, _, _, _ =>
      False

/--
The phase-specific premise required to match one exact generated-LF detailed
bound-payload step from a source detailed phase.

Every admitted payload-aware backward phase combination is premise-free beyond
the exact transition and current state correspondence.
-/
def DetailedBoundPayloadBackwardPhaseCompatible
    {server : DTR.PayloadMessageServer}
    (sourceBefore :
      DTR.DetailedBoundPayloadState server)
    (targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server))
    (targetLabel :
      LF.DetailedBoundPayloadLabel)
    (targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)) :
    Prop :=

  match
      sourceBefore,
      targetBefore,
      targetLabel,
      targetAfter
    with

  | .stable _,
    .stable _,
    .tau,
    .stable _ =>
      True

  | .stable _,
    .stable _,
    .timeAdvance _ _,
    .afterTime _ _ _ _ =>
      True

  | .dispatchReady _ _ _ _,
    .afterTime _ _ _ _,
    .microstepAdvance _ _,
    .dispatchReady _ _ _ _ =>
      True

  | .dispatchReady _ _ _ _,
    .afterTime _ _ _ _,
    .consume _,
    .stable _ =>
      True

  | .stable _,
    .stable _,
    .microstepAdvance _ _,
    .dispatchReady _ _ _ _ =>
      True

  | .dispatchReady _ _ _ _,
    .dispatchReady _ _ _ _,
    .consume _,
    .stable _ =>
      True

  | .stable _,
    .dispatchReady _ _ _ _,
    .consume _,
    .stable _ =>
      True

  | .stable _,
    .stable _,
    .consume _,
    .stable _ =>
      True

  | _, _, _, _ =>
      False

/--
Lift one phase-compatible exact detailed source step to one generated-LF weak
match.
-/
theorem DetailedBoundPayloadPhaseWeakBisimulation.forwardStep
    {server : DTR.PayloadMessageServer}
    (hBisimulation :
      DetailedBoundPayloadPhaseWeakBisimulation
        server)
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState server}
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
    (hCompatible :
      DetailedBoundPayloadForwardPhaseCompatible
        sourceBefore
        sourceLabel
        sourceAfter
        targetBefore) :
    DetailedBoundPayloadForwardMatch
      server
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
          targetAfterState
          targetDispatch =>
          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          targetBeforeState
          selectedAction
          targetAfterState
          targetDispatch =>
          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ] at hCompatible

  | timeAdvance hSourceDispatch hFuture =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage

      cases targetBefore with

      | stable targetBeforeState =>
          have hScheduler :
              BoundPayloadForwardDispatchCompatible
                selectedMessage
                sourceAfterState.pendingMessages
                targetBeforeState := by

            simpa [
              DetailedBoundPayloadForwardPhaseCompatible
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
          targetAfterState
          targetDispatch =>
          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          targetBeforeState
          selectedAction
          targetAfterState
          targetDispatch =>
          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ] at hCompatible

  | consumeReady hSourceDispatch =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage

      cases targetBefore with

      | stable targetBeforeState =>
          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ] at hCompatible

      | afterTime
          targetBeforeState
          selectedAction
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
              (sourceDispatch :=
                hSourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (targetDispatch :=
                targetDispatch)
              hStates

      | dispatchReady
          targetBeforeState
          selectedAction
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
              (sourceDispatch :=
                hSourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (targetDispatch :=
                targetDispatch)
              hStates

  | consumeNow hSourceDispatch hSameTime =>
      rename_i
        sourceBeforeState
        sourceAfterState
        selectedMessage

      cases targetBefore with

      | stable targetBeforeState =>
          have hScheduler :
              BoundPayloadForwardDispatchCompatible
                selectedMessage
                sourceAfterState.pendingMessages
                targetBeforeState := by

            simpa [
              DetailedBoundPayloadForwardPhaseCompatible
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
              (targetBefore :=
                targetBeforeState)
              hSourceDispatch
              hSameTime
              hStates
              hScheduler

      | afterTime
          targetBeforeState
          selectedAction
          targetAfterState
          targetDispatch =>
          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          targetBeforeState
          selectedAction
          targetAfterState
          targetDispatch =>
          simp [
            DetailedBoundPayloadForwardPhaseCompatible
          ] at hCompatible

/--
Lift one phase-compatible exact generated-LF detailed bound-payload step to one
source weak match.
-/
theorem DetailedBoundPayloadPhaseWeakBisimulation.backwardStep
    {server : DTR.PayloadMessageServer}
    (hBisimulation :
      DetailedBoundPayloadPhaseWeakBisimulation
        server)
    {sourceBefore :
      DTR.DetailedBoundPayloadState server}
    {targetBefore targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    {targetLabel :
      LF.DetailedBoundPayloadLabel}
    (hTargetStep :
      LF.DetailedBoundPayloadStep
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      DetailedBoundPayloadStateCorresponds
        server
        sourceBefore
        targetBefore)
    (hCompatible :
      DetailedBoundPayloadBackwardPhaseCompatible
        sourceBefore
        targetBefore
        targetLabel
        targetAfter) :
    DetailedBoundPayloadBackwardMatch
      server
      targetLabel
      targetAfter
      sourceBefore := by

  cases hTargetStep with

  | statement hStatement =>
      cases sourceBefore with

      | stable sourceBeforeState =>
          exact
            hBisimulation.backwardStatementMatch
              _ _ _ _
              hStatement
              hStates

      | dispatchReady
          sourceBeforeState
          selectedMessage
          sourceAfterState
          sourceDispatch =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ] at hCompatible

  | timeAdvance hTargetDispatch hFuture =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction

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
              (targetDispatch :=
                hTargetDispatch)
              hFuture
              hStates

      | dispatchReady
          sourceBeforeState
          selectedMessage
          sourceAfterState
          sourceDispatch =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ] at hCompatible

  | microstepAfterTime
      hTargetDispatch
      hPositiveMicrostep =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction

      cases sourceBefore with

      | stable sourceBeforeState =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          sourceBeforeState
          selectedMessage
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
              (sourceDispatch :=
                sourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
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

      cases sourceBefore with

      | stable sourceBeforeState =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ] at hCompatible

      | dispatchReady
          sourceBeforeState
          selectedMessage
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
              (sourceDispatch :=
                sourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
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
              (targetDispatch :=
                hTargetDispatch)
              hSameTime
              hLaterMicrostep
              hStates

      | dispatchReady
          sourceBeforeState
          selectedMessage
          sourceAfterState
          sourceDispatch =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ] at hCompatible

  | consumeReady hTargetDispatch =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction

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
              (targetDispatch :=
                hTargetDispatch)
              hStates

      | dispatchReady
          sourceBeforeState
          selectedMessage
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
              (sourceDispatch :=
                sourceDispatch)
              (targetBefore :=
                targetBeforeState)
              (targetAfter :=
                targetAfterState)
              (selectedAction :=
                selectedAction)
              (targetDispatch :=
                hTargetDispatch)
              hStates

  | consumeNow
      hTargetDispatch
      hSameTag =>
      rename_i
        targetBeforeState
        targetAfterState
        selectedAction

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
              hTargetDispatch
              hSameTag
              hStates

      | dispatchReady
          sourceBeforeState
          selectedMessage
          sourceAfterState
          sourceDispatch =>
          simp [
            DetailedBoundPayloadBackwardPhaseCompatible
          ] at hCompatible

/--
Compatibility evidence indexed by an exact finite source detailed
bound-payload label sequence.
-/
def DetailedBoundPayloadForwardLabelsCompatible
    (server : DTR.PayloadMessageServer)
    (sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState server)
    (sourceLabels :
      List DTR.DetailedBoundPayloadLabel)
    (targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)) :
    Prop :=

  match sourceLabels with

  | [] =>
      sourceBefore =
        sourceAfter

  | sourceLabel :: sourceRemainingLabels =>
      ∀ sourceMiddle,
        DTR.DetailedBoundPayloadStep
            server
            sourceBefore
            sourceLabel
            sourceMiddle →
        DTR.DetailedBoundPayloadSteps
            server
            sourceMiddle
            sourceRemainingLabels
            sourceAfter →
        DetailedBoundPayloadForwardPhaseCompatible
            sourceBefore
            sourceLabel
            sourceMiddle
            targetBefore ∧
          ∀ {targetLabel targetMiddle},
            LF.DetailedBoundPayloadWeakStep
                (Translation.compilePayloadMessageServer
                  server)
                targetBefore
                targetLabel
                targetMiddle →
            DetailedBoundPayloadLabelCorresponds
                sourceLabel
                targetLabel →
            DetailedBoundPayloadStateCorresponds
                server
                sourceMiddle
                targetMiddle →
            DetailedBoundPayloadForwardLabelsCompatible
              server
              sourceMiddle
              sourceAfter
              sourceRemainingLabels
              targetMiddle

termination_by sourceLabels.length

/--
Compatibility for one exact finite source detailed bound-payload execution.
-/
def DetailedBoundPayloadForwardStepsCompatible
    (server : DTR.PayloadMessageServer)
    {sourceBefore sourceAfter :
      DTR.DetailedBoundPayloadState server}
    {sourceLabels :
      List DTR.DetailedBoundPayloadLabel}
    (_hSteps :
      DTR.DetailedBoundPayloadSteps
        server
        sourceBefore
        sourceLabels
        sourceAfter)
    (targetBefore :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)) :
    Prop :=

  DetailedBoundPayloadForwardLabelsCompatible
    server
    sourceBefore
    sourceAfter
    sourceLabels
    targetBefore

/--
Compatibility evidence indexed by an exact finite generated-LF detailed
bound-payload label sequence.
-/
def DetailedBoundPayloadBackwardLabelsCompatible
    (server : DTR.PayloadMessageServer)
    (sourceBefore :
      DTR.DetailedBoundPayloadState server)
    (targetBefore targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server))
    (targetLabels :
      List LF.DetailedBoundPayloadLabel) :
    Prop :=

  match targetLabels with

  | [] =>
      targetBefore =
        targetAfter

  | targetLabel :: targetRemainingLabels =>
      ∀ targetMiddle,
        LF.DetailedBoundPayloadStep
            (Translation.compilePayloadMessageServer
              server)
            targetBefore
            targetLabel
            targetMiddle →
        LF.DetailedBoundPayloadSteps
            (Translation.compilePayloadMessageServer
              server)
            targetMiddle
            targetRemainingLabels
            targetAfter →
        DetailedBoundPayloadBackwardPhaseCompatible
            sourceBefore
            targetBefore
            targetLabel
            targetMiddle ∧
          ∀ {sourceLabel sourceMiddle},
            DTR.DetailedBoundPayloadWeakStep
                server
                sourceBefore
                sourceLabel
                sourceMiddle →
            DetailedBoundPayloadLabelCorresponds
                sourceLabel
                targetLabel →
            DetailedBoundPayloadStateCorresponds
                server
                sourceMiddle
                targetMiddle →
            DetailedBoundPayloadBackwardLabelsCompatible
              server
              sourceMiddle
              targetMiddle
              targetAfter
              targetRemainingLabels

termination_by targetLabels.length

/--
Compatibility for one exact finite generated-LF detailed bound-payload
execution.
-/
def DetailedBoundPayloadBackwardStepsCompatible
    (server : DTR.PayloadMessageServer)
    (sourceBefore :
      DTR.DetailedBoundPayloadState server)
    {targetBefore targetAfter :
      LF.DetailedBoundPayloadState
        (Translation.compilePayloadMessageServer
          server)}
    {targetLabels :
      List LF.DetailedBoundPayloadLabel}
    (_hSteps :
      LF.DetailedBoundPayloadSteps
        (Translation.compilePayloadMessageServer
          server)
        targetBefore
        targetLabels
        targetAfter) :
    Prop :=

  DetailedBoundPayloadBackwardLabelsCompatible
    server
    sourceBefore
    targetBefore
    targetAfter
    targetLabels

/--
Conditional finite forward correspondence for exact detailed source
bound-payload executions.
-/
theorem detailedBoundPayloadSteps_forward_of_compatible
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
          targetAfter := by

  let hBisimulation :=
    detailedBoundPayload_phaseWeakBisimulation
      server

  induction hSourceSteps generalizing targetBefore with

  | refl sourceState =>
      exact
        ⟨[],
         targetBefore,
         Common.WeakSteps.refl
           targetBefore,
         DetailedBoundPayloadWeakLabelTraceCorresponds.nil,
         hStates⟩

  | cons hHead hTail inductionHypothesis =>
      unfold
        DetailedBoundPayloadForwardStepsCompatible
        at hCompatible

      simp only [
        DetailedBoundPayloadForwardLabelsCompatible
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
          DetailedBoundPayloadForwardStepsCompatible
            server
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
         DetailedBoundPayloadWeakLabelTraceCorresponds.cons
           hHeadLabels
           hTailLabels,
         hFinalStates⟩

/--
Conditional finite backward correspondence for exact detailed generated-LF
bound-payload executions.
-/
theorem detailedBoundPayloadSteps_backward_of_compatible
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
          targetAfter := by

  let hBisimulation :=
    detailedBoundPayload_phaseWeakBisimulation
      server

  induction hTargetSteps generalizing sourceBefore with

  | refl targetState =>
      exact
        ⟨[],
         sourceBefore,
         Common.WeakSteps.refl
           sourceBefore,
         DetailedBoundPayloadWeakLabelTraceCorresponds.nil,
         hStates⟩

  | cons hHead hTail inductionHypothesis =>
      unfold
        DetailedBoundPayloadBackwardStepsCompatible
        at hCompatible

      simp only [
        DetailedBoundPayloadBackwardLabelsCompatible
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
          DetailedBoundPayloadBackwardStepsCompatible
            server
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
         DetailedBoundPayloadWeakLabelTraceCorresponds.cons
           hHeadLabels
           hTailLabels,
         hFinalStates⟩

end Correctness
end Relico
