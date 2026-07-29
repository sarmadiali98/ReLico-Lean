import Relico.Correctness.MultiStorePayloadDetailedRuntimePhaseWeakBisimulation

set_option autoImplicit false

namespace Relico

namespace DTR

/--
A finite sequence of the already published payload-aware DTR weak steps.

This relation does not reconstruct a second weak semantics. Each head is one
`DetailedMultiStorePayloadWeakStep`, whose tau closure and visible-step
packaging are defined by the published multi-store weak semantics.
-/
inductive DetailedMultiStorePayloadWeakSteps
    (messageServers :
      List Relico.DTR.MultiStorePayloadMessageServer) :
    Relico.DTR.DetailedMultiStorePayloadState
        messageServers →
      List Relico.DTR.DetailedMultiStorePayloadLabel →
        Relico.DTR.DetailedMultiStorePayloadState
            messageServers →
          Prop where

  | refl
      (state :
        Relico.DTR.DetailedMultiStorePayloadState
          messageServers) :
      DetailedMultiStorePayloadWeakSteps
        messageServers
        state
        []
        state

  | cons
      {before middle after :
        Relico.DTR.DetailedMultiStorePayloadState
          messageServers}
      {label :
        Relico.DTR.DetailedMultiStorePayloadLabel}
      {remaining :
        List Relico.DTR.DetailedMultiStorePayloadLabel}
      (head :
        Relico.DTR.DetailedMultiStorePayloadWeakStep
          messageServers
          before
          label
          middle)
      (tail :
        DetailedMultiStorePayloadWeakSteps
          messageServers
          middle
          remaining
          after) :
      DetailedMultiStorePayloadWeakSteps
        messageServers
        before
        (label :: remaining)
        after

theorem DetailedMultiStorePayloadWeakSteps.single
    {messageServers :
      List Relico.DTR.MultiStorePayloadMessageServer}
    {before after :
      Relico.DTR.DetailedMultiStorePayloadState
        messageServers}
    {label :
      Relico.DTR.DetailedMultiStorePayloadLabel}
    (step :
      Relico.DTR.DetailedMultiStorePayloadWeakStep
        messageServers
        before
        label
        after) :
    DetailedMultiStorePayloadWeakSteps
      messageServers
      before
      [label]
      after := by

  exact
    DetailedMultiStorePayloadWeakSteps.cons
      step
      (DetailedMultiStorePayloadWeakSteps.refl
        after)

theorem DetailedMultiStorePayloadWeakSteps.append
    {messageServers :
      List Relico.DTR.MultiStorePayloadMessageServer}
    {before middle after :
      Relico.DTR.DetailedMultiStorePayloadState
        messageServers}
    {leftLabels rightLabels :
      List Relico.DTR.DetailedMultiStorePayloadLabel}
    (left :
      DetailedMultiStorePayloadWeakSteps
        messageServers
        before
        leftLabels
        middle)
    (right :
      DetailedMultiStorePayloadWeakSteps
        messageServers
        middle
        rightLabels
        after) :
    DetailedMultiStorePayloadWeakSteps
      messageServers
      before
      (leftLabels ++ rightLabels)
      after := by

  induction left generalizing rightLabels after with

  | refl =>
      simpa using right

  | cons head tail inductionHypothesis =>
      simp only [List.cons_append]

      exact
        DetailedMultiStorePayloadWeakSteps.cons
          head
          (inductionHypothesis
            right)

end DTR

namespace LF

/--
A finite sequence of the already published generated-LF payload weak steps.

LF statement and microstep transitions have already been absorbed into the
tau closure of each `DetailedMultiStorePayloadWeakStep`; metric-time and
payload-consumption transitions remain visible labels.
-/
inductive DetailedMultiStorePayloadWeakSteps
    (messageReactions :
      List Relico.LF.MultiStorePayloadReaction) :
    Relico.LF.DetailedMultiStorePayloadState
        messageReactions →
      List Relico.LF.DetailedMultiStorePayloadLabel →
        Relico.LF.DetailedMultiStorePayloadState
            messageReactions →
          Prop where

  | refl
      (state :
        Relico.LF.DetailedMultiStorePayloadState
          messageReactions) :
      DetailedMultiStorePayloadWeakSteps
        messageReactions
        state
        []
        state

  | cons
      {before middle after :
        Relico.LF.DetailedMultiStorePayloadState
          messageReactions}
      {label :
        Relico.LF.DetailedMultiStorePayloadLabel}
      {remaining :
        List Relico.LF.DetailedMultiStorePayloadLabel}
      (head :
        Relico.LF.DetailedMultiStorePayloadWeakStep
          messageReactions
          before
          label
          middle)
      (tail :
        DetailedMultiStorePayloadWeakSteps
          messageReactions
          middle
          remaining
          after) :
      DetailedMultiStorePayloadWeakSteps
        messageReactions
        before
        (label :: remaining)
        after

theorem DetailedMultiStorePayloadWeakSteps.single
    {messageReactions :
      List Relico.LF.MultiStorePayloadReaction}
    {before after :
      Relico.LF.DetailedMultiStorePayloadState
        messageReactions}
    {label :
      Relico.LF.DetailedMultiStorePayloadLabel}
    (step :
      Relico.LF.DetailedMultiStorePayloadWeakStep
        messageReactions
        before
        label
        after) :
    DetailedMultiStorePayloadWeakSteps
      messageReactions
      before
      [label]
      after := by

  exact
    DetailedMultiStorePayloadWeakSteps.cons
      step
      (DetailedMultiStorePayloadWeakSteps.refl
        after)

theorem DetailedMultiStorePayloadWeakSteps.append
    {messageReactions :
      List Relico.LF.MultiStorePayloadReaction}
    {before middle after :
      Relico.LF.DetailedMultiStorePayloadState
        messageReactions}
    {leftLabels rightLabels :
      List Relico.LF.DetailedMultiStorePayloadLabel}
    (left :
      DetailedMultiStorePayloadWeakSteps
        messageReactions
        before
        leftLabels
        middle)
    (right :
      DetailedMultiStorePayloadWeakSteps
        messageReactions
        middle
        rightLabels
        after) :
    DetailedMultiStorePayloadWeakSteps
      messageReactions
      before
      (leftLabels ++ rightLabels)
      after := by

  induction left generalizing rightLabels after with

  | refl =>
      simpa using right

  | cons head tail inductionHypothesis =>
      simp only [List.cons_append]

      exact
        DetailedMultiStorePayloadWeakSteps.cons
          head
          (inductionHypothesis
            right)

end LF

namespace Correctness

/--
Pointwise correspondence between finite DTR and LF weak-step label lists.

The head relation is the published exact payload-aware detailed-label
correspondence.
-/
inductive MultiStorePayloadDetailedWeakLabelTraceCorresponds :
    List Relico.DTR.DetailedMultiStorePayloadLabel →
      List Relico.LF.DetailedMultiStorePayloadLabel →
        Prop where

  | nil :
      MultiStorePayloadDetailedWeakLabelTraceCorresponds
        []
        []

  | cons
      {sourceLabel :
        Relico.DTR.DetailedMultiStorePayloadLabel}
      {targetLabel :
        Relico.LF.DetailedMultiStorePayloadLabel}
      {sourceRemaining :
        List Relico.DTR.DetailedMultiStorePayloadLabel}
      {targetRemaining :
        List Relico.LF.DetailedMultiStorePayloadLabel}
      (head :
        Relico.Correctness.MultiStorePayloadDetailedLabelCorresponds
          sourceLabel
          targetLabel)
      (tail :
        MultiStorePayloadDetailedWeakLabelTraceCorresponds
          sourceRemaining
          targetRemaining) :
      MultiStorePayloadDetailedWeakLabelTraceCorresponds
        (sourceLabel :: sourceRemaining)
        (targetLabel :: targetRemaining)

theorem MultiStorePayloadDetailedWeakLabelTraceCorresponds.length_eq
    {sourceLabels :
      List Relico.DTR.DetailedMultiStorePayloadLabel}
    {targetLabels :
      List Relico.LF.DetailedMultiStorePayloadLabel}
    (corresponds :
      MultiStorePayloadDetailedWeakLabelTraceCorresponds
        sourceLabels
        targetLabels) :
    sourceLabels.length =
      targetLabels.length := by

  induction corresponds with

  | nil =>
      rfl

  | cons head tail inductionHypothesis =>
      simp only [List.length_cons]

      exact
        congrArg Nat.succ
          inductionHypothesis

theorem MultiStorePayloadDetailedWeakLabelTraceCorresponds.append
    {sourceLeft sourceRight :
      List Relico.DTR.DetailedMultiStorePayloadLabel}
    {targetLeft targetRight :
      List Relico.LF.DetailedMultiStorePayloadLabel}
    (left :
      MultiStorePayloadDetailedWeakLabelTraceCorresponds
        sourceLeft
        targetLeft)
    (right :
      MultiStorePayloadDetailedWeakLabelTraceCorresponds
        sourceRight
        targetRight) :
    MultiStorePayloadDetailedWeakLabelTraceCorresponds
      (sourceLeft ++ sourceRight)
      (targetLeft ++ targetRight) := by

  induction left with

  | nil =>
      simpa using right

  | cons head tail inductionHypothesis =>
      simp only [List.cons_append]

      exact
        MultiStorePayloadDetailedWeakLabelTraceCorresponds.cons
          head
          inductionHypothesis

end Correctness

namespace Correctness

/--
Compatibility required to dispatch one detailed DTR phase through the
published payload-aware multi-store weak-bisimulation package.

The five admitted shapes are exactly the four source constructors, with the
ready-consumption constructor split according to the corresponding LF phase.
Only statement execution carries the explicit runtime-compatibility premise.
-/
def MultiStorePayloadDetailedForwardPhaseCompatible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (sourceBefore :
      DTR.DetailedMultiStorePayloadState
        messageServers)
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

  match sourceBefore, sourceLabel, sourceAfter, targetBefore with

  | .stable sourceBeforeState,
    .tau,
    .stable _,
    .stable targetBeforeState =>
      MultiStorePayloadStatementRuntimeCompatible
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
Compatibility required to dispatch one detailed LF phase through the
published payload-aware multi-store weak-bisimulation package.

The eight admitted shapes correspond exactly to the seven target
constructors, with ready consumption split according to whether the source is
already dispatch-ready or remains stable. Statement execution retains the
explicit runtime-compatibility premise. LF microsteps occur only here.
-/
def MultiStorePayloadDetailedBackwardPhaseCompatible
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (sourceBefore :
      DTR.DetailedMultiStorePayloadState
        messageServers)
    (targetBefore :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers))
    (targetLabel :
      LF.DetailedMultiStorePayloadLabel)
    (targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)) :
    Prop :=

  match sourceBefore, targetBefore, targetLabel, targetAfter with

  | .stable sourceBeforeState,
    .stable targetBeforeState,
    .tau,
    .stable _ =>
      MultiStorePayloadStatementRuntimeCompatible
        messageServers
        sourceBeforeState
        targetBeforeState

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

/--
Generic forward one-step dispatcher for the published thirteen-field package.
-/
theorem multiStorePayloadDetailedRuntime_forwardStep
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (hBisimulation :
      MultiStorePayloadDetailedRuntimePhaseWeakBisimulation
        messageServers)
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStorePayloadState
        messageServers}
    {sourceLabel :
      DTR.DetailedMultiStorePayloadLabel}
    {targetBefore :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
    (hSourceStep :
      DTR.DetailedMultiStorePayloadStep
        messageServers
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      MultiStorePayloadDetailedForwardPhaseCompatible
        sourceBefore
        sourceLabel
        sourceAfter
        targetBefore) :
    MultiStorePayloadDetailedForwardMatch
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
              hStatement
              hStates
              hCompatible

      | afterTime _ _ _ _ _ =>
          exact False.elim hCompatible

      | dispatchReady _ _ _ _ _ =>
          exact False.elim hCompatible

  | timeAdvance sourceDispatch hFuture =>
      cases targetBefore with

      | stable _ =>
          exact
            hBisimulation.forwardTimeAdvanceMatch
              sourceDispatch
              hFuture
              hStates

      | afterTime _ _ _ _ _ =>
          exact False.elim hCompatible

      | dispatchReady _ _ _ _ _ =>
          exact False.elim hCompatible

  | consumeReady sourceDispatch =>
      cases targetBefore with

      | stable _ =>
          exact False.elim hCompatible

      | afterTime _ _ _ _ _ =>
          exact
            hBisimulation.forwardConsumeAfterTimeMatch
              hStates

      | dispatchReady _ _ _ _ _ =>
          exact
            hBisimulation.forwardConsumeReadyMatch
              hStates

  | consumeNow sourceDispatch hSameTime =>
      cases targetBefore with

      | stable _ =>
          exact
            hBisimulation.forwardConsumeNowMatch
              sourceDispatch
              hSameTime
              hStates

      | afterTime _ _ _ _ _ =>
          exact False.elim hCompatible

      | dispatchReady _ _ _ _ _ =>
          exact False.elim hCompatible

/--
Generic backward one-step dispatcher for the published thirteen-field package.
-/
theorem multiStorePayloadDetailedRuntime_backwardStep
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    (hBisimulation :
      MultiStorePayloadDetailedRuntimePhaseWeakBisimulation
        messageServers)
    {sourceBefore :
      DTR.DetailedMultiStorePayloadState
        messageServers}
    {targetBefore targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
    {targetLabel :
      LF.DetailedMultiStorePayloadLabel}
    (hTargetStep :
      LF.DetailedMultiStorePayloadStep
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      MultiStorePayloadDetailedBackwardPhaseCompatible
        sourceBefore
        targetBefore
        targetLabel
        targetAfter) :
    MultiStorePayloadDetailedBackwardMatch
      messageServers
      targetLabel
      targetAfter
      sourceBefore := by

  cases hTargetStep with

  | statement hStatement =>
      cases sourceBefore with

      | stable _ =>
          exact
            hBisimulation.backwardStatementMatch
              hStatement
              hStates
              hCompatible

      | dispatchReady _ _ _ _ _ =>
          exact False.elim hCompatible

  | timeAdvance targetDispatch hFuture =>
      cases sourceBefore with

      | stable _ =>
          exact
            hBisimulation.backwardTimeAdvanceMatch
              targetDispatch
              hFuture
              hStates

      | dispatchReady _ _ _ _ _ =>
          exact False.elim hCompatible

  | microstepAfterTime targetDispatch hPositiveMicrostep =>
      cases sourceBefore with

      | stable _ =>
          exact False.elim hCompatible

      | dispatchReady _ _ _ _ _ =>
          exact
            hBisimulation.backwardMicrostepAfterTimeMatch
              hPositiveMicrostep
              hStates

  | consumeAfterTimeZero targetDispatch hZeroMicrostep =>
      cases sourceBefore with

      | stable _ =>
          exact False.elim hCompatible

      | dispatchReady _ _ _ _ _ =>
          exact
            hBisimulation.backwardConsumeAfterTimeZeroMatch
              hZeroMicrostep
              hStates

  | microstepSameTime targetDispatch hSameTime hLaterMicrostep =>
      cases sourceBefore with

      | stable _ =>
          exact
            hBisimulation.backwardMicrostepSameTimeMatch
              targetDispatch
              hSameTime
              hLaterMicrostep
              hStates

      | dispatchReady _ _ _ _ _ =>
          exact False.elim hCompatible

  | consumeReady targetDispatch =>
      cases sourceBefore with

      | stable _ =>
          exact
            hBisimulation.backwardConsumeReadySameTimeMatch
              hStates

      | dispatchReady _ _ _ _ _ =>
          exact
            hBisimulation.backwardConsumeReadyFutureMatch
              hStates

  | consumeNow targetDispatch hSameTime hSameMicrostep =>
      cases sourceBefore with

      | stable _ =>
          exact
            hBisimulation.backwardConsumeNowMatch
              targetDispatch
              hSameTime
              hSameMicrostep
              hStates

      | dispatchReady _ _ _ _ _ =>
          exact False.elim hCompatible

end Correctness
end Relico
