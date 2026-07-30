import Relico.Correctness.MultiStorePayloadDetailedFiniteWeakExecutionFoundation

set_option autoImplicit false

namespace Relico

namespace DTR

/--
A finite list-labelled execution of the existing payload-aware multi-store
detailed DTR step relation.
-/
inductive DetailedMultiStorePayloadSteps
    (messageServers :
      List MultiStorePayloadMessageServer) :
    DetailedMultiStorePayloadState messageServers →
      List DetailedMultiStorePayloadLabel →
        DetailedMultiStorePayloadState messageServers →
          Prop where

  | refl
      (state :
        DetailedMultiStorePayloadState messageServers) :
      DetailedMultiStorePayloadSteps
        messageServers
        state
        []
        state

  | cons
      {before middle after :
        DetailedMultiStorePayloadState messageServers}
      {label :
        DetailedMultiStorePayloadLabel}
      {remaining :
        List DetailedMultiStorePayloadLabel}
      (head :
        DetailedMultiStorePayloadStep
          messageServers
          before
          label
          middle)
      (tail :
        DetailedMultiStorePayloadSteps
          messageServers
          middle
          remaining
          after) :
      DetailedMultiStorePayloadSteps
        messageServers
        before
        (label :: remaining)
        after

theorem DetailedMultiStorePayloadSteps.single
    {messageServers :
      List MultiStorePayloadMessageServer}
    {before after :
      DetailedMultiStorePayloadState messageServers}
    {label :
      DetailedMultiStorePayloadLabel}
    (step :
      DetailedMultiStorePayloadStep
        messageServers
        before
        label
        after) :
    DetailedMultiStorePayloadSteps
      messageServers
      before
      [label]
      after := by

  exact
    DetailedMultiStorePayloadSteps.cons
      step
      (DetailedMultiStorePayloadSteps.refl after)

theorem DetailedMultiStorePayloadSteps.append
    {messageServers :
      List MultiStorePayloadMessageServer}
    {before middle after :
      DetailedMultiStorePayloadState messageServers}
    {leftLabels rightLabels :
      List DetailedMultiStorePayloadLabel}
    (left :
      DetailedMultiStorePayloadSteps
        messageServers
        before
        leftLabels
        middle)
    (right :
      DetailedMultiStorePayloadSteps
        messageServers
        middle
        rightLabels
        after) :
    DetailedMultiStorePayloadSteps
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
        DetailedMultiStorePayloadSteps.cons
          head
          (inductionHypothesis right)

end DTR

namespace LF

/--
A finite list-labelled execution of the existing generated-LF payload-aware
multi-store detailed step relation.
-/
inductive DetailedMultiStorePayloadSteps
    (messageReactions :
      List MultiStorePayloadReaction) :
    DetailedMultiStorePayloadState messageReactions →
      List DetailedMultiStorePayloadLabel →
        DetailedMultiStorePayloadState messageReactions →
          Prop where

  | refl
      (state :
        DetailedMultiStorePayloadState messageReactions) :
      DetailedMultiStorePayloadSteps
        messageReactions
        state
        []
        state

  | cons
      {before middle after :
        DetailedMultiStorePayloadState messageReactions}
      {label :
        DetailedMultiStorePayloadLabel}
      {remaining :
        List DetailedMultiStorePayloadLabel}
      (head :
        DetailedMultiStorePayloadStep
          messageReactions
          before
          label
          middle)
      (tail :
        DetailedMultiStorePayloadSteps
          messageReactions
          middle
          remaining
          after) :
      DetailedMultiStorePayloadSteps
        messageReactions
        before
        (label :: remaining)
        after

theorem DetailedMultiStorePayloadSteps.single
    {messageReactions :
      List MultiStorePayloadReaction}
    {before after :
      DetailedMultiStorePayloadState messageReactions}
    {label :
      DetailedMultiStorePayloadLabel}
    (step :
      DetailedMultiStorePayloadStep
        messageReactions
        before
        label
        after) :
    DetailedMultiStorePayloadSteps
      messageReactions
      before
      [label]
      after := by

  exact
    DetailedMultiStorePayloadSteps.cons
      step
      (DetailedMultiStorePayloadSteps.refl after)

theorem DetailedMultiStorePayloadSteps.append
    {messageReactions :
      List MultiStorePayloadReaction}
    {before middle after :
      DetailedMultiStorePayloadState messageReactions}
    {leftLabels rightLabels :
      List DetailedMultiStorePayloadLabel}
    (left :
      DetailedMultiStorePayloadSteps
        messageReactions
        before
        leftLabels
        middle)
    (right :
      DetailedMultiStorePayloadSteps
        messageReactions
        middle
        rightLabels
        after) :
    DetailedMultiStorePayloadSteps
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
        DetailedMultiStorePayloadSteps.cons
          head
          (inductionHypothesis right)

end LF

namespace Correctness

/--
Derivation-aware compatibility for a finite detailed DTR execution.

For a nonempty source trace, the premise contains compatibility for the head
phase and a continuation obligation for every valid weak target match of that
head. The continuation receives the weak head execution, exact head-label
correspondence, and intermediate detailed runtime-state correspondence.
-/
def MultiStorePayloadDetailedForwardLabelsCompatible
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceBefore sourceAfter :
      DTR.DetailedMultiStorePayloadState messageServers)
    (sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel)
    (targetBefore :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)) :
    Prop :=

  match sourceLabels with

  | [] =>
      True

  | sourceLabel :: remaining =>
      ∀
        (sourceMiddle :
          DTR.DetailedMultiStorePayloadState messageServers),
        DTR.DetailedMultiStorePayloadStep
            messageServers
            sourceBefore
            sourceLabel
            sourceMiddle →
          DTR.DetailedMultiStorePayloadSteps
              messageServers
              sourceMiddle
              remaining
              sourceAfter →
            MultiStorePayloadDetailedForwardPhaseCompatible
                sourceBefore
                sourceLabel
                sourceMiddle
                targetBefore ∧
              ∀
                {targetHeadLabel :
                  LF.DetailedMultiStorePayloadLabel}
                {targetMiddle :
                  LF.DetailedMultiStorePayloadState
                    (Translation.compileMultiStorePayloadMessageReactions
                      messageServers)},
                LF.DetailedMultiStorePayloadWeakStep
                    (Translation.compileMultiStorePayloadMessageReactions
                      messageServers)
                    targetBefore
                    targetHeadLabel
                    targetMiddle →
                  MultiStorePayloadDetailedLabelCorresponds
                      sourceLabel
                      targetHeadLabel →
                    MultiStorePayloadDetailedRuntimeStateCorresponds
                        messageServers
                        sourceMiddle
                        targetMiddle →
                      MultiStorePayloadDetailedForwardLabelsCompatible
                        messageServers
                        sourceMiddle
                        sourceAfter
                        remaining
                        targetMiddle

termination_by sourceLabels

/--
Compatibility indexed by the concrete finite DTR derivation.
-/
def MultiStorePayloadDetailedForwardStepsCompatible
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    {sourceBefore sourceAfter :
      DTR.DetailedMultiStorePayloadState messageServers}
    {sourceLabels :
      List DTR.DetailedMultiStorePayloadLabel}
    (_hSteps :
      DTR.DetailedMultiStorePayloadSteps
        messageServers
        sourceBefore
        sourceLabels
        sourceAfter)
    (targetBefore :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)) :
    Prop :=

  MultiStorePayloadDetailedForwardLabelsCompatible
    messageServers
    sourceBefore
    sourceAfter
    sourceLabels
    targetBefore

/--
Derivation-aware compatibility for a finite detailed generated-LF execution.

For a nonempty target trace, the premise contains compatibility for the head
phase and a continuation obligation for every valid weak source match of that
head. LF microsteps remain target-only and are matched through the published
source weak-step relation.
-/
def MultiStorePayloadDetailedBackwardLabelsCompatible
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceBefore :
      DTR.DetailedMultiStorePayloadState messageServers)
    (targetBefore targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers))
    (targetLabels :
      List LF.DetailedMultiStorePayloadLabel) :
    Prop :=

  match targetLabels with

  | [] =>
      True

  | targetLabel :: remaining =>
      ∀
        (targetMiddle :
          LF.DetailedMultiStorePayloadState
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers)),
        LF.DetailedMultiStorePayloadStep
            (Translation.compileMultiStorePayloadMessageReactions
              messageServers)
            targetBefore
            targetLabel
            targetMiddle →
          LF.DetailedMultiStorePayloadSteps
              (Translation.compileMultiStorePayloadMessageReactions
                messageServers)
              targetMiddle
              remaining
              targetAfter →
            MultiStorePayloadDetailedBackwardPhaseCompatible
                sourceBefore
                targetBefore
                targetLabel
                targetMiddle ∧
              ∀
                {sourceHeadLabel :
                  DTR.DetailedMultiStorePayloadLabel}
                {sourceMiddle :
                  DTR.DetailedMultiStorePayloadState messageServers},
                DTR.DetailedMultiStorePayloadWeakStep
                    messageServers
                    sourceBefore
                    sourceHeadLabel
                    sourceMiddle →
                  MultiStorePayloadDetailedLabelCorresponds
                      sourceHeadLabel
                      targetLabel →
                    MultiStorePayloadDetailedRuntimeStateCorresponds
                        messageServers
                        sourceMiddle
                        targetMiddle →
                      MultiStorePayloadDetailedBackwardLabelsCompatible
                        messageServers
                        sourceMiddle
                        targetMiddle
                        targetAfter
                        remaining

termination_by targetLabels

/--
Compatibility indexed by the concrete finite generated-LF derivation.
-/
def MultiStorePayloadDetailedBackwardStepsCompatible
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceBefore :
      DTR.DetailedMultiStorePayloadState messageServers)
    {targetBefore targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)}
    {targetLabels :
      List LF.DetailedMultiStorePayloadLabel}
    (_hSteps :
      LF.DetailedMultiStorePayloadSteps
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)
        targetBefore
        targetLabels
        targetAfter) :
    Prop :=

  MultiStorePayloadDetailedBackwardLabelsCompatible
    messageServers
    sourceBefore
    targetBefore
    targetAfter
    targetLabels

theorem multiStorePayloadDetailedForwardLabelsCompatible_nil
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceBefore sourceAfter :
      DTR.DetailedMultiStorePayloadState messageServers)
    (targetBefore :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)) :
    MultiStorePayloadDetailedForwardLabelsCompatible
      messageServers
      sourceBefore
      sourceAfter
      []
      targetBefore := by

  simp [MultiStorePayloadDetailedForwardLabelsCompatible]

theorem multiStorePayloadDetailedBackwardLabelsCompatible_nil
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceBefore :
      DTR.DetailedMultiStorePayloadState messageServers)
    (targetBefore targetAfter :
      LF.DetailedMultiStorePayloadState
        (Translation.compileMultiStorePayloadMessageReactions
          messageServers)) :
    MultiStorePayloadDetailedBackwardLabelsCompatible
      messageServers
      sourceBefore
      targetBefore
      targetAfter
      [] := by

  simp [MultiStorePayloadDetailedBackwardLabelsCompatible]


/--
Conditional forward correspondence for a finite payload-aware multi-store
detailed DTR execution.

The proof consumes the derivation-indexed compatibility premise one source
phase at a time. Each source head step is matched by the published detailed
runtime phase package, and the resulting LF weak step is prepended to the
weak execution obtained from the induction hypothesis.
-/
theorem multiStorePayloadDetailedSteps_forward_of_compatible
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
            targetAfter := by

  induction hSourceSteps generalizing targetBefore with

  | refl state =>
      exact
        ⟨ [],
          targetBefore,
          LF.DetailedMultiStorePayloadWeakSteps.refl
            targetBefore,
          MultiStorePayloadDetailedWeakLabelTraceCorresponds.nil,
          hStates ⟩

  | @cons
      before
      middle
      after
      sourceLabel
      remaining
      head
      tail
      inductionHypothesis =>

      change
        MultiStorePayloadDetailedForwardLabelsCompatible
          messageServers
          before
          after
          (sourceLabel :: remaining)
          targetBefore
        at hCompatible

      simp only
        [MultiStorePayloadDetailedForwardLabelsCompatible]
        at hCompatible

      rcases
        hCompatible
          middle
          head
          tail
        with
        ⟨hHeadCompatible, hContinuation⟩

      rcases
        multiStorePayloadDetailedRuntime_forwardStep
          (multiStorePayloadDetailedRuntime_phaseWeakBisimulation
            messageServers)
          head
          hStates
          hHeadCompatible
        with
        ⟨ targetHeadLabel,
          targetMiddle,
          hTargetHead,
          hHeadLabels,
          hMiddleStates ⟩

      have hTailCompatible :
          MultiStorePayloadDetailedForwardStepsCompatible
            messageServers
            tail
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
        ⟨ targetRemaining,
          targetAfter,
          hTargetTail,
          hTailLabels,
          hFinalStates ⟩

      exact
        ⟨ targetHeadLabel :: targetRemaining,
          targetAfter,
          LF.DetailedMultiStorePayloadWeakSteps.cons
            hTargetHead
            hTargetTail,
          MultiStorePayloadDetailedWeakLabelTraceCorresponds.cons
            hHeadLabels
            hTailLabels,
          hFinalStates ⟩


/--
Conditional backward correspondence for a finite payload-aware generated-LF
detailed execution.

The proof consumes the derivation-indexed compatibility premise one target
phase at a time. Each target head step is matched through the published
detailed runtime phase package. LF statement and microstep administration
remain target-only and are represented by the resulting DTR weak head step.
-/
theorem multiStorePayloadDetailedSteps_backward_of_compatible
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
            targetAfter := by

  induction hTargetSteps generalizing sourceBefore with

  | refl state =>
      exact
        ⟨ [],
          sourceBefore,
          DTR.DetailedMultiStorePayloadWeakSteps.refl
            sourceBefore,
          MultiStorePayloadDetailedWeakLabelTraceCorresponds.nil,
          hStates ⟩

  | @cons
      before
      middle
      after
      targetLabel
      remaining
      head
      tail
      inductionHypothesis =>

      change
        MultiStorePayloadDetailedBackwardLabelsCompatible
          messageServers
          sourceBefore
          before
          after
          (targetLabel :: remaining)
        at hCompatible

      simp only
        [MultiStorePayloadDetailedBackwardLabelsCompatible]
        at hCompatible

      rcases
        hCompatible
          middle
          head
          tail
        with
        ⟨hHeadCompatible, hContinuation⟩

      rcases
        multiStorePayloadDetailedRuntime_backwardStep
          (multiStorePayloadDetailedRuntime_phaseWeakBisimulation
            messageServers)
          head
          hStates
          hHeadCompatible
        with
        ⟨ sourceHeadLabel,
          sourceMiddle,
          hSourceHead,
          hHeadLabels,
          hMiddleStates ⟩

      have hTailCompatible :
          MultiStorePayloadDetailedBackwardStepsCompatible
            messageServers
            sourceMiddle
            tail := by

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
        ⟨ sourceRemaining,
          sourceAfter,
          hSourceTail,
          hTailLabels,
          hFinalStates ⟩

      exact
        ⟨ sourceHeadLabel :: sourceRemaining,
          sourceAfter,
          DTR.DetailedMultiStorePayloadWeakSteps.cons
            hSourceHead
            hSourceTail,
          MultiStorePayloadDetailedWeakLabelTraceCorresponds.cons
            hHeadLabels
            hTailLabels,
          hFinalStates ⟩

end Correctness
end Relico
