import Relico.Correctness.MultiStoreMachine
import Relico.Correctness.PriorityMachineTiming
import Relico.DTR.MultiStoreMachineTraceSemantics
import Relico.DTR.MultiStoreRuntimeWellFormed
import Relico.LF.MultiStoreMachineTraceSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Pointwise correspondence between finite source and generated-LF
multi-server machine traces.
-/
inductive MultiStoreMachineTraceCorresponds :
    List DTR.MultiStoreMachineLabel →
    List LF.MultiStoreMachineLabel →
    Prop where

  | nil :
      MultiStoreMachineTraceCorresponds
        []
        []

  | cons
      {sourceLabel : DTR.MultiStoreMachineLabel}
      {targetLabel : LF.MultiStoreMachineLabel}
      {sourceRemaining :
        List DTR.MultiStoreMachineLabel}
      {targetRemaining :
        List LF.MultiStoreMachineLabel}
      (hHead :
        MultiStoreMachineLabelCorresponds
          sourceLabel
          targetLabel)
      (hTail :
        MultiStoreMachineTraceCorresponds
          sourceRemaining
          targetRemaining) :

      MultiStoreMachineTraceCorresponds
        (sourceLabel :: sourceRemaining)
        (targetLabel :: targetRemaining)

/--
Compatibility evidence indexed by a source multi-server machine-label
sequence.

For every possible first-step decomposition, this predicate supplies
the LF scheduler compatibility needed by that step and recursively
supplies compatibility after every corresponding generated target
step.
-/
def MultiStoreForwardMachineLabelsCompatible
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    (sourceBefore sourceAfter : DTR.StoreState)
    (sourceLabels :
      List DTR.MultiStoreMachineLabel)
    (targetBefore : LF.StoreState) :
    Prop :=

  match sourceLabels with

  | [] =>
      sourceBefore =
        sourceAfter

  | sourceLabel :: sourceRemainingLabels =>
      ∀ sourceMiddle,
        DTR.MultiStoreMachineStep
            declaredVariables
            messageServers
            sourceBefore
            sourceLabel
            sourceMiddle →
        DTR.MultiStoreMachineSteps
            declaredVariables
            messageServers
            sourceMiddle
            sourceRemainingLabels
            sourceAfter →
        MultiStoreForwardMachineCompatible
            sourceLabel
            sourceMiddle
            targetBefore ∧
          ∀ {targetLabel targetMiddle},
            LF.MultiStoreMachineStep
                declaredVariables
                (Translation.compileLogicalActions
                  messageServers)
                (Translation.compileMessageReactions
                  messageServers)
                targetBefore
                targetLabel
                targetMiddle →
            MultiStoreMachineLabelCorresponds
                sourceLabel
                targetLabel →
            StoreStateCorresponds
                sourceMiddle
                targetMiddle →
            MultiStoreForwardMachineLabelsCompatible
              declaredVariables
              messageServers
              sourceMiddle
              sourceAfter
              sourceRemainingLabels
              targetMiddle

termination_by sourceLabels.length

/--
Compatibility for one concrete finite source execution.
-/
def MultiStoreForwardMachineStepsCompatible
    (declaredVariables : List VarName)
    (messageServers : List DTR.MessageServer)
    {sourceBefore sourceAfter : DTR.StoreState}
    {sourceLabels :
      List DTR.MultiStoreMachineLabel}
    (_hSteps :
      DTR.MultiStoreMachineSteps
        declaredVariables
        messageServers
        sourceBefore
        sourceLabels
        sourceAfter)
    (targetBefore : LF.StoreState) :
    Prop :=

  MultiStoreForwardMachineLabelsCompatible
    declaredVariables
    messageServers
    sourceBefore
    sourceAfter
    sourceLabels
    targetBefore

/--
Finite source multi-server executions preserve runtime
well-formedness.
-/
theorem dtrMultiStoreMachineSteps_preserve_runtimeWellFormed
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {before after : DTR.StoreState}
    {labels :
      List DTR.MultiStoreMachineLabel}
    (hSteps :
      DTR.MultiStoreMachineSteps
        declaredVariables
        messageServers
        before
        labels
        after)
    (hMessageBodies :
      ∀ messageServer,
        messageServer ∈
          messageServers →
        DTR.Body.MultiStoreWellFormed
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          messageServer.body)
    (hBefore :
      DTR.StoreState.MultiStoreRuntimeWellFormed
        declaredVariables
        messageServers
        before) :
    DTR.StoreState.MultiStoreRuntimeWellFormed
      declaredVariables
      messageServers
      after := by

  induction hSteps with

  | refl state =>
      exact hBefore

  | cons hHead hTail inductionHypothesis =>
      have hMiddle :
          DTR.StoreState.MultiStoreRuntimeWellFormed
            declaredVariables
            messageServers
            _ :=

        DTR.MultiStoreMachineStep.preserves_runtimeWellFormed
          hHead
          hMessageBodies
          hBefore

      exact
        inductionHypothesis
          hMiddle

/--
Conditional forward simulation for arbitrary finite multi-server
machine executions.
-/
theorem multiStoreMachineSteps_forward_of_compatible
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore sourceAfter : DTR.StoreState}
    {sourceLabels :
      List DTR.MultiStoreMachineLabel}
    {targetBefore : LF.StoreState}
    (hSourceSteps :
      DTR.MultiStoreMachineSteps
        declaredVariables
        messageServers
        sourceBefore
        sourceLabels
        sourceAfter)
    (hStates :
      StoreStateCorresponds
        sourceBefore
        targetBefore)
    (hCompatible :
      MultiStoreForwardMachineStepsCompatible
        declaredVariables
        messageServers
        hSourceSteps
        targetBefore) :
    ∃ targetLabels targetAfter,
      LF.MultiStoreMachineSteps
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          (Translation.compileMessageReactions
            messageServers)
          targetBefore
          targetLabels
          targetAfter ∧
      MultiStoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter := by

  induction hSourceSteps generalizing targetBefore with

  | refl sourceState =>
      exact
        ⟨[],
         targetBefore,
         LF.MultiStoreMachineSteps.refl
           targetBefore,
         MultiStoreMachineTraceCorresponds.nil,
         hStates⟩

  | cons hHead hTail inductionHypothesis =>
      unfold
        MultiStoreForwardMachineStepsCompatible
        at hCompatible

      simp only [
        MultiStoreForwardMachineLabelsCompatible
      ] at hCompatible

      rcases
          hCompatible
            _
            hHead
            hTail
        with
          ⟨hHeadCompatible,
           hTailCompatible⟩

      rcases
          multiStoreMachineStep_forward
            hHead
            hStates
            hHeadCompatible
        with
          ⟨targetLabel,
           targetMiddle,
           hTargetHead,
           hHeadLabels,
           hMiddleStates⟩

      have hRemainingCompatible :
          MultiStoreForwardMachineStepsCompatible
            declaredVariables
            messageServers
            hTail
            targetMiddle := by

        unfold
          MultiStoreForwardMachineStepsCompatible

        exact
          hTailCompatible
            hTargetHead
            hHeadLabels
            hMiddleStates

      rcases
          inductionHypothesis
            hMiddleStates
            hRemainingCompatible
        with
          ⟨targetRemainingLabels,
           targetAfter,
           hTargetTail,
           hTailLabels,
           hFinalStates⟩

      exact
        ⟨targetLabel :: targetRemainingLabels,
         targetAfter,
         LF.MultiStoreMachineSteps.cons
           hTargetHead
           hTargetTail,
         MultiStoreMachineTraceCorresponds.cons
           hHeadLabels
           hTailLabels,
         hFinalStates⟩

/--
Backward simulation for finite generated-LF multi-server machine
executions in the positive-delay priority timing fragment.

Runtime well-formedness supplies the structural source-body premise.
Source priority timing and target zero-microstep invariants are preserved
through every recovered execution step.
-/
theorem multiStoreMachineSteps_backward
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {targetLabels :
      List LF.MultiStoreMachineLabel}
    (hTargetSteps :
      LF.MultiStoreMachineSteps
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetBefore
        targetLabels
        targetAfter)
    (hStates :
      StoreStateCorresponds
        sourceBefore
        targetBefore)
    (hTargetMicrostepsZero :
      LF.StoreState.PendingMicrostepsZero
        targetBefore)
    (hMessageBodies :
      ∀ messageServer,
        messageServer ∈
          messageServers →
        DTR.Body.MultiStoreWellFormed
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          messageServer.body)
    (hMessageTiming :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.PriorityTimingWellFormed
            messageServer.body)
    (hSourceWellFormed :
      DTR.StoreState.MultiStoreRuntimeWellFormed
        declaredVariables
        messageServers
        sourceBefore)
    (hSourceTiming :
      DTR.Body.PriorityTimingWellFormed
        sourceBefore.activeBody) :
    ∃ sourceLabels sourceAfter,
      DTR.MultiStoreMachineSteps
          declaredVariables
          messageServers
          sourceBefore
          sourceLabels
          sourceAfter ∧
      MultiStoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter ∧
      DTR.StoreState.MultiStoreRuntimeWellFormed
        declaredVariables
        messageServers
        sourceAfter := by

  induction hTargetSteps generalizing sourceBefore with

  | refl targetState =>
      exact
        ⟨[],
         sourceBefore,
         DTR.MultiStoreMachineSteps.refl
           sourceBefore,
         MultiStoreMachineTraceCorresponds.nil,
         hStates,
         hSourceWellFormed⟩

  | cons hHead hTail inductionHypothesis =>
      rcases
          multiStoreMachineStep_backward
            hHead
            hStates
            hTargetMicrostepsZero
            hSourceWellFormed.activeBody
        with
          ⟨sourceLabel,
           sourceMiddle,
           hSourceHead,
           hHeadLabels,
           hMiddleStates⟩

      have hMiddleWellFormed :
          DTR.StoreState.MultiStoreRuntimeWellFormed
            declaredVariables
            messageServers
            sourceMiddle :=

        DTR.MultiStoreMachineStep.preserves_runtimeWellFormed
          hSourceHead
          hMessageBodies
          hSourceWellFormed


      have hMiddleSourceTiming :
          DTR.Body.PriorityTimingWellFormed
            sourceMiddle.activeBody :=

        DTR.MultiStoreMachineStep.preserves_priorityTimingWellFormed
          hSourceHead
          hMessageTiming
          hSourceTiming

      have hMiddleTargetMicrostepsZero :
          LF.StoreState.PendingMicrostepsZero
            _ :=

        targetMultiStoreMachineStep_preserves_pendingMicrostepsZero
          hHead
          hStates
          hSourceTiming
          hTargetMicrostepsZero

      rcases
          inductionHypothesis
            hMiddleStates
            hMiddleTargetMicrostepsZero
            hMiddleWellFormed
            hMiddleSourceTiming
        with
          ⟨sourceRemainingLabels,
           sourceAfter,
           hSourceTail,
           hTailLabels,
           hFinalStates,
           hFinalWellFormed⟩

      exact
        ⟨sourceLabel :: sourceRemainingLabels,
         sourceAfter,
         DTR.MultiStoreMachineSteps.cons
           hSourceHead
           hSourceTail,
         MultiStoreMachineTraceCorresponds.cons
           hHeadLabels
           hTailLabels,
         hFinalStates,
         hFinalWellFormed⟩

end Correctness
end Relico
