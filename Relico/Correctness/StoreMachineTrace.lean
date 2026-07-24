import Relico.Correctness.StoreMachine
import Relico.DTR.StoreMachineTraceSemantics
import Relico.DTR.StoreRuntimeWellFormed
import Relico.LF.StoreMachineTraceSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Pointwise correspondence between finite source and generated-LF
store-machine traces.
-/
inductive StoreMachineTraceCorresponds :
    List DTR.StoreMachineLabel →
    List LF.StoreMachineLabel →
    Prop where

  | nil :
      StoreMachineTraceCorresponds
        []
        []

  | cons
      {sourceLabel : DTR.StoreMachineLabel}
      {targetLabel : LF.StoreMachineLabel}
      {sourceRemaining : List DTR.StoreMachineLabel}
      {targetRemaining : List LF.StoreMachineLabel}
      (hHead :
        StoreMachineLabelCorresponds
          sourceLabel
          targetLabel)
      (hTail :
        StoreMachineTraceCorresponds
          sourceRemaining
          targetRemaining) :

      StoreMachineTraceCorresponds
        (sourceLabel :: sourceRemaining)
        (targetLabel :: targetRemaining)

/--
Compatibility evidence for a complete forward source execution.

The recursive core is indexed by the source machine-label list rather
than by a proof-valued execution object. For each possible decomposition
of the source execution, it supplies compatibility for the first step
and compatibility for the remaining execution after a matching target
step.
-/
def StoreForwardMachineLabelsCompatible
    (declaredVariables : List VarName)
    (messageServer : MsgName)
    (messageBody : DTR.Body)
    (sourceBefore sourceAfter : DTR.StoreState)
    (sourceLabels : List DTR.StoreMachineLabel)
    (targetBefore : LF.StoreState) :
    Prop :=

  match sourceLabels with

  | [] =>
      sourceBefore =
        sourceAfter

  | sourceLabel :: sourceRemainingLabels =>
      ∀ sourceMiddle,
        DTR.StoreMachineStep
            declaredVariables
            messageServer
            messageBody
            sourceBefore
            sourceLabel
            sourceMiddle →
        DTR.StoreMachineSteps
            declaredVariables
            messageServer
            messageBody
            sourceMiddle
            sourceRemainingLabels
            sourceAfter →
        StoreForwardMachineCompatible
            sourceLabel
            sourceMiddle
            targetBefore ∧
          ∀ {targetLabel targetMiddle},
            LF.StoreMachineStep
                declaredVariables
                (Translation.actionNameFor
                  messageServer)
                (Translation.compileBody
                  messageBody)
                targetBefore
                targetLabel
                targetMiddle →
            StoreMachineLabelCorresponds
                sourceLabel
                targetLabel →
            StoreStateCorresponds
                sourceMiddle
                targetMiddle →
            StoreForwardMachineLabelsCompatible
              declaredVariables
              messageServer
              messageBody
              sourceMiddle
              sourceAfter
              sourceRemainingLabels
              targetMiddle

termination_by sourceLabels.length

/--
Compatibility for a concrete source execution.

The execution proof fixes the source endpoints and label sequence. The
recursive compatibility definition itself depends only on those
indices, avoiding elimination from a proof into computational data.
-/
def StoreForwardMachineStepsCompatible
    (declaredVariables : List VarName)
    (messageServer : MsgName)
    (messageBody : DTR.Body)
    {sourceBefore sourceAfter : DTR.StoreState}
    {sourceLabels : List DTR.StoreMachineLabel}
    (_hSteps :
      DTR.StoreMachineSteps
        declaredVariables
        messageServer
        messageBody
        sourceBefore
        sourceLabels
        sourceAfter)
    (targetBefore : LF.StoreState) :
    Prop :=

  StoreForwardMachineLabelsCompatible
    declaredVariables
    messageServer
    messageBody
    sourceBefore
    sourceAfter
    sourceLabels
    targetBefore

/--
Finite DTR store-machine executions preserve runtime well-formedness.
-/
theorem dtrStoreMachineSteps_preserve_runtimeWellFormed
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {before after : DTR.StoreState}
    {labels : List DTR.StoreMachineLabel}
    (hSteps :
      DTR.StoreMachineSteps
        declaredVariables
        messageServer
        messageBody
        before
        labels
        after)
    (hMessageBody :
      DTR.Body.StoreWellFormed
        declaredVariables
        messageServer
        messageBody)
    (hBefore :
      DTR.StoreState.RuntimeWellFormed
        declaredVariables
        messageServer
        before) :
    DTR.StoreState.RuntimeWellFormed
      declaredVariables
      messageServer
      after := by

  induction hSteps with

  | refl state =>
      exact hBefore

  | cons hHead hTail inductionHypothesis =>
      have hMiddle :
          DTR.StoreState.RuntimeWellFormed
            declaredVariables
            messageServer
            _ :=

        DTR.StoreMachineStep.preserves_runtimeWellFormed
          hHead
          hMessageBody
          hBefore

      exact
        inductionHypothesis
          hMiddle

/--
Conditional forward simulation for finite combined store-machine
executions.
-/
theorem storeMachineSteps_forward_of_compatible
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {sourceBefore sourceAfter : DTR.StoreState}
    {sourceLabels : List DTR.StoreMachineLabel}
    {targetBefore : LF.StoreState}
    (hSourceSteps :
      DTR.StoreMachineSteps
        declaredVariables
        messageServer
        messageBody
        sourceBefore
        sourceLabels
        sourceAfter)
    (hStates :
      StoreStateCorresponds
        sourceBefore
        targetBefore)
    (hCompatible :
      StoreForwardMachineStepsCompatible
        declaredVariables
        messageServer
        messageBody
        hSourceSteps
        targetBefore) :
    ∃ targetLabels targetAfter,
      LF.StoreMachineSteps
          declaredVariables
          (Translation.actionNameFor
            messageServer)
          (Translation.compileBody
            messageBody)
          targetBefore
          targetLabels
          targetAfter ∧
      StoreMachineTraceCorresponds
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
         LF.StoreMachineSteps.refl
           targetBefore,
         StoreMachineTraceCorresponds.nil,
         hStates⟩

  | cons hHead hTail inductionHypothesis =>
      unfold
        StoreForwardMachineStepsCompatible
        at hCompatible

      simp only [
        StoreForwardMachineLabelsCompatible
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
          storeMachineStep_forward
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
          StoreForwardMachineStepsCompatible
            declaredVariables
            messageServer
            messageBody
            hTail
            targetMiddle := by

        unfold
          StoreForwardMachineStepsCompatible

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
         LF.StoreMachineSteps.cons
           hTargetHead
           hTargetTail,
         StoreMachineTraceCorresponds.cons
           hHeadLabels
           hTailLabels,
         hFinalStates⟩

/--
Unconditional backward simulation for finite generated-LF combined
store-machine executions.

Runtime well-formedness supplies the body and pending-message premises
required by each backward machine step and is preserved throughout the
recovered source execution.
-/
theorem storeMachineSteps_backward
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {sourceBefore : DTR.StoreState}
    {targetBefore targetAfter : LF.StoreState}
    {targetLabels : List LF.StoreMachineLabel}
    (hTargetSteps :
      LF.StoreMachineSteps
        declaredVariables
        (Translation.actionNameFor
          messageServer)
        (Translation.compileBody
          messageBody)
        targetBefore
        targetLabels
        targetAfter)
    (hStates :
      StoreStateCorresponds
        sourceBefore
        targetBefore)
    (hMessageBody :
      DTR.Body.StoreWellFormed
        declaredVariables
        messageServer
        messageBody)
    (hSourceWellFormed :
      DTR.StoreState.RuntimeWellFormed
        declaredVariables
        messageServer
        sourceBefore) :
    ∃ sourceLabels sourceAfter,
      DTR.StoreMachineSteps
          declaredVariables
          messageServer
          messageBody
          sourceBefore
          sourceLabels
          sourceAfter ∧
      StoreMachineTraceCorresponds
        sourceLabels
        targetLabels ∧
      StoreStateCorresponds
        sourceAfter
        targetAfter ∧
      DTR.StoreState.RuntimeWellFormed
        declaredVariables
        messageServer
        sourceAfter := by

  induction hTargetSteps generalizing sourceBefore with

  | refl targetState =>
      exact
        ⟨[],
         sourceBefore,
         DTR.StoreMachineSteps.refl
           sourceBefore,
         StoreMachineTraceCorresponds.nil,
         hStates,
         hSourceWellFormed⟩

  | cons hHead hTail inductionHypothesis =>
      rcases
          storeMachineStep_backward
            hHead
            hStates
            hSourceWellFormed.activeBody
            hSourceWellFormed.pendingTargets
        with
          ⟨sourceLabel,
           sourceMiddle,
           hSourceHead,
           hHeadLabels,
           hMiddleStates⟩

      have hMiddleWellFormed :
          DTR.StoreState.RuntimeWellFormed
            declaredVariables
            messageServer
            sourceMiddle :=

        DTR.StoreMachineStep.preserves_runtimeWellFormed
          hSourceHead
          hMessageBody
          hSourceWellFormed

      rcases
          inductionHypothesis
            hMiddleStates
            hMiddleWellFormed
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
         DTR.StoreMachineSteps.cons
           hSourceHead
           hSourceTail,
         StoreMachineTraceCorresponds.cons
           hHeadLabels
           hTailLabels,
         hFinalStates,
         hFinalWellFormed⟩

end Correctness
end Relico
