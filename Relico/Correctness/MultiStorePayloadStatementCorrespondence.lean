import Relico.Correctness.PayloadCorrespondence
import Relico.DTR.MultiStorePayloadSemantics
import Relico.LF.MultiStorePayloadSemantics
import Relico.Translation.MultiStorePayloadBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compiled expressions evaluate to exactly the same integer result as
their source expressions.
-/
@[simp]
theorem compileMultiStorePayloadExpr_evaluate
    (stateStore :
      StateStore)
    (parameters :
      ParameterStore)
    (expression :
      DTR.MultiStorePayloadExpr) :
    LF.MultiStorePayloadExpr.evaluate
        stateStore
        parameters
        (Translation.compileMultiStorePayloadExpr
          expression) =
      DTR.MultiStorePayloadExpr.evaluate
        stateStore
        parameters
        expression := by

  cases expression <;>
    rfl

/--
Compilation preserves evaluation of complete ordered payload lists.
-/
@[simp]
theorem compileMultiStorePayloadExprs_evaluateAll
    (stateStore :
      StateStore)
    (parameters :
      ParameterStore)
    (expressions :
      List DTR.MultiStorePayloadExpr) :
    LF.MultiStorePayloadExpr.evaluateAll
        stateStore
        parameters
        (Translation.compileMultiStorePayloadExprs
          expressions) =
      DTR.MultiStorePayloadExpr.evaluateAll
        stateStore
        parameters
        expressions := by

  induction expressions with

  | nil =>
      rfl

  | cons expression remaining inductionHypothesis =>
      simp only [
        Translation.compileMultiStorePayloadExprs,
        List.map_cons,
        DTR.MultiStorePayloadExpr.evaluateAll,
        LF.MultiStorePayloadExpr.evaluateAll
      ]

      have hRemaining :
          LF.MultiStorePayloadExpr.evaluateAll
              stateStore
              parameters
              (List.map
                Translation.compileMultiStorePayloadExpr
                remaining) =
            DTR.MultiStorePayloadExpr.evaluateAll
              stateStore
              parameters
              remaining := by

        simpa [
          Translation.compileMultiStorePayloadExprs
        ] using
          inductionHypothesis

      rw [
        compileMultiStorePayloadExpr_evaluate,
        hRemaining
      ]

      rfl

/--
Correspondence between local source and generated target runtime states.

Target microsteps are intentionally not projected into source state.
Only metric time is equated. Pending queues retain exact ordered
payload correspondence and occurrence multiplicity.
-/
structure MultiStorePayloadStateCorresponds
    (sourceState :
      DTR.MultiStorePayloadState)
    (targetState :
      LF.MultiStorePayloadState) :
    Prop where

  currentTime :
    targetState.currentTag.time =
      sourceState.currentTime

  stateStore :
    targetState.stateStore =
      sourceState.stateStore

  parameters :
    targetState.parameters =
      sourceState.parameters

  pendingQueues :
    Correctness.PayloadQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions

  activeBody :
    targetState.activeBody =
      Translation.compileMultiStorePayloadBody
        sourceState.activeBody

/--
A successful source assignment and its compiled LF assignment execute
in lockstep and preserve local state correspondence.
-/
theorem multiStorePayload_assign_forward
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore :
      LF.MultiStorePayloadState}
    {targetName :
      VarName}
    {sourceExpression :
      DTR.MultiStorePayloadExpr}
    {sourceRemaining :
      DTR.MultiStorePayloadBody}
    {value :
      Int}
    (hStates :
      MultiStorePayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSourceBody :
      sourceBefore.activeBody =
        DTR.MultiStorePayloadStmt.assign
            targetName
            sourceExpression ::
          sourceRemaining)
    (hSourceEvaluate :
      DTR.MultiStorePayloadExpr.evaluate
          sourceBefore.stateStore
          sourceBefore.parameters
          sourceExpression =
        some value) :
    DTR.MultiStorePayloadStep
        sourceBefore
        (DTR.MultiStorePayloadState.assignmentResult
          sourceBefore
          targetName
          value
          sourceRemaining) ∧
      LF.MultiStorePayloadStep
        targetBefore
        (LF.MultiStorePayloadState.assignmentResult
          targetBefore
          targetName
          value
          (Translation.compileMultiStorePayloadBody
            sourceRemaining)) ∧
      MultiStorePayloadStateCorresponds
        (DTR.MultiStorePayloadState.assignmentResult
          sourceBefore
          targetName
          value
          sourceRemaining)
        (LF.MultiStorePayloadState.assignmentResult
          targetBefore
          targetName
          value
          (Translation.compileMultiStorePayloadBody
            sourceRemaining)) := by

  have hTargetBody :
      targetBefore.activeBody =
        LF.MultiStorePayloadStmt.assign
            targetName
            (Translation.compileMultiStorePayloadExpr
              sourceExpression) ::
          Translation.compileMultiStorePayloadBody
            sourceRemaining := by

    calc
      targetBefore.activeBody =
          Translation.compileMultiStorePayloadBody
            sourceBefore.activeBody :=
        hStates.activeBody

      _ =
          Translation.compileMultiStorePayloadBody
            (DTR.MultiStorePayloadStmt.assign
                targetName
                sourceExpression ::
              sourceRemaining) := by
            rw [hSourceBody]

      _ =
          LF.MultiStorePayloadStmt.assign
              targetName
              (Translation.compileMultiStorePayloadExpr
                sourceExpression) ::
            Translation.compileMultiStorePayloadBody
              sourceRemaining := by
            rfl

  have hTargetEvaluate :
      LF.MultiStorePayloadExpr.evaluate
          targetBefore.stateStore
          targetBefore.parameters
          (Translation.compileMultiStorePayloadExpr
            sourceExpression) =
        some value := by

    calc
      LF.MultiStorePayloadExpr.evaluate
          targetBefore.stateStore
          targetBefore.parameters
          (Translation.compileMultiStorePayloadExpr
            sourceExpression) =
        DTR.MultiStorePayloadExpr.evaluate
          targetBefore.stateStore
          targetBefore.parameters
          sourceExpression := by
            exact
              compileMultiStorePayloadExpr_evaluate
                targetBefore.stateStore
                targetBefore.parameters
                sourceExpression

      _ =
        DTR.MultiStorePayloadExpr.evaluate
          sourceBefore.stateStore
          sourceBefore.parameters
          sourceExpression := by
            rw [
              hStates.stateStore,
              hStates.parameters
            ]

      _ =
        some value :=
          hSourceEvaluate

  refine
    ⟨?_, ?_, ?_⟩

  · simp [
      DTR.MultiStorePayloadStep,
      DTR.MultiStorePayloadState.step?,
      hSourceBody,
      hSourceEvaluate
    ]

  · simp [
      LF.MultiStorePayloadStep,
      LF.MultiStorePayloadState.step?,
      hTargetBody,
      hTargetEvaluate
    ]

  · refine {
      currentTime := ?_
      stateStore := ?_
      parameters := ?_
      pendingQueues := ?_
      activeBody := ?_
    }

    · simpa [
        DTR.MultiStorePayloadState.assignmentResult,
        LF.MultiStorePayloadState.assignmentResult
      ] using
        hStates.currentTime

    · simpa [
        DTR.MultiStorePayloadState.assignmentResult,
        LF.MultiStorePayloadState.assignmentResult
      ] using
        congrArg
          (fun store =>
            StateStore.update
              store
              targetName
              value)
          hStates.stateStore

    · simpa [
        DTR.MultiStorePayloadState.assignmentResult,
        LF.MultiStorePayloadState.assignmentResult
      ] using
        hStates.parameters

    · simpa [
        DTR.MultiStorePayloadState.assignmentResult,
        LF.MultiStorePayloadState.assignmentResult
      ] using
        hStates.pendingQueues

    · rfl

/--
A successful payload-bearing source self-send and the generated LF
schedule statement preserve exact payload order, metric arrival time,
and queue occurrence multiplicity.
-/
theorem multiStorePayload_selfSend_forward
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore :
      LF.MultiStorePayloadState}
    {messageName :
      MsgName}
    {sourcePayloadExpressions :
      List DTR.MultiStorePayloadExpr}
    {sourceRemaining :
      DTR.MultiStorePayloadBody}
    {delay :
      Delay}
    {payload :
      Payload}
    (hStates :
      MultiStorePayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSourceBody :
      sourceBefore.activeBody =
        DTR.MultiStorePayloadStmt.selfSend
            messageName
            sourcePayloadExpressions
            delay ::
          sourceRemaining)
    (hSourceEvaluate :
      DTR.MultiStorePayloadExpr.evaluateAll
          sourceBefore.stateStore
          sourceBefore.parameters
          sourcePayloadExpressions =
        some payload) :
    DTR.MultiStorePayloadStep
        sourceBefore
        (DTR.MultiStorePayloadState.selfSendResult
          sourceBefore
          messageName
          payload
          delay
          sourceRemaining) ∧
      LF.MultiStorePayloadStep
        targetBefore
        (LF.MultiStorePayloadState.scheduleResult
          targetBefore
          (Translation.actionNameFor
            messageName)
          payload
          delay
          (Translation.compileMultiStorePayloadBody
            sourceRemaining)) ∧
      MultiStorePayloadStateCorresponds
        (DTR.MultiStorePayloadState.selfSendResult
          sourceBefore
          messageName
          payload
          delay
          sourceRemaining)
        (LF.MultiStorePayloadState.scheduleResult
          targetBefore
          (Translation.actionNameFor
            messageName)
          payload
          delay
          (Translation.compileMultiStorePayloadBody
            sourceRemaining)) := by

  have hTargetBody :
      targetBefore.activeBody =
        LF.MultiStorePayloadStmt.schedule
            (Translation.actionNameFor
              messageName)
            (Translation.compileMultiStorePayloadExprs
              sourcePayloadExpressions)
            delay ::
          Translation.compileMultiStorePayloadBody
            sourceRemaining := by

    calc
      targetBefore.activeBody =
          Translation.compileMultiStorePayloadBody
            sourceBefore.activeBody :=
        hStates.activeBody

      _ =
          Translation.compileMultiStorePayloadBody
            (DTR.MultiStorePayloadStmt.selfSend
                messageName
                sourcePayloadExpressions
                delay ::
              sourceRemaining) := by
            rw [hSourceBody]

      _ =
          LF.MultiStorePayloadStmt.schedule
              (Translation.actionNameFor
                messageName)
              (Translation.compileMultiStorePayloadExprs
                sourcePayloadExpressions)
              delay ::
            Translation.compileMultiStorePayloadBody
              sourceRemaining := by
            rfl

  have hTargetEvaluate :
      LF.MultiStorePayloadExpr.evaluateAll
          targetBefore.stateStore
          targetBefore.parameters
          (Translation.compileMultiStorePayloadExprs
            sourcePayloadExpressions) =
        some payload := by

    calc
      LF.MultiStorePayloadExpr.evaluateAll
          targetBefore.stateStore
          targetBefore.parameters
          (Translation.compileMultiStorePayloadExprs
            sourcePayloadExpressions) =
        DTR.MultiStorePayloadExpr.evaluateAll
          targetBefore.stateStore
          targetBefore.parameters
          sourcePayloadExpressions := by
            exact
              compileMultiStorePayloadExprs_evaluateAll
                targetBefore.stateStore
                targetBefore.parameters
                sourcePayloadExpressions

      _ =
        DTR.MultiStorePayloadExpr.evaluateAll
          sourceBefore.stateStore
          sourceBefore.parameters
          sourcePayloadExpressions := by
            rw [
              hStates.stateStore,
              hStates.parameters
            ]

      _ =
        some payload :=
          hSourceEvaluate

  refine
    ⟨?_, ?_, ?_⟩

  · simp [
      DTR.MultiStorePayloadStep,
      DTR.MultiStorePayloadState.step?,
      hSourceBody,
      hSourceEvaluate
    ]

  · simp [
      LF.MultiStorePayloadStep,
      LF.MultiStorePayloadState.step?,
      hTargetBody,
      hTargetEvaluate
    ]

  · refine {
      currentTime := ?_
      stateStore := ?_
      parameters := ?_
      pendingQueues := ?_
      activeBody := ?_
    }

    · simpa [
        DTR.MultiStorePayloadState.selfSendResult,
        LF.MultiStorePayloadState.scheduleResult
      ] using
        hStates.currentTime

    · simpa [
        DTR.MultiStorePayloadState.selfSendResult,
        LF.MultiStorePayloadState.scheduleResult
      ] using
        hStates.stateStore

    · simpa [
        DTR.MultiStorePayloadState.selfSendResult,
        LF.MultiStorePayloadState.scheduleResult
      ] using
        hStates.parameters

    · simpa [
        DTR.MultiStorePayloadState.selfSendResult,
        LF.MultiStorePayloadState.scheduleResult
      ] using
        (Correctness.payloadQueueCorresponds_append_scheduleWithPayload
          hStates.pendingQueues
          sourceBefore.currentTime
          targetBefore.currentTag
          messageName
          payload
          delay
          hStates.currentTime)

    · rfl

end Correctness
end Relico
