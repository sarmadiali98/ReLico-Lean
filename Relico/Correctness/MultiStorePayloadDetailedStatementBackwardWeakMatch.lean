import Relico.Correctness.MultiStorePayloadDetailedStatementForwardWeakMatch

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
A nonempty compiled payload body comes from a nonempty source body, and
its head and tail are compiled independently.
-/
theorem compileMultiStorePayloadBody_cons_invert
    {sourceBody :
      DTR.MultiStorePayloadBody}
    {targetHead :
      LF.MultiStorePayloadStmt}
    {targetTail :
      LF.MultiStorePayloadBody}
    (hCompiled :
      Translation.compileMultiStorePayloadBody
          sourceBody =
        targetHead :: targetTail) :
    ∃ sourceHead sourceTail,
      sourceBody =
          sourceHead :: sourceTail ∧
        Translation.compileMultiStorePayloadStmt
            sourceHead =
          targetHead ∧
        Translation.compileMultiStorePayloadBody
            sourceTail =
          targetTail := by

  cases sourceBody with

  | nil =>

      simp [
        Translation.compileMultiStorePayloadBody
      ] at hCompiled

  | cons sourceHead sourceTail =>

      change
        Translation.compileMultiStorePayloadStmt
              sourceHead ::
            Translation.compileMultiStorePayloadBody
              sourceTail =
          targetHead :: targetTail
        at hCompiled

      injection hCompiled with
        hHead hTail

      exact
        ⟨sourceHead,
         sourceTail,
         rfl,
         hHead,
         hTail⟩

/--
A compiled assignment head can only originate from a source assignment
head.
-/
theorem compileMultiStorePayloadBody_assign_head
    {sourceBody :
      DTR.MultiStorePayloadBody}
    {targetName :
      VarName}
    {targetExpression :
      LF.MultiStorePayloadExpr}
    {targetRemaining :
      LF.MultiStorePayloadBody}
    (hCompiled :
      Translation.compileMultiStorePayloadBody
          sourceBody =
        LF.MultiStorePayloadStmt.assign
            targetName
            targetExpression ::
          targetRemaining) :
    ∃ sourceName sourceExpression sourceRemaining,
      sourceBody =
          DTR.MultiStorePayloadStmt.assign
              sourceName
              sourceExpression ::
            sourceRemaining ∧
        Translation.compileMultiStorePayloadStmt
            (DTR.MultiStorePayloadStmt.assign
              sourceName
              sourceExpression) =
          LF.MultiStorePayloadStmt.assign
            targetName
            targetExpression ∧
        Translation.compileMultiStorePayloadBody
            sourceRemaining =
          targetRemaining := by

  obtain
    ⟨sourceHead,
     sourceRemaining,
     hSourceBody,
     hHead,
     hRemaining⟩ :=
      compileMultiStorePayloadBody_cons_invert
        hCompiled

  cases sourceHead with

  | assign sourceName sourceExpression =>

      exact
        ⟨sourceName,
         sourceExpression,
         sourceRemaining,
         hSourceBody,
         hHead,
         hRemaining⟩

  | selfSend
      sourceMessage
      sourcePayloadExpressions
      sourceDelay =>

      simp [
        Translation.compileMultiStorePayloadStmt
      ] at hHead

/--
A compiled schedule head can only originate from a source self-send
head.
-/
theorem compileMultiStorePayloadBody_schedule_head
    {sourceBody :
      DTR.MultiStorePayloadBody}
    {targetAction :
      ActionName}
    {targetPayloadExpressions :
      List LF.MultiStorePayloadExpr}
    {targetDelay :
      Delay}
    {targetRemaining :
      LF.MultiStorePayloadBody}
    (hCompiled :
      Translation.compileMultiStorePayloadBody
          sourceBody =
        LF.MultiStorePayloadStmt.schedule
            targetAction
            targetPayloadExpressions
            targetDelay ::
          targetRemaining) :
    ∃ sourceMessage
        sourcePayloadExpressions
        sourceDelay
        sourceRemaining,
      sourceBody =
          DTR.MultiStorePayloadStmt.selfSend
              sourceMessage
              sourcePayloadExpressions
              sourceDelay ::
            sourceRemaining ∧
        Translation.compileMultiStorePayloadStmt
            (DTR.MultiStorePayloadStmt.selfSend
              sourceMessage
              sourcePayloadExpressions
              sourceDelay) =
          LF.MultiStorePayloadStmt.schedule
            targetAction
            targetPayloadExpressions
            targetDelay ∧
        Translation.compileMultiStorePayloadBody
            sourceRemaining =
          targetRemaining := by

  obtain
    ⟨sourceHead,
     sourceRemaining,
     hSourceBody,
     hHead,
     hRemaining⟩ :=
      compileMultiStorePayloadBody_cons_invert
        hCompiled

  cases sourceHead with

  | assign sourceName sourceExpression =>

      simp [
        Translation.compileMultiStorePayloadStmt
      ] at hHead

  | selfSend
      sourceMessage
      sourcePayloadExpressions
      sourceDelay =>

      exact
        ⟨sourceMessage,
         sourcePayloadExpressions,
         sourceDelay,
         sourceRemaining,
         hSourceBody,
         hHead,
         hRemaining⟩

/--
Invert one successful generated payload statement step into the exact
source assignment or payload self-send that compiled to it.

The existing forward runtime-compatibility premise is reused only for
the self-send result, where appending a newly scheduled occurrence must
re-establish selection compatibility and target `PendingNotPast`.
-/
theorem multiStorePayload_statement_backward_runtime
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    (hTargetStep :
      LF.MultiStorePayloadStep
        targetBefore
        targetAfter)
    (hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore)
    (hCompatible :
      MultiStorePayloadStatementRuntimeCompatible
        messageServers
        sourceBefore
        targetBefore) :
    ∃ sourceAfter,
      DTR.MultiStorePayloadStep
          sourceBefore
          sourceAfter ∧
        MultiStorePayloadRuntimeStateCorresponds
          messageServers
          sourceAfter
          targetAfter := by

  have hBase :
      MultiStorePayloadStateCorresponds
        sourceBefore
        targetBefore :=
    hRuntime.states.states

  unfold LF.MultiStorePayloadStep at hTargetStep

  cases hBody :
      targetBefore.activeBody with

  | nil =>

      simp [
        LF.MultiStorePayloadState.step?,
        hBody
      ] at hTargetStep

  | cons targetStatement targetRemaining =>

      cases targetStatement with

      | assign targetName targetExpression =>

          cases hEvaluate :
              LF.MultiStorePayloadExpr.evaluate
                targetBefore.stateStore
                targetBefore.parameters
                targetExpression with

          | none =>

              simp [
                LF.MultiStorePayloadState.step?,
                hBody,
                hEvaluate
              ] at hTargetStep

          | some value =>

              simp [
                LF.MultiStorePayloadState.step?,
                hBody,
                hEvaluate
              ] at hTargetStep

              subst targetAfter

              have hCompiled :
                  Translation.compileMultiStorePayloadBody
                      sourceBefore.activeBody =
                    LF.MultiStorePayloadStmt.assign
                        targetName
                        targetExpression ::
                      targetRemaining := by

                calc
                  Translation.compileMultiStorePayloadBody
                      sourceBefore.activeBody =
                    targetBefore.activeBody :=
                      hBase.activeBody.symm

                  _ =
                    LF.MultiStorePayloadStmt.assign
                        targetName
                        targetExpression ::
                      targetRemaining :=
                        hBody

              obtain
                ⟨sourceName,
                 sourceExpression,
                 sourceRemaining,
                 hSourceBody,
                 hHead,
                 hRemaining⟩ :=
                  compileMultiStorePayloadBody_assign_head
                    hCompiled

              injection hHead with
                hName hExpression

              subst targetName
              subst targetExpression
              subst targetRemaining

              have hSourceEvaluate :
                  DTR.MultiStorePayloadExpr.evaluate
                      sourceBefore.stateStore
                      sourceBefore.parameters
                      sourceExpression =
                    some value := by

                rw [
                  ← compileMultiStorePayloadExpr_evaluate
                ]

                rw [
                  ← hBase.stateStore,
                  ← hBase.parameters
                ]

                exact hEvaluate

              obtain
                ⟨hSourceStep,
                 _hCanonicalTargetStep,
                 hAfterBase⟩ :=
                  multiStorePayload_assign_forward
                    hBase
                    hSourceBody
                    hSourceEvaluate

              have hAfterSelection :
                  MultiStorePayloadSelectionCompatible
                    messageServers
                    (DTR.MultiStorePayloadState.assignmentResult
                      sourceBefore
                      sourceName
                      value
                      sourceRemaining).pendingMessages
                    (LF.MultiStorePayloadState.assignmentResult
                      targetBefore
                      sourceName
                      value
                      (Translation.compileMultiStorePayloadBody
                        sourceRemaining)).pendingActions := by

                simpa [
                  DTR.MultiStorePayloadState.assignmentResult,
                  LF.MultiStorePayloadState.assignmentResult
                ] using
                  hRuntime.states.pendingEvents

              have hBeforeNotPast :
                  LF.ActionQueue.PendingNotPast
                    targetBefore.currentTag
                    targetBefore.pendingActions := by

                exact
                  hRuntime.pendingNotPast

              have hAfterNotPast :
                  (LF.MultiStorePayloadState.assignmentResult
                    targetBefore
                    sourceName
                    value
                    (Translation.compileMultiStorePayloadBody
                      sourceRemaining)).PendingNotPast := by

                change
                  LF.ActionQueue.PendingNotPast
                    (LF.MultiStorePayloadState.assignmentResult
                      targetBefore
                      sourceName
                      value
                      (Translation.compileMultiStorePayloadBody
                        sourceRemaining)).currentTag
                    (LF.MultiStorePayloadState.assignmentResult
                      targetBefore
                      sourceName
                      value
                      (Translation.compileMultiStorePayloadBody
                        sourceRemaining)).pendingActions

                simpa [
                  LF.MultiStorePayloadState.assignmentResult
                ] using
                  hBeforeNotPast

              exact
                ⟨DTR.MultiStorePayloadState.assignmentResult
                    sourceBefore
                    sourceName
                    value
                    sourceRemaining,
                 hSourceStep,
                 {
                   states :=
                     {
                       states :=
                         hAfterBase

                       pendingEvents :=
                         hAfterSelection
                     }

                   pendingNotPast :=
                     hAfterNotPast
                 }⟩

      | schedule
          targetAction
          targetPayloadExpressions
          targetDelay =>

          cases hEvaluate :
              LF.MultiStorePayloadExpr.evaluateAll
                targetBefore.stateStore
                targetBefore.parameters
                targetPayloadExpressions with

          | none =>

              simp [
                LF.MultiStorePayloadState.step?,
                hBody,
                hEvaluate
              ] at hTargetStep

          | some payload =>

              simp [
                LF.MultiStorePayloadState.step?,
                hBody,
                hEvaluate
              ] at hTargetStep

              subst targetAfter

              have hCompiled :
                  Translation.compileMultiStorePayloadBody
                      sourceBefore.activeBody =
                    LF.MultiStorePayloadStmt.schedule
                        targetAction
                        targetPayloadExpressions
                        targetDelay ::
                      targetRemaining := by

                calc
                  Translation.compileMultiStorePayloadBody
                      sourceBefore.activeBody =
                    targetBefore.activeBody :=
                      hBase.activeBody.symm

                  _ =
                    LF.MultiStorePayloadStmt.schedule
                        targetAction
                        targetPayloadExpressions
                        targetDelay ::
                      targetRemaining :=
                        hBody

              obtain
                ⟨sourceMessage,
                 sourcePayloadExpressions,
                 sourceDelay,
                 sourceRemaining,
                 hSourceBody,
                 hHead,
                 hRemaining⟩ :=
                  compileMultiStorePayloadBody_schedule_head
                    hCompiled

              injection hHead with
                hAction
                hPayloadExpressions
                hDelay

              subst targetAction
              subst targetPayloadExpressions
              subst targetDelay
              subst targetRemaining

              have hSourceEvaluate :
                  DTR.MultiStorePayloadExpr.evaluateAll
                      sourceBefore.stateStore
                      sourceBefore.parameters
                      sourcePayloadExpressions =
                    some payload := by

                rw [
                  ← compileMultiStorePayloadExprs_evaluateAll
                ]

                rw [
                  ← hBase.stateStore,
                  ← hBase.parameters
                ]

                exact hEvaluate

              obtain
                ⟨hSourceStep,
                 _hCanonicalTargetStep,
                 hAfterBase⟩ :=
                  multiStorePayload_selfSend_forward
                    hBase
                    hSourceBody
                    hSourceEvaluate

              have hCompatibleReduced :=
                hCompatible

              simp [
                MultiStorePayloadStatementRuntimeCompatible,
                hSourceBody
              ] at hCompatibleReduced

              have hCompatibleSelfSend :
                  MultiStorePayloadSelectionCompatible
                      messageServers
                      (DTR.MultiStorePayloadState.selfSendResult
                        sourceBefore
                        sourceMessage
                        payload
                        sourceDelay
                        sourceRemaining).pendingMessages
                      (LF.MultiStorePayloadState.scheduleResult
                        targetBefore
                        (Translation.actionNameFor
                          sourceMessage)
                        payload
                        sourceDelay
                        (Translation.compileMultiStorePayloadBody
                          sourceRemaining)).pendingActions ∧
                    (LF.MultiStorePayloadState.scheduleResult
                        targetBefore
                        (Translation.actionNameFor
                          sourceMessage)
                        payload
                        sourceDelay
                        (Translation.compileMultiStorePayloadBody
                          sourceRemaining)).PendingNotPast :=

                hCompatibleReduced
                  hSourceEvaluate

              exact
                ⟨DTR.MultiStorePayloadState.selfSendResult
                    sourceBefore
                    sourceMessage
                    payload
                    sourceDelay
                    sourceRemaining,
                 hSourceStep,
                 {
                   states :=
                     {
                       states :=
                         hAfterBase

                       pendingEvents :=
                         hCompatibleSelfSend.1
                     }

                   pendingNotPast :=
                     hCompatibleSelfSend.2
                 }⟩

/--
Package runtime statement inversion as a detailed backward weak-tau
match.
-/
theorem multiStorePayloadDetailedRuntime_statement_backward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore :
      DTR.MultiStorePayloadState}
    {targetBefore targetAfter :
      LF.MultiStorePayloadState}
    (hTargetStep :
      LF.MultiStorePayloadStep
        targetBefore
        targetAfter)
    (hStates :
      MultiStorePayloadDetailedRuntimeStateCorresponds
        messageServers
        (.stable sourceBefore)
        (.stable targetBefore))
    (hCompatible :
      MultiStorePayloadStatementRuntimeCompatible
        messageServers
        sourceBefore
        targetBefore) :
    MultiStorePayloadDetailedBackwardMatch
      messageServers
      .tau
      (.stable targetAfter)
      (.stable sourceBefore) := by

  have hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    multiStorePayloadDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨sourceAfter,
     hSourceStep,
     hAfter⟩ :=
      multiStorePayload_statement_backward_runtime
        hTargetStep
        hRuntime
        hCompatible

  exact
    ⟨.tau,
     .stable sourceAfter,
     DTR.detailedMultiStorePayloadStatement_is_weak
       hSourceStep,
     MultiStorePayloadDetailedLabelCorresponds.tau,
     multiStorePayloadDetailedRuntime_stable_iff.mpr
       hAfter⟩

end Correctness
end Relico
