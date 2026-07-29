import Relico.Correctness.MultiStorePayloadDetailedDispatchWeakMatches
import Relico.Correctness.MultiStorePayloadStatementCorrespondence
import Relico.Correctness.MultiStorePayloadRuntimeStateCorrespondence

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Runtime preservation obligation for a payload statement.

Assignments preserve queues and target logical time directly. For self-send,
the premise requires selection compatibility and `PendingNotPast` for the
exact source and target result states constructed by the existing semantics.
-/
def MultiStorePayloadStatementRuntimeCompatible
    (messageServers :
      List DTR.MultiStorePayloadMessageServer)
    (sourceBefore :
      DTR.MultiStorePayloadState)
    (targetBefore :
      LF.MultiStorePayloadState) :
    Prop :=

  match sourceBefore.activeBody with

  | (.selfSend
        messageName
        payloadExpressions
        delay) ::
      sourceRemaining =>

      ∀ {payload : Payload},

        DTR.MultiStorePayloadExpr.evaluateAll
            sourceBefore.stateStore
            sourceBefore.parameters
            payloadExpressions =
          some payload →

        MultiStorePayloadSelectionCompatible
            messageServers
            (sourceBefore.selfSendResult
              messageName
              payload
              delay
              sourceRemaining).pendingMessages
            (targetBefore.scheduleResult
              (Translation.actionNameFor
                messageName)
              payload
              delay
              (Translation.compileMultiStorePayloadBody
                sourceRemaining)).pendingActions ∧

          (targetBefore.scheduleResult
              (Translation.actionNameFor
                messageName)
              payload
              delay
              (Translation.compileMultiStorePayloadBody
                sourceRemaining)).PendingNotPast

  | _ =>
      True

/--
Forward runtime correspondence for one payload assignment or self-send
statement.
-/
theorem multiStorePayload_statement_forward_runtime
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {targetBefore :
      LF.MultiStorePayloadState}
    (hSourceStep :
      DTR.MultiStorePayloadStep
        sourceBefore
        sourceAfter)
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
    ∃ targetAfter,
      LF.MultiStorePayloadStep
          targetBefore
          targetAfter ∧
        MultiStorePayloadRuntimeStateCorresponds
          messageServers
          sourceAfter
          targetAfter := by

  have hBase :
      MultiStorePayloadStateCorresponds
        sourceBefore
        targetBefore :=
    hRuntime.states.states

  unfold DTR.MultiStorePayloadStep at hSourceStep

  cases hBody :
      sourceBefore.activeBody with

  | nil =>

      simp [
        DTR.MultiStorePayloadState.step?,
        hBody
      ] at hSourceStep

  | cons statement sourceRemaining =>

      cases statement with

      | assign targetName sourceExpression =>

          cases hEvaluate :
              DTR.MultiStorePayloadExpr.evaluate
                sourceBefore.stateStore
                sourceBefore.parameters
                sourceExpression with

          | none =>

              simp [
                DTR.MultiStorePayloadState.step?,
                hBody,
                hEvaluate
              ] at hSourceStep

          | some value =>

              simp [
                DTR.MultiStorePayloadState.step?,
                hBody,
                hEvaluate
              ] at hSourceStep

              subst sourceAfter

              obtain
                ⟨_sourceStep,
                 hTargetStep,
                 hAfterBase⟩ :=
                  multiStorePayload_assign_forward
                    hBase
                    hBody
                    hEvaluate

              let targetAfter :=
                targetBefore.assignmentResult
                  targetName
                  value
                  (Translation.compileMultiStorePayloadBody
                    sourceRemaining)

              have hAfterSelection :
                  MultiStorePayloadSelectionCompatible
                    messageServers
                    (sourceBefore.assignmentResult
                      targetName
                      value
                      sourceRemaining).pendingMessages
                    targetAfter.pendingActions := by

                simpa [
                  targetAfter,
                  DTR.MultiStorePayloadState.assignmentResult,
                  LF.MultiStorePayloadState.assignmentResult
                ] using hRuntime.states.pendingEvents

              have hAfterNotPast :
                  targetAfter.PendingNotPast := by

                have hBeforeNotPast :
                    LF.ActionQueue.PendingNotPast
                      targetBefore.currentTag
                      targetBefore.pendingActions := by

                  exact
                    hRuntime.pendingNotPast

                change
                  LF.ActionQueue.PendingNotPast
                    targetAfter.currentTag
                    targetAfter.pendingActions

                simpa [
                  targetAfter,
                  LF.MultiStorePayloadState.assignmentResult
                ] using hBeforeNotPast

              exact
                ⟨targetAfter,
                 hTargetStep,
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

      | selfSend
          messageName
          payloadExpressions
          delay =>

          cases hEvaluate :
              DTR.MultiStorePayloadExpr.evaluateAll
                sourceBefore.stateStore
                sourceBefore.parameters
                payloadExpressions with

          | none =>

              simp [
                DTR.MultiStorePayloadState.step?,
                hBody,
                hEvaluate
              ] at hSourceStep

          | some payload =>

              simp [
                DTR.MultiStorePayloadState.step?,
                hBody,
                hEvaluate
              ] at hSourceStep

              subst sourceAfter

              obtain
                ⟨_sourceStep,
                 hTargetStep,
                 hAfterBase⟩ :=
                  multiStorePayload_selfSend_forward
                    hBase
                    hBody
                    hEvaluate

              have hCompatibleSelfSend :
                  MultiStorePayloadSelectionCompatible
                      messageServers
                      (sourceBefore.selfSendResult
                        messageName
                        payload
                        delay
                        sourceRemaining).pendingMessages
                      (targetBefore.scheduleResult
                        (Translation.actionNameFor
                          messageName)
                        payload
                        delay
                        (Translation.compileMultiStorePayloadBody
                          sourceRemaining)).pendingActions ∧
                    (targetBefore.scheduleResult
                        (Translation.actionNameFor
                          messageName)
                        payload
                        delay
                        (Translation.compileMultiStorePayloadBody
                          sourceRemaining)).PendingNotPast := by

                have hCompatibleReduced :=
                  hCompatible

                simp [
                  MultiStorePayloadStatementRuntimeCompatible,
                  hBody
                ] at hCompatibleReduced

                exact
                  hCompatibleReduced
                    hEvaluate

              exact
                ⟨targetBefore.scheduleResult
                    (Translation.actionNameFor
                      messageName)
                    payload
                    delay
                    (Translation.compileMultiStorePayloadBody
                      sourceRemaining),
                 hTargetStep,
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
Detailed forward weak matching for one payload statement step.
-/
theorem multiStorePayloadDetailedRuntime_statement_forward_weak
    {messageServers :
      List DTR.MultiStorePayloadMessageServer}
    {sourceBefore sourceAfter :
      DTR.MultiStorePayloadState}
    {targetBefore :
      LF.MultiStorePayloadState}
    (hSourceStep :
      DTR.MultiStorePayloadStep
        sourceBefore
        sourceAfter)
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
    MultiStorePayloadDetailedForwardMatch
      messageServers
      .tau
      (.stable sourceAfter)
      (.stable targetBefore) := by

  have hRuntime :
      MultiStorePayloadRuntimeStateCorresponds
        messageServers
        sourceBefore
        targetBefore :=
    multiStorePayloadDetailedRuntime_stable_iff.mp
      hStates

  obtain
    ⟨targetAfter,
     hTargetStep,
     hAfter⟩ :=
      multiStorePayload_statement_forward_runtime
        hSourceStep
        hRuntime
        hCompatible

  exact
    ⟨.tau,
     .stable targetAfter,
     LF.detailedMultiStorePayloadStatement_is_weak
       hTargetStep,
     MultiStorePayloadDetailedLabelCorresponds.tau,
     multiStorePayloadDetailedRuntime_stable_iff.mpr
       hAfter⟩

end Correctness
end Relico
