import Relico.Correctness.Inversion
import Relico.Correctness.MultiStoreForward
import Relico.DTR.MultiStoreWellFormed

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Backward statement simulation for finite stores and multiple message
servers.
-/
theorem multiStore_step_backward
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState targetStateAfter : LF.StoreState}
    {targetLabel : LF.Label}
    (hTargetStep :
      LF.MultiStoreStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        targetState
        targetLabel
        targetStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState)
    (hSourceBodyWellFormed :
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceState.activeBody) :
    ∃ sourceLabel sourceStateAfter,
      DTR.MultiStoreStep
          declaredVariables
          (DTR.messageServerNames
            messageServers)
          sourceState
          sourceLabel
          sourceStateAfter ∧
      LabelCorresponds
        sourceLabel
        targetLabel ∧
      StoreStateCorresponds
        sourceStateAfter
        targetStateAfter := by

  cases hTargetStep with

  | assign
      currentTag
      targetStore
      pendingActions
      targetVar
      targetExpression
      evaluatedValue
      targetRemaining
      hTargetVar
      hTargetEvaluate =>

      cases sourceState with

      | mk
          sourceTime
          sourceStore
          pendingMessages
          sourceBody =>

          have hCurrentTime :
              currentTag.time =
                sourceTime := by
            simpa using
              hStates.currentTime

          have hPendingEvents :
              QueueCorresponds
                pendingMessages
                pendingActions := by
            simpa using
              hStates.pendingEvents

          have hCompiledBody :
              Translation.compileBody
                  sourceBody =
                LF.Stmt.assign
                    targetVar
                    targetExpression ::
                  targetRemaining := by
            simpa using
              hStates.activeBody.symm

          have hSourceBodyWellFormed' :
              DTR.Body.MultiStoreWellFormed
                declaredVariables
                (DTR.messageServerNames
                  messageServers)
                sourceBody := by
            simpa using
              hSourceBodyWellFormed

          rcases
              compileBody_assign_head
                hCompiledBody
            with
              ⟨sourceVar,
               sourceExpression,
               sourceRemaining,
               hSourceBody,
               hTargetVarGenerated,
               hTargetExpression,
               hTargetRemaining⟩

          subst sourceBody
          subst targetVar
          subst targetExpression
          subst targetRemaining

          have hStore :
              targetStore =
                sourceStore := by
            simpa using
              hStates.stateStore

          subst targetStore

          have hBodyParts :=
            (DTR.Body.multiStoreWellFormed_cons
              declaredVariables
              (DTR.messageServerNames
                messageServers)
              (DTR.Stmt.assign
                sourceVar
                sourceExpression)
              sourceRemaining).mp
              hSourceBodyWellFormed'

          have hSourceTarget :
              sourceVar ∈
                declaredVariables :=
            hBodyParts.1.1

          have hSourceEvaluate :
              DTR.Expr.evaluateStore
                  sourceStore
                  sourceExpression =
                some evaluatedValue := by

            rw [
              ← compileExpr_preserves_store_evaluation
            ]

            exact hTargetEvaluate

          let sourceStateAfter :
              DTR.StoreState := {
            currentTime :=
              sourceTime

            stateStore :=
              StateStore.update
                sourceStore
                sourceVar
                evaluatedValue

            pendingMessages :=
              pendingMessages

            activeBody :=
              sourceRemaining
          }

          refine
            ⟨DTR.Label.internal,
             sourceStateAfter,
             ?_,
             LabelCorresponds.internal,
             ?_⟩

          · exact
              DTR.MultiStoreStep.assign
                sourceTime
                sourceStore
                pendingMessages
                sourceVar
                sourceExpression
                evaluatedValue
                sourceRemaining
                hSourceTarget
                hSourceEvaluate

          · exact {
              currentTime :=
                hCurrentTime

              stateStore :=
                rfl

              pendingEvents :=
                hPendingEvents

              activeBody :=
                rfl
            }

  | schedule
      currentTag
      targetStore
      pendingActions
      targetAction
      targetDelay
      targetRemaining
      _hTargetAction =>

      cases sourceState with

      | mk
          sourceTime
          sourceStore
          pendingMessages
          sourceBody =>

          have hCurrentTime :
              currentTag.time =
                sourceTime := by
            simpa using
              hStates.currentTime

          have hPendingEvents :
              QueueCorresponds
                pendingMessages
                pendingActions := by
            simpa using
              hStates.pendingEvents

          have hCompiledBody :
              Translation.compileBody
                  sourceBody =
                LF.Stmt.schedule
                    targetAction
                    targetDelay ::
                  targetRemaining := by
            simpa using
              hStates.activeBody.symm

          have hSourceBodyWellFormed' :
              DTR.Body.MultiStoreWellFormed
                declaredVariables
                (DTR.messageServerNames
                  messageServers)
                sourceBody := by
            simpa using
              hSourceBodyWellFormed

          rcases
              compileBody_schedule_head
                hCompiledBody
            with
              ⟨sourceMessage,
               sourceDelay,
               sourceRemaining,
               hSourceBody,
               hTargetActionGenerated,
               hTargetDelay,
               hTargetRemaining⟩

          subst sourceBody
          subst targetAction
          subst targetDelay
          subst targetRemaining

          have hStore :
              targetStore =
                sourceStore := by
            simpa using
              hStates.stateStore

          subst targetStore

          have hBodyParts :=
            (DTR.Body.multiStoreWellFormed_cons
              declaredVariables
              (DTR.messageServerNames
                messageServers)
              (DTR.Stmt.selfSend
                sourceMessage
                sourceDelay)
              sourceRemaining).mp
              hSourceBodyWellFormed'

          have hSourceTarget :
              sourceMessage ∈
                DTR.messageServerNames
                  messageServers :=
            hBodyParts.1

          let sourceArrivalTime :
              LogicalTime :=
            LogicalTime.after
              sourceTime
              sourceDelay

          let sourceStateAfter :
              DTR.StoreState := {
            currentTime :=
              sourceTime

            stateStore :=
              sourceStore

            pendingMessages :=
              pendingMessages ++ [
                {
                  name :=
                    sourceMessage

                  arrivalTime :=
                    sourceArrivalTime
                }
              ]

            activeBody :=
              sourceRemaining
          }

          refine
            ⟨DTR.Label.send
                sourceMessage
                sourceArrivalTime,
             sourceStateAfter,
             ?_,
             ?_,
             ?_⟩

          · exact
              DTR.MultiStoreStep.selfSend
                sourceTime
                sourceStore
                pendingMessages
                sourceMessage
                sourceDelay
                sourceRemaining
                hSourceTarget

          · apply
              LabelCorresponds.send
                sourceMessage
                sourceArrivalTime
                (LF.Tag.schedule
                  currentTag
                  sourceDelay)

            change
              (LF.Tag.schedule
                currentTag
                sourceDelay).time =
              LogicalTime.after
                sourceTime
                sourceDelay

            calc
              (LF.Tag.schedule
                  currentTag
                  sourceDelay).time
                  =
                LogicalTime.after
                  currentTag.time
                  sourceDelay := by

                    exact
                      LF.Tag.schedule_time
                        currentTag
                        sourceDelay

              _ =
                LogicalTime.after
                  sourceTime
                  sourceDelay := by

                    rw [hCurrentTime]

          · refine {
              currentTime :=
                hCurrentTime

              stateStore :=
                rfl

              pendingEvents :=
                ?_

              activeBody :=
                rfl
            }

            apply
              QueueCorresponds.append_one
                hPendingEvents

            exact
              pendingCorresponds_scheduled
                sourceTime
                currentTag
                sourceMessage
                sourceDelay
                hCurrentTime

end Correctness
end Relico
