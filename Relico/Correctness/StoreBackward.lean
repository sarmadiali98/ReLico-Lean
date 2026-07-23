import Relico.Correctness.Inversion
import Relico.Correctness.StoreForward
import Relico.DTR.StoreWellFormed

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Backward statement simulation over finite stores.

Every generated-LF store step from a corresponding state can be
matched by one DTR store step. Transition labels and resulting runtime
states correspond.

Source-body well-formedness is required to recover the declared
message-server target of a compiled self-send.
-/
theorem store_step_backward
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {sourceState : DTR.StoreState}
    {targetState targetStateAfter : LF.StoreState}
    {targetLabel : LF.Label}
    (hTargetStep :
      LF.StoreStep
        declaredVariables
        (Translation.actionNameFor
          messageServer)
        targetState
        targetLabel
        targetStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState)
    (hSourceBodyWellFormed :
      DTR.Body.StoreWellFormed
        declaredVariables
        messageServer
        sourceState.activeBody) :
    ∃ sourceLabel sourceStateAfter,
      DTR.StoreStep
          declaredVariables
          messageServer
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

          have hStore :
              targetStore =
                sourceStore := by
            simpa using
              hStates.stateStore

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
              DTR.Body.StoreWellFormed
                declaredVariables
                messageServer
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
          subst targetStore

          have hBodyParts :=
            (DTR.Body.storeWellFormed_cons
              declaredVariables
              messageServer
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

          · apply DTR.StoreStep.assign

            · exact hSourceTarget

            · exact hSourceEvaluate

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
      hTargetAction =>

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

          have hStore :
              targetStore =
                sourceStore := by
            simpa using
              hStates.stateStore

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
              DTR.Body.StoreWellFormed
                declaredVariables
                messageServer
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
          subst targetStore

          have hBodyParts :=
            (DTR.Body.storeWellFormed_cons
              declaredVariables
              messageServer
              (DTR.Stmt.selfSend
                sourceMessage
                sourceDelay)
              sourceRemaining).mp
              hSourceBodyWellFormed'

          have hSourceTarget :
              sourceMessage =
                messageServer :=
            hBodyParts.1

          subst sourceMessage

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
                    messageServer

                  arrivalTime :=
                    sourceArrivalTime
                }
              ]

            activeBody :=
              sourceRemaining
          }

          refine
            ⟨DTR.Label.send
                messageServer
                sourceArrivalTime,
             sourceStateAfter,
             ?_,
             ?_,
             ?_⟩

          · apply DTR.StoreStep.selfSend
            rfl

          · apply
              LabelCorresponds.send
                messageServer
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
                messageServer
                sourceDelay
                hCurrentTime

end Correctness
end Relico
