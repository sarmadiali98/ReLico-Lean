import Relico.Correctness.StoreForward
import Relico.DTR.MultiStoreSemantics
import Relico.LF.MultiStoreSemantics
import Relico.Translation.MultiStoreBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Forward statement simulation for finite stores and multiple message
servers.
-/
theorem multiStore_step_forward
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceState sourceStateAfter : DTR.StoreState}
    {sourceLabel : DTR.Label}
    {targetState : LF.StoreState}
    (hSourceStep :
      DTR.MultiStoreStep
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceState
        sourceLabel
        sourceStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState) :
    ∃ targetLabel targetStateAfter,
      LF.MultiStoreStep
          declaredVariables
          (Translation.compileLogicalActions
            messageServers)
          targetState
          targetLabel
          targetStateAfter ∧
      LabelCorresponds
        sourceLabel
        targetLabel ∧
      StoreStateCorresponds
        sourceStateAfter
        targetStateAfter := by

  cases hSourceStep with

  | assign
      currentTime
      sourceStore
      pendingMessages
      target
      sourceExpression
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      cases targetState with

      | mk
          targetTag
          targetStore
          pendingActions
          targetBody =>

          have hCurrentTime :
              targetTag.time =
                currentTime :=
            hStates.currentTime

          have hPending :
              QueueCorresponds
                pendingMessages
                pendingActions :=
            hStates.pendingEvents

          have hBody :
              targetBody =
                LF.Stmt.assign
                    target
                    (Translation.compileExpr
                      sourceExpression) ::
                  Translation.compileBody
                    remaining := by

            simpa [
              Translation.compileBody,
              Translation.compileStmt
            ] using
              hStates.activeBody

          have hStore :
              targetStore =
                sourceStore :=
            hStates.stateStore

          subst targetStore
          subst targetBody

          have hTargetEvaluate :
              LF.Expr.evaluateStore
                  sourceStore
                  (Translation.compileExpr
                    sourceExpression) =
                some evaluatedValue := by

            rw [
              compileExpr_preserves_store_evaluation
            ]

            exact hEvaluate

          let targetStateAfter :
              LF.StoreState := {
            currentTag :=
              targetTag

            stateStore :=
              StateStore.update
                sourceStore
                target
                evaluatedValue

            pendingActions :=
              pendingActions

            activeBody :=
              Translation.compileBody
                remaining
          }

          refine
            ⟨LF.Label.internal,
             targetStateAfter,
             ?_,
             LabelCorresponds.internal,
             ?_⟩

          · exact
              LF.MultiStoreStep.assign
                targetTag
                sourceStore
                pendingActions
                target
                (Translation.compileExpr
                  sourceExpression)
                evaluatedValue
                (Translation.compileBody
                  remaining)
                hTarget
                hTargetEvaluate

          · exact {
              currentTime :=
                hCurrentTime

              stateStore :=
                rfl

              pendingEvents :=
                hPending

              activeBody :=
                rfl
            }

  | selfSend
      currentTime
      sourceStore
      pendingMessages
      targetMessage
      delay
      remaining
      hTarget =>

      cases targetState with

      | mk
          targetTag
          targetStore
          pendingActions
          targetBody =>

          have hCurrentTime :
              targetTag.time =
                currentTime :=
            hStates.currentTime

          have hPending :
              QueueCorresponds
                pendingMessages
                pendingActions :=
            hStates.pendingEvents

          have hBody :
              targetBody =
                LF.Stmt.schedule
                    (Translation.actionNameFor
                      targetMessage)
                    delay ::
                  Translation.compileBody
                    remaining := by

            simpa [
              Translation.compileBody,
              Translation.compileStmt
            ] using
              hStates.activeBody

          have hStore :
              targetStore =
                sourceStore :=
            hStates.stateStore

          subst targetStore
          subst targetBody

          have hTargetAction :
              Translation.actionNameFor
                  targetMessage ∈
                Translation.compileLogicalActions
                  messageServers := by

            have hMapped :
                Translation.actionNameFor
                    targetMessage ∈
                  (DTR.messageServerNames
                    messageServers).map
                      Translation.actionNameFor :=
              List.mem_map_of_mem
                hTarget

            simpa only [
              Translation.compileLogicalActions_names
            ] using
              hMapped

          let scheduledTag :
              LF.Tag :=
            LF.Tag.schedule
              targetTag
              delay

          let targetStateAfter :
              LF.StoreState := {
            currentTag :=
              targetTag

            stateStore :=
              sourceStore

            pendingActions :=
              pendingActions ++ [
                {
                  name :=
                    Translation.actionNameFor
                      targetMessage

                  tag :=
                    scheduledTag
                }
              ]

            activeBody :=
              Translation.compileBody
                remaining
          }

          refine
            ⟨LF.Label.schedule
                (Translation.actionNameFor
                  targetMessage)
                scheduledTag,
             targetStateAfter,
             ?_,
             ?_,
             ?_⟩

          · exact
              LF.MultiStoreStep.schedule
                targetTag
                sourceStore
                pendingActions
                (Translation.actionNameFor
                  targetMessage)
                delay
                (Translation.compileBody
                  remaining)
                hTargetAction

          · apply
              LabelCorresponds.send
                targetMessage
                (LogicalTime.after
                  currentTime
                  delay)
                scheduledTag

            change
              (LF.Tag.schedule
                targetTag
                delay).time =
              LogicalTime.after
                currentTime
                delay

            calc
              (LF.Tag.schedule
                  targetTag
                  delay).time
                  =
                LogicalTime.after
                  targetTag.time
                  delay := by

                    exact
                      LF.Tag.schedule_time
                        targetTag
                        delay

              _ =
                LogicalTime.after
                  currentTime
                  delay := by

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
                hPending

            exact
              pendingCorresponds_scheduled
                currentTime
                targetTag
                targetMessage
                delay
                hCurrentTime

end Correctness
end Relico
