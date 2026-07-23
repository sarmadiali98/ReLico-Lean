import Relico.Correctness.Correspondence
import Relico.Correctness.ExpressionStore
import Relico.DTR.StoreSemantics
import Relico.LF.StoreSemantics

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between store-backed DTR and LF runtime states.

The relation preserves:

- logical time;
- the complete finite state-variable store;
- pending message/action occurrences;
- the executable body produced by `Translation.compileBody`.
-/
structure StoreStateCorresponds
    (sourceState : DTR.StoreState)
    (targetState : LF.StoreState) :
    Prop where

  currentTime :
    targetState.currentTag.time =
      sourceState.currentTime

  stateStore :
    targetState.stateStore =
      sourceState.stateStore

  pendingEvents :
    QueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions

  activeBody :
    targetState.activeBody =
      Translation.compileBody
        sourceState.activeBody

/--
Forward statement simulation over finite stores.

Every DTR store step starting from corresponding runtime states has one
matching generated-LF store step. Transition labels and resulting
runtime states also correspond.

The LF logical action is generated directly from the DTR message-server
name through the executable translation function.
-/
theorem store_step_forward
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {sourceState sourceStateAfter : DTR.StoreState}
    {sourceLabel : DTR.Label}
    {targetState : LF.StoreState}
    (hSourceStep :
      DTR.StoreStep
        declaredVariables
        messageServer
        sourceState
        sourceLabel
        sourceStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState) :
    ∃ targetLabel targetStateAfter,
      LF.StoreStep
          declaredVariables
          (Translation.actionNameFor
            messageServer)
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

          have hStore :
              targetStore =
                sourceStore :=
            hStates.stateStore

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

          · apply LF.StoreStep.assign

            · exact hTarget

            · exact hTargetEvaluate

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

          have hStore :
              targetStore =
                sourceStore :=
            hStates.stateStore

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

          subst targetStore
          subst targetBody

          have hTargetAction :
              Translation.actionNameFor
                  targetMessage =
                Translation.actionNameFor
                  messageServer := by

            exact
              congrArg
                Translation.actionNameFor
                hTarget

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

          · apply LF.StoreStep.schedule
            exact hTargetAction

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
