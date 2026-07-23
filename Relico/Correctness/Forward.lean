import Relico.Correctness.Correspondence
import Relico.Correctness.Expression

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Forward simulation for the statement-level SOS rules in vertical slice v0.

For every DTR assignment or self-send transition starting from a state
that corresponds to an LF state, the generated LF program can perform
one matching transition. The labels and resulting states also correspond.

This theorem refers directly to the executable translation functions.
-/
theorem step_forward
    {model : DTR.Model}
    {sourceState sourceStateAfter : DTR.State}
    {sourceLabel : DTR.Label}
    {targetState : LF.State}
    (hSourceStep :
      DTR.Step
        model
        sourceState
        sourceLabel
        sourceStateAfter)
    (hStates :
      StateCorresponds
        sourceState
        targetState) :
    ∃ targetLabel targetStateAfter,
      LF.Step
          (Translation.translateCore model)
          targetState
          targetLabel
          targetStateAfter ∧
      LabelCorresponds
          sourceLabel
          targetLabel ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by

  cases hSourceStep with

  | assign
      currentTime
      stateValue
      pendingMessages
      targetVar
      sourceExpression
      remaining
      hTargetVar =>

      cases targetState with
      | mk
          targetTag
          targetStateValue
          targetPendingActions
          targetActiveBody =>

          have hCurrentTime :
              targetTag.time = currentTime :=
            hStates.currentTime

          have hStateValue :
              targetStateValue = stateValue :=
            hStates.stateValue

          have hPendingEvents :
              QueueCorresponds
                pendingMessages
                targetPendingActions :=
            hStates.pendingEvents

          have hActiveBody :
              targetActiveBody =
                LF.Stmt.assign
                    targetVar
                    (Translation.compileExpr
                      sourceExpression) ::
                  Translation.compileBody
                    remaining := by
            simpa [
              Translation.compileBody,
              Translation.compileStmt
            ] using hStates.activeBody

          subst targetStateValue
          subst targetActiveBody

          let targetStateAfter : LF.State := {
            currentTag := targetTag
            stateValue :=
              LF.Expr.evaluate
                stateValue
                (Translation.compileExpr
                  sourceExpression)
            pendingActions := targetPendingActions
            activeBody :=
              Translation.compileBody remaining
          }

          refine
            ⟨LF.Label.internal,
             targetStateAfter,
             ?_,
             LabelCorresponds.internal,
             ?_⟩

          · apply LF.Step.assign
              (program :=
                Translation.translateCore model)
              (currentTag := targetTag)
              (stateValue := stateValue)
              (pendingActions :=
                targetPendingActions)
              (target := targetVar)
              (expression :=
                Translation.compileExpr
                  sourceExpression)
              (remaining :=
                Translation.compileBody remaining)

            simpa [
              Translation.translateCore,
              Translation.compileReactor
            ] using hTargetVar

          · refine {
              currentTime := hCurrentTime
              stateValue := ?_
              pendingEvents := hPendingEvents
              activeBody := rfl
            }

            exact
              compileExpr_preserves_evaluation
                sourceExpression
                stateValue

  | selfSend
      currentTime
      stateValue
      pendingMessages
      targetMessage
      delay
      remaining
      hTargetMessage =>

      cases targetState with
      | mk
          targetTag
          targetStateValue
          targetPendingActions
          targetActiveBody =>

          have hCurrentTime :
              targetTag.time = currentTime :=
            hStates.currentTime

          have hStateValue :
              targetStateValue = stateValue :=
            hStates.stateValue

          have hPendingEvents :
              QueueCorresponds
                pendingMessages
                targetPendingActions :=
            hStates.pendingEvents

          have hActiveBody :
              targetActiveBody =
                LF.Stmt.schedule
                    (Translation.actionNameFor
                      targetMessage)
                    delay ::
                  Translation.compileBody
                    remaining := by
            simpa [
              Translation.compileBody,
              Translation.compileStmt
            ] using hStates.activeBody

          subst targetStateValue
          subst targetActiveBody

          let scheduledTag : LF.Tag :=
            LF.Tag.schedule targetTag delay

          let targetStateAfter : LF.State := {
            currentTag := targetTag
            stateValue := stateValue
            pendingActions :=
              targetPendingActions ++
                [{
                  name :=
                    Translation.actionNameFor
                      targetMessage
                  tag := scheduledTag
                }]
            activeBody :=
              Translation.compileBody remaining
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

          · apply LF.Step.schedule
              (program :=
                Translation.translateCore model)
              (currentTag := targetTag)
              (stateValue := stateValue)
              (pendingActions :=
                targetPendingActions)
              (targetAction :=
                Translation.actionNameFor
                  targetMessage)
              (delay := delay)
              (remaining :=
                Translation.compileBody remaining)

            have hGeneratedAction :=
              congrArg
                Translation.actionNameFor
                hTargetMessage

            simpa [
              Translation.translateCore,
              Translation.compileReactor
            ] using hGeneratedAction

          · apply LabelCorresponds.send
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
              currentTime := hCurrentTime
              stateValue := rfl
              pendingEvents := ?_
              activeBody := rfl
            }

            apply QueueCorresponds.append_one
              hPendingEvents

            exact
              pendingCorresponds_scheduled
                currentTime
                targetTag
                targetMessage
                delay
                hCurrentTime

end Correctness
end Relico
