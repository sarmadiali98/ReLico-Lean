import Relico.Correctness.Expression
import Relico.Correctness.PayloadCorrespondence
import Relico.DTR.PayloadSemantics
import Relico.LF.PayloadSemantics
import Relico.Translation.PayloadBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between source payload-send labels and generated
payload-scheduling labels.
-/
def PayloadLabelCorresponds :
    DTR.PayloadLabel →
    LF.PayloadLabel →
    Prop

  | .sendInt
      sourceMessage
      sourceArrivalTime
      sourceValue,
    .scheduleInt
      targetAction
      targetTag
      targetValue =>

      targetAction =
          Translation.actionNameFor
            sourceMessage ∧
        targetTag.time =
          sourceArrivalTime ∧
        targetValue =
          sourceValue

/--
Correspondence between additive source and target payload runtime
states.
-/
structure PayloadStateCorresponds
    (sourceState : DTR.PayloadState)
    (targetState : LF.PayloadState) :
    Prop where

  currentTime :
    targetState.currentTag.time =
      sourceState.currentTime

  stateValue :
    targetState.stateValue =
      sourceState.stateValue

  pendingEvents :
    PayloadQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions

  activeBody :
    targetState.activeBody =
      Translation.compilePayloadBody
        sourceState.activeBody

/--
One additive source payload-scheduling step has a corresponding
generated-LF step.

The proof uses the executable expression and statement translators.
The evaluated source integer is preserved and enqueued as the singleton
payload `[evaluatedValue]` on both sides.
-/
theorem payloadStep_forward
    {declaredMessageServer : MsgName}
    {sourceBefore sourceAfter : DTR.PayloadState}
    {sourceLabel : DTR.PayloadLabel}
    {targetBefore : LF.PayloadState}
    (hStates :
      PayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSourceStep :
      DTR.PayloadStep
        declaredMessageServer
        sourceBefore
        sourceLabel
        sourceAfter) :
    ∃ targetLabel targetAfter,
      LF.PayloadStep
          (Translation.actionNameFor
            declaredMessageServer)
          targetBefore
          targetLabel
          targetAfter ∧
        PayloadLabelCorresponds
          sourceLabel
          targetLabel ∧
        PayloadStateCorresponds
          sourceAfter
          targetAfter := by

  cases hSourceStep with

  | selfSendInt
      currentTime
      stateValue
      pendingMessages
      targetMessage
      payloadExpression
      delay
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      cases targetBefore with

      | mk
          currentTag
          targetStateValue
          pendingActions
          targetBody =>

          have hCurrentTime :
              currentTag.time =
                currentTime :=
            hStates.currentTime

          have hStateValue :
              targetStateValue =
                stateValue :=
            hStates.stateValue

          have hPending :
              PayloadQueueCorresponds
                pendingMessages
                pendingActions :=
            hStates.pendingEvents

          have hTargetBody :
              targetBody =
                LF.PayloadStmt.scheduleInt
                    (Translation.actionNameFor
                      targetMessage)
                    (Translation.compileExpr
                      payloadExpression)
                    delay ::
                  Translation.compilePayloadBody
                    remaining := by

            simpa [
              Translation.compilePayloadBody,
              Translation.compilePayloadStmt
            ] using
              hStates.activeBody

          subst targetStateValue
          subst targetBody

          have hTargetAction :
              Translation.actionNameFor
                  targetMessage =
                Translation.actionNameFor
                  declaredMessageServer := by

            exact
              congrArg
                Translation.actionNameFor
                hTarget

          have hTargetEvaluate :
              LF.Expr.evaluate
                  stateValue
                  (Translation.compileExpr
                    payloadExpression) =
                evaluatedValue := by

            calc
              LF.Expr.evaluate
                  stateValue
                  (Translation.compileExpr
                    payloadExpression) =
                DTR.Expr.evaluate
                  stateValue
                  payloadExpression := by

                    exact
                      compileExpr_preserves_evaluation
                        payloadExpression
                        stateValue

              _ =
                evaluatedValue :=
                  hEvaluate

          let targetLabel :
              LF.PayloadLabel :=
            LF.PayloadLabel.scheduleInt
              (Translation.actionNameFor
                targetMessage)
              (LF.Tag.schedule
                currentTag
                delay)
              evaluatedValue

          let targetAfter :
              LF.PayloadState := {
            currentTag :=
              currentTag

            stateValue :=
              stateValue

            pendingActions :=
              pendingActions ++ [
                LF.PendingAction.scheduleWithPayload
                  currentTag
                  (Translation.actionNameFor
                    targetMessage)
                  [
                    evaluatedValue
                  ]
                  delay
              ]

            activeBody :=
              Translation.compilePayloadBody
                remaining
          }

          refine
            ⟨targetLabel,
             targetAfter,
             ?_,
             ?_,
             ?_⟩

          · exact
              LF.PayloadStep.scheduleInt
                (declaredAction :=
                  Translation.actionNameFor
                    declaredMessageServer)
                (currentTag :=
                  currentTag)
                (stateValue :=
                  stateValue)
                (pendingActions :=
                  pendingActions)
                (targetAction :=
                  Translation.actionNameFor
                    targetMessage)
                (payloadExpression :=
                  Translation.compileExpr
                    payloadExpression)
                (delay :=
                  delay)
                (evaluatedValue :=
                  evaluatedValue)
                (remaining :=
                  Translation.compilePayloadBody
                    remaining)
                hTargetAction
                hTargetEvaluate

          · unfold
              PayloadLabelCorresponds

            refine
              ⟨rfl,
               ?_,
               rfl⟩

            calc
              (LF.Tag.schedule
                currentTag
                delay).time =
                LogicalTime.after
                  currentTag.time
                  delay := by

                    exact
                      LF.Tag.schedule_time
                        currentTag
                        delay

              _ =
                LogicalTime.after
                  currentTime
                  delay := by

                    rw [
                      hCurrentTime
                    ]

          · refine {
              currentTime :=
                hCurrentTime

              stateValue :=
                rfl

              pendingEvents :=
                ?_

              activeBody :=
                rfl
            }

            exact
              payloadQueueCorresponds_append_scheduleWithPayload
                hPending
                currentTime
                currentTag
                targetMessage
                [
                  evaluatedValue
                ]
                delay
                hCurrentTime

end Correctness
end Relico
