import Relico.Correctness.Expression
import Relico.Correctness.PayloadCorrespondence
import Relico.DTR.PayloadSemantics
import Relico.DTR.PayloadWellFormed
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


/--
Every generated payload scheduling step corresponding to a well-formed
source payload body can be reconstructed as a source payload-send step.

The proof inverts the executable payload-body translation, uses source
well-formedness to recover the declared message target, and transfers
expression evaluation from generated LF back to DTR.
-/
theorem payloadStep_backward
    {declaredMessageServer : MsgName}
    {sourceBefore : DTR.PayloadState}
    {targetBefore targetAfter : LF.PayloadState}
    {targetLabel : LF.PayloadLabel}
    (hSourceBodyWellFormed :
      DTR.PayloadBody.WellFormed
        declaredMessageServer
        sourceBefore.activeBody)
    (hStates :
      PayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hTargetStep :
      LF.PayloadStep
        (Translation.actionNameFor
          declaredMessageServer)
        targetBefore
        targetLabel
        targetAfter) :
    ∃ sourceLabel sourceAfter,
      DTR.PayloadStep
          declaredMessageServer
          sourceBefore
          sourceLabel
          sourceAfter ∧
        PayloadLabelCorresponds
          sourceLabel
          targetLabel ∧
        PayloadStateCorresponds
          sourceAfter
          targetAfter := by

  cases hTargetStep with

  | scheduleInt
      currentTag
      targetStateValue
      pendingActions
      targetAction
      targetExpression
      targetDelay
      evaluatedValue
      targetRemaining
      hTargetAction
      hTargetEvaluate =>

      cases sourceBefore with

      | mk
          sourceTime
          sourceStateValue
          pendingMessages
          sourceBody =>

          have hCurrentTime :
              currentTag.time =
                sourceTime :=
            hStates.currentTime

          have hStateValue :
              targetStateValue =
                sourceStateValue :=
            hStates.stateValue

          have hPending :
              PayloadQueueCorresponds
                pendingMessages
                pendingActions :=
            hStates.pendingEvents

          have hCompiledBody :
              LF.PayloadStmt.scheduleInt
                    targetAction
                    targetExpression
                    targetDelay ::
                  targetRemaining =
                Translation.compilePayloadBody
                  sourceBody :=
            hStates.activeBody

          cases sourceBody with

          | nil =>

              simp [
                Translation.compilePayloadBody
              ] at hCompiledBody

          | cons sourceStatement sourceRemaining =>

              cases sourceStatement with

              | selfSendInt
                  sourceMessage
                  sourceExpression
                  sourceDelay =>

                  have hCompiledBody' :
                      LF.PayloadStmt.scheduleInt
                            targetAction
                            targetExpression
                            targetDelay ::
                          targetRemaining =
                        LF.PayloadStmt.scheduleInt
                              (Translation.actionNameFor
                                sourceMessage)
                              (Translation.compileExpr
                                sourceExpression)
                              sourceDelay ::
                            Translation.compilePayloadBody
                              sourceRemaining := by

                    simpa [
                      Translation.compilePayloadBody,
                      Translation.compilePayloadStmt
                    ] using
                      hCompiledBody

                  injection hCompiledBody' with
                    hCompiledHead
                    hCompiledRemaining

                  injection hCompiledHead with
                    hAction
                    hExpression
                    hDelay

                  have hWellFormedParts :=
                    (DTR.PayloadBody.wellFormed_cons
                      declaredMessageServer
                      (DTR.PayloadStmt.selfSendInt
                        sourceMessage
                        sourceExpression
                        sourceDelay)
                      sourceRemaining).mp
                      hSourceBodyWellFormed

                  have hSourceTarget :
                      sourceMessage =
                        declaredMessageServer := by

                    simpa [
                      DTR.PayloadStmt.WellFormed
                    ] using
                      hWellFormedParts.1

                  subst targetAction
                  subst targetExpression
                  subst targetDelay
                  subst targetRemaining
                  subst targetStateValue

                  have hSourceEvaluate :
                      DTR.Expr.evaluate
                          sourceStateValue
                          sourceExpression =
                        evaluatedValue := by

                    calc
                      DTR.Expr.evaluate
                          sourceStateValue
                          sourceExpression =
                        LF.Expr.evaluate
                          sourceStateValue
                          (Translation.compileExpr
                            sourceExpression) := by

                            exact
                              (compileExpr_preserves_evaluation
                                sourceExpression
                                sourceStateValue).symm

                      _ =
                        evaluatedValue :=
                          hTargetEvaluate

                  let sourceLabel :
                      DTR.PayloadLabel :=
                    DTR.PayloadLabel.sendInt
                      sourceMessage
                      (LogicalTime.after
                        sourceTime
                        sourceDelay)
                      evaluatedValue

                  let sourceAfter :
                      DTR.PayloadState := {
                    currentTime :=
                      sourceTime

                    stateValue :=
                      sourceStateValue

                    pendingMessages :=
                      pendingMessages ++ [
                        DTR.PendingMessage.scheduleWithPayload
                          sourceTime
                          sourceMessage
                          [
                            evaluatedValue
                          ]
                          sourceDelay
                      ]

                    activeBody :=
                      sourceRemaining
                  }

                  refine
                    ⟨sourceLabel,
                     sourceAfter,
                     ?_,
                     ?_,
                     ?_⟩

                  · exact
                      DTR.PayloadStep.selfSendInt
                        (declaredMessageServer :=
                          declaredMessageServer)
                        (currentTime :=
                          sourceTime)
                        (stateValue :=
                          sourceStateValue)
                        (pendingMessages :=
                          pendingMessages)
                        (targetMessage :=
                          sourceMessage)
                        (payloadExpression :=
                          sourceExpression)
                        (delay :=
                          sourceDelay)
                        (evaluatedValue :=
                          evaluatedValue)
                        (remaining :=
                          sourceRemaining)
                        hSourceTarget
                        hSourceEvaluate

                  · unfold
                      PayloadLabelCorresponds

                    refine
                      ⟨?_,
                       ?_,
                       rfl⟩

                    · exact
                        congrArg
                          Translation.actionNameFor
                          hSourceTarget.symm

                    · calc
                      (LF.Tag.schedule
                        currentTag
                        sourceDelay).time =
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

                    simpa [
                      sourceAfter,
                      hSourceTarget
                    ] using
                      payloadQueueCorresponds_append_scheduleWithPayload
                        hPending
                        sourceTime
                        currentTag
                        sourceMessage
                        [
                          evaluatedValue
                        ]
                        sourceDelay
                        hCurrentTime

end Correctness
end Relico
