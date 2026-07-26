import Relico.Correctness.BoundPayloadState
import Relico.DTR.BoundPayloadSemantics
import Relico.LF.BoundPayloadSemantics
import Relico.Translation.BoundPayloadBasic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Correspondence between parameter-aware source-send labels and generated
LF scheduling labels.
-/
def BoundPayloadLabelCorresponds :
    DTR.BoundPayloadLabel →
    LF.BoundPayloadLabel →
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
Every parameter-aware source scheduling step has a corresponding
generated-LF step.

The theorem preserves expression evaluation, ordered payload contents,
activation-local parameters, persistent state, and the remaining active
body.
-/
theorem boundPayloadStep_forward
    {declaredMessageServer : MsgName}
    {sourceBefore sourceAfter : DTR.BoundPayloadState}
    {sourceLabel : DTR.BoundPayloadLabel}
    {targetBefore : LF.BoundPayloadState}
    (hStates :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSourceStep :
      DTR.BoundPayloadStep
        declaredMessageServer
        sourceBefore
        sourceLabel
        sourceAfter) :
    ∃ targetLabel targetAfter,
      LF.BoundPayloadStep
          (Translation.actionNameFor
            declaredMessageServer)
          targetBefore
          targetLabel
          targetAfter ∧
        BoundPayloadLabelCorresponds
          sourceLabel
          targetLabel ∧
        BoundPayloadStateCorresponds
          sourceAfter
          targetAfter := by

  cases hSourceStep with

  | selfSendInt
      currentTime
      stateValue
      sourceParameters
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
          targetParameters
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

          have hParameters :
              targetParameters =
                sourceParameters :=
            hStates.parameters

          have hPending :
              PayloadQueueCorresponds
                pendingMessages
                pendingActions :=
            hStates.pendingEvents

          have hTargetBody :
              targetBody =
                LF.BoundPayloadStmt.scheduleInt
                    (Translation.actionNameFor
                      targetMessage)
                    (Translation.compilePayloadExpr
                      payloadExpression)
                    delay ::
                  Translation.compileBoundPayloadBody
                    remaining := by

            simpa using
              hStates.activeBody

          subst targetStateValue
          subst targetParameters
          subst targetBody

          have hTargetAction :
              Translation.actionNameFor
                  targetMessage =
                Translation.actionNameFor
                  declaredMessageServer :=

            congrArg
              Translation.actionNameFor
              hTarget

          have hTargetEvaluate :
              LF.PayloadExpr.evaluate
                  stateValue
                  sourceParameters
                  (Translation.compilePayloadExpr
                    payloadExpression) =
                some evaluatedValue := by

            calc
              LF.PayloadExpr.evaluate
                  stateValue
                  sourceParameters
                  (Translation.compilePayloadExpr
                    payloadExpression) =
                DTR.PayloadExpr.evaluate
                  stateValue
                  sourceParameters
                  payloadExpression :=

                    Translation.compilePayloadExpr_preserves_evaluation
                      payloadExpression
                      stateValue
                      sourceParameters

              _ =
                some evaluatedValue :=
                  hEvaluate

          let targetLabel :
              LF.BoundPayloadLabel :=
            LF.BoundPayloadLabel.scheduleInt
              (Translation.actionNameFor
                targetMessage)
              (LF.Tag.schedule
                currentTag
                delay)
              evaluatedValue

          let targetAfter :
              LF.BoundPayloadState := {

            currentTag :=
              currentTag

            stateValue :=
              stateValue

            parameters :=
              sourceParameters

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
              Translation.compileBoundPayloadBody
                remaining
          }

          refine
            ⟨targetLabel,
             targetAfter,
             ?_,
             ?_,
             ?_⟩

          · exact
              LF.BoundPayloadStep.scheduleInt
                (declaredAction :=
                  Translation.actionNameFor
                    declaredMessageServer)
                (currentTag :=
                  currentTag)
                (stateValue :=
                  stateValue)
                (parameters :=
                  sourceParameters)
                (pendingActions :=
                  pendingActions)
                (targetAction :=
                  Translation.actionNameFor
                    targetMessage)
                (payloadExpression :=
                  Translation.compilePayloadExpr
                    payloadExpression)
                (delay :=
                  delay)
                (evaluatedValue :=
                  evaluatedValue)
                (remaining :=
                  Translation.compileBoundPayloadBody
                    remaining)
                hTargetAction
                hTargetEvaluate

          · unfold
              BoundPayloadLabelCorresponds

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
                  delay :=

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

          · exact {
              currentTime :=
                hCurrentTime

              stateValue :=
                rfl

              parameters :=
                rfl

              pendingEvents :=
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

              activeBody :=
                rfl
            }

/--
Every generated parameter-aware scheduling step beginning in
corresponding states can be reconstructed as a source scheduling step.

Executable body translation is inverted to recover the source statement.
Injectivity of generated action names reconstructs the source self-send
target, while payload-expression correctness reconstructs source
evaluation.
-/
theorem boundPayloadStep_backward
    {declaredMessageServer : MsgName}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter : LF.BoundPayloadState}
    {targetLabel : LF.BoundPayloadLabel}
    (hStates :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hTargetStep :
      LF.BoundPayloadStep
        (Translation.actionNameFor
          declaredMessageServer)
        targetBefore
        targetLabel
        targetAfter) :
    ∃ sourceLabel sourceAfter,
      DTR.BoundPayloadStep
          declaredMessageServer
          sourceBefore
          sourceLabel
          sourceAfter ∧
        BoundPayloadLabelCorresponds
          sourceLabel
          targetLabel ∧
        BoundPayloadStateCorresponds
          sourceAfter
          targetAfter := by

  cases hTargetStep with

  | scheduleInt
      currentTag
      targetStateValue
      targetParameters
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
          sourceParameters
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

          have hParameters :
              targetParameters =
                sourceParameters :=
            hStates.parameters

          have hPending :
              PayloadQueueCorresponds
                pendingMessages
                pendingActions :=
            hStates.pendingEvents

          have hCompiledBody :
              LF.BoundPayloadStmt.scheduleInt
                    targetAction
                    targetExpression
                    targetDelay ::
                  targetRemaining =
                Translation.compileBoundPayloadBody
                  sourceBody :=
            hStates.activeBody

          cases sourceBody with

          | nil =>

              simp [
                Translation.compileBoundPayloadBody
              ] at hCompiledBody

          | cons sourceStatement sourceRemaining =>

              cases sourceStatement with

              | selfSendInt
                  sourceMessage
                  sourceExpression
                  sourceDelay =>

                  have hCompiledBody' :
                      LF.BoundPayloadStmt.scheduleInt
                            targetAction
                            targetExpression
                            targetDelay ::
                          targetRemaining =
                        LF.BoundPayloadStmt.scheduleInt
                              (Translation.actionNameFor
                                sourceMessage)
                              (Translation.compilePayloadExpr
                                sourceExpression)
                              sourceDelay ::
                            Translation.compileBoundPayloadBody
                              sourceRemaining := by

                    simpa using
                      hCompiledBody

                  injection hCompiledBody' with
                    hCompiledHead
                    hCompiledRemaining

                  injection hCompiledHead with
                    hAction
                    hExpression
                    hDelay

                  have hSourceAction :
                      Translation.actionNameFor
                          sourceMessage =
                        Translation.actionNameFor
                          declaredMessageServer := by

                    calc
                      Translation.actionNameFor
                          sourceMessage =
                        targetAction :=
                          hAction.symm

                      _ =
                        Translation.actionNameFor
                          declaredMessageServer :=
                            hTargetAction

                  have hSourceTarget :
                      sourceMessage =
                        declaredMessageServer :=

                    Translation.actionNameFor_injective
                      hSourceAction

                  subst targetExpression
                  subst targetDelay
                  subst targetRemaining
                  subst targetStateValue
                  subst targetParameters
                  subst sourceMessage
                  subst targetAction

                  have hSourceEvaluate :
                      DTR.PayloadExpr.evaluate
                          sourceStateValue
                          sourceParameters
                          sourceExpression =
                        some evaluatedValue := by

                    calc
                      DTR.PayloadExpr.evaluate
                          sourceStateValue
                          sourceParameters
                          sourceExpression =
                        LF.PayloadExpr.evaluate
                          sourceStateValue
                          sourceParameters
                          (Translation.compilePayloadExpr
                            sourceExpression) :=

                            (Translation.compilePayloadExpr_preserves_evaluation
                              sourceExpression
                              sourceStateValue
                              sourceParameters).symm

                      _ =
                        some evaluatedValue :=
                          hTargetEvaluate

                  let sourceLabel :
                      DTR.BoundPayloadLabel :=
                    DTR.BoundPayloadLabel.sendInt
                      declaredMessageServer
                      (LogicalTime.after
                        sourceTime
                        sourceDelay)
                      evaluatedValue

                  let sourceAfter :
                      DTR.BoundPayloadState := {

                    currentTime :=
                      sourceTime

                    stateValue :=
                      sourceStateValue

                    parameters :=
                      sourceParameters

                    pendingMessages :=
                      pendingMessages ++ [
                        DTR.PendingMessage.scheduleWithPayload
                          sourceTime
                          declaredMessageServer
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
                      DTR.BoundPayloadStep.selfSendInt
                        (declaredMessageServer :=
                          declaredMessageServer)
                        (currentTime :=
                          sourceTime)
                        (stateValue :=
                          sourceStateValue)
                        (parameters :=
                          sourceParameters)
                        (pendingMessages :=
                          pendingMessages)
                        (targetMessage :=
                          declaredMessageServer)
                        (payloadExpression :=
                          sourceExpression)
                        (delay :=
                          sourceDelay)
                        (evaluatedValue :=
                          evaluatedValue)
                        (remaining :=
                          sourceRemaining)
                        rfl
                        hSourceEvaluate

                  · unfold
                      BoundPayloadLabelCorresponds

                    refine
                      ⟨rfl,
                       ?_,
                       rfl⟩

                    calc
                      (LF.Tag.schedule
                        currentTag
                        sourceDelay).time =
                        LogicalTime.after
                          currentTag.time
                          sourceDelay :=

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

                  · exact {
                      currentTime :=
                        hCurrentTime

                      stateValue :=
                        rfl

                      parameters :=
                        rfl

                      pendingEvents :=
                        payloadQueueCorresponds_append_scheduleWithPayload
                          hPending
                          sourceTime
                          currentTag
                          declaredMessageServer
                          [
                            evaluatedValue
                          ]
                          sourceDelay
                          hCurrentTime

                      activeBody :=
                        rfl
                    }

end Correctness
end Relico
