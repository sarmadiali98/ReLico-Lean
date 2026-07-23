import Relico.Correctness.Correspondence
import Relico.Correctness.Expression
import Relico.Correctness.Inversion
import Relico.Correctness.RuntimeInvariant

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Backward simulation for the statement-level SOS rules in vertical
slice v0.

Every assignment or logical-action scheduling transition performed by
the generated LF program from a corresponding state can be matched by
a DTR transition. The labels and resulting runtime states correspond.

Runtime well-formedness ensures that the recovered source assignment
and self-send target declarations belonging to the source model.
-/
theorem step_backward
    {model : DTR.Model}
    {sourceState : DTR.State}
    {targetState targetStateAfter : LF.State}
    {targetLabel : LF.Label}
    (hTargetStep :
      LF.Step
        (Translation.translateCore model)
        targetState
        targetLabel
        targetStateAfter)
    (hStates :
      StateCorresponds
        sourceState
        targetState)
    (hSourceWellFormed :
      DTR.State.WellFormed
        model
        sourceState) :
    ∃ sourceLabel sourceStateAfter,
      DTR.Step
          model
          sourceState
          sourceLabel
          sourceStateAfter ∧
      LabelCorresponds
          sourceLabel
          targetLabel ∧
      StateCorresponds
          sourceStateAfter
          targetStateAfter := by

  cases hTargetStep with

  | assign
      currentTag
      targetStateValue
      pendingActions
      targetVar
      targetExpression
      targetRemaining
      hTargetVar =>

      cases sourceState with
      | mk
          sourceTime
          sourceStateValue
          pendingMessages
          sourceBody =>

          have hCurrentTime :
              currentTag.time = sourceTime := by
            simpa using hStates.currentTime

          have hStateValue :
              targetStateValue = sourceStateValue := by
            simpa using hStates.stateValue

          have hPendingEvents :
              QueueCorresponds
                pendingMessages
                pendingActions := by
            simpa using hStates.pendingEvents

          have hCompiledBody :
              Translation.compileBody sourceBody =
                LF.Stmt.assign
                    targetVar
                    targetExpression ::
                  targetRemaining := by
            simpa using hStates.activeBody.symm

          rcases
              compileBody_assign_head hCompiledBody
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

          have hBodyParts :=
            (DTR.Body.wellFormed_cons
              model.reactiveClass.stateVar
              model.reactiveClass.messageServer.name
              (DTR.Stmt.assign
                sourceVar
                sourceExpression)
              sourceRemaining).mp
              hSourceWellFormed.activeBodyWellFormed

          have hSourceTarget :
              sourceVar =
                model.reactiveClass.stateVar :=
            hBodyParts.1.1

          refine
            ⟨DTR.Label.internal,
             {
               currentTime := sourceTime
               stateValue :=
                 DTR.Expr.evaluate
                   sourceStateValue
                   sourceExpression
               pendingMessages := pendingMessages
               activeBody := sourceRemaining
             },
             ?_,
             LabelCorresponds.internal,
             ?_⟩

          · exact
              DTR.Step.assign
                (model := model)
                (currentTime := sourceTime)
                (stateValue := sourceStateValue)
                (pendingMessages := pendingMessages)
                (target := sourceVar)
                (expression := sourceExpression)
                (remaining := sourceRemaining)
                hSourceTarget

          · refine {
              currentTime :=
                hCurrentTime

              stateValue := ?_

              pendingEvents :=
                hPendingEvents

              activeBody := rfl
            }

            calc
              LF.Expr.evaluate
                  targetStateValue
                  (Translation.compileExpr
                    sourceExpression)
                  =
                LF.Expr.evaluate
                  sourceStateValue
                  (Translation.compileExpr
                    sourceExpression) := by
                      rw [hStateValue]

              _ =
                DTR.Expr.evaluate
                  sourceStateValue
                  sourceExpression := by
                    exact
                      compileExpr_preserves_evaluation
                        sourceExpression
                        sourceStateValue

  | schedule
      currentTag
      targetStateValue
      pendingActions
      targetAction
      targetDelay
      targetRemaining
      hTargetAction =>

      cases sourceState with
      | mk
          sourceTime
          sourceStateValue
          pendingMessages
          sourceBody =>

          have hCurrentTime :
              currentTag.time = sourceTime := by
            simpa using hStates.currentTime

          have hStateValue :
              targetStateValue = sourceStateValue := by
            simpa using hStates.stateValue

          have hPendingEvents :
              QueueCorresponds
                pendingMessages
                pendingActions := by
            simpa using hStates.pendingEvents

          have hCompiledBody :
              Translation.compileBody sourceBody =
                LF.Stmt.schedule
                    targetAction
                    targetDelay ::
                  targetRemaining := by
            simpa using hStates.activeBody.symm

          rcases
              compileBody_schedule_head hCompiledBody
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

          have hBodyParts :=
            (DTR.Body.wellFormed_cons
              model.reactiveClass.stateVar
              model.reactiveClass.messageServer.name
              (DTR.Stmt.selfSend
                sourceMessage
                sourceDelay)
              sourceRemaining).mp
              hSourceWellFormed.activeBodyWellFormed

          have hSourceTarget :
              sourceMessage =
                model.reactiveClass.messageServer.name :=
            hBodyParts.1

          refine
            ⟨DTR.Label.send
                sourceMessage
                (LogicalTime.after
                  sourceTime
                  sourceDelay),
             {
               currentTime := sourceTime
               stateValue := sourceStateValue
               pendingMessages :=
                 pendingMessages ++
                   [{
                     name := sourceMessage
                     arrivalTime :=
                       LogicalTime.after
                         sourceTime
                         sourceDelay
                   }]
               activeBody := sourceRemaining
             },
             ?_,
             ?_,
             ?_⟩

          · exact
              DTR.Step.selfSend
                (model := model)
                (currentTime := sourceTime)
                (stateValue := sourceStateValue)
                (pendingMessages := pendingMessages)
                (targetMessage := sourceMessage)
                (delay := sourceDelay)
                (remaining := sourceRemaining)
                hSourceTarget

          · rw [hTargetActionGenerated]

            apply LabelCorresponds.send
              sourceMessage
              (LogicalTime.after
                sourceTime
                sourceDelay)
              (LF.Tag.schedule
                currentTag
                sourceDelay)

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

              stateValue :=
                hStateValue

              pendingEvents := ?_

              activeBody := rfl
            }

            rw [hTargetActionGenerated]

            apply QueueCorresponds.append_one
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
