/-
Copyright (c) 2026.

Forward simulation for ordinary store-backed DTR statements and their
generated LF statements.

The state correspondence relates the ordinary DTR pending-message bag to the
ordinary LF action queue through the permutation-invariant,
selection-compatible correspondence.

A self-send requires the newly generated source and target occurrences to
satisfy the approved selection-compatibility/non-overtaking condition against
all retained aligned occurrences.

No source-side microstep, ghost state, or restricted source semantics is
introduced.
-/

import Relico.Correctness.DirectLFSelectionAppend
import Relico.Correctness.ExpressionStore
import Relico.DTR.MultiStoreSemantics
import Relico.LF.MultiStoreSemantics
import Relico.Translation.MultiStoreBasic

set_option autoImplicit false

namespace Relico
namespace Correctness
/--
Correspondence between ordinary store-backed DTR and LF runtime states for the
direct translation.

Pending occurrences are related by the permutation-invariant, selection-aware
relation. No LF microstep is added to the DTR state.
-/
structure DirectLFStoreStateCorresponds
    (messageServers :
      List DTR.MessageServer)
    (sourceState :
      DTR.StoreState)
    (targetState :
      LF.StoreState) :
    Prop where

  currentTime :
    targetState.currentTag.time =
      sourceState.currentTime

  stateStore :
    targetState.stateStore =
      sourceState.stateStore

  pendingEvents :
    DirectLFSelectionCompatible
      messageServers
      sourceState.pendingMessages
      targetState.pendingActions

  activeBody :
    targetState.activeBody =
      Translation.compileBody
        sourceState.activeBody

/--
The new state relation retains occurrence-preserving bag/action-queue
correspondence.
-/
theorem DirectLFStoreStateCorresponds.toBagQueueCorresponds
    {messageServers :
      List DTR.MessageServer}
    {sourceState :
      DTR.StoreState}
    {targetState :
      LF.StoreState}
    (hStates :
      DirectLFStoreStateCorresponds
        messageServers
        sourceState
        targetState) :
    DirectLFBagQueueCorresponds
      sourceState.pendingMessages
      targetState.pendingActions :=
  hStates.pendingEvents.toBagQueueCorresponds

/--
Step-local supported-fragment condition for the statement at the head of the
source body.

Assignments impose no queue obligation.

For a self-send, the exact source occurrence and generated LF occurrence must
satisfy `DirectLFSelectionAppendCompatible`. This packages:

* the pre-existing selection-compatible pending collections;
* structural correspondence of the new occurrences; and
* pairwise non-overtaking between the new occurrence and every retained
  aligned occurrence.
-/
def DirectLFStatementAppendCompatible
    (messageServers :
      List DTR.MessageServer)
    (sourceState :
      DTR.StoreState)
    (targetState :
      LF.StoreState) :
    Prop :=
  match sourceState.activeBody with

  | DTR.Stmt.selfSend
        targetMessage
        delay ::
      _remaining =>

      DirectLFSelectionAppendCompatible
        messageServers
        sourceState.pendingMessages
        targetState.pendingActions
        {
          name :=
            targetMessage

          arrivalTime :=
            LogicalTime.after
              sourceState.currentTime
              delay
        }
        {
          name :=
            Translation.actionNameFor
              targetMessage

          tag :=
            LF.Tag.schedule
              targetState.currentTag
              delay
        }

  | _ =>
      True

/--
Forward simulation for one ordinary multiple-message-server statement step.

The executable DTR and LF operational semantics are unchanged.

The additional statement-append premise is relevant only to self-send. It is
the local preservation form of the approved direct-LF selection-compatibility
condition.
-/
theorem directLF_multiStore_step_forward
    {declaredVariables :
      List VarName}
    {messageServers :
      List DTR.MessageServer}
    {sourceState sourceStateAfter :
      DTR.StoreState}
    {sourceLabel :
      DTR.Label}
    {targetState :
      LF.StoreState}
    (hSourceStep :
      DTR.MultiStoreStep
        declaredVariables
        (DTR.messageServerNames
          messageServers)
        sourceState
        sourceLabel
        sourceStateAfter)
    (hStates :
      DirectLFStoreStateCorresponds
        messageServers
        sourceState
        targetState)
    (hStatementAppend :
      DirectLFStatementAppendCompatible
        messageServers
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
        DirectLFStoreStateCorresponds
          messageServers
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
              DirectLFSelectionCompatible
                messageServers
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

          have hStore :
              targetStore =
                sourceStore :=
            hStates.stateStore

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

          have hAppend :
              DirectLFSelectionAppendCompatible
                messageServers
                pendingMessages
                pendingActions
                {
                  name :=
                    targetMessage

                  arrivalTime :=
                    LogicalTime.after
                      currentTime
                      delay
                }
                {
                  name :=
                    Translation.actionNameFor
                      targetMessage

                  tag :=
                    LF.Tag.schedule
                      targetTag
                      delay
                } := by

            simpa [
              DirectLFStatementAppendCompatible
            ] using
              hStatementAppend

          subst targetStore
          subst targetBody

          have hTargetAction :
              Translation.actionNameFor
                  targetMessage ∈
                Translation.compileLogicalActions
                  messageServers := by

            exact
              (Translation.actionName_mem_compileLogicalActions_iff
                targetMessage
                messageServers).mpr
                  hTarget

          let scheduledTag :
              LF.Tag :=
            LF.Tag.schedule
              targetTag
              delay

          let sourceNew :
              DTR.PendingMessage := {
            name :=
              targetMessage

            arrivalTime :=
              LogicalTime.after
                currentTime
                delay
          }

          let targetNew :
              LF.PendingAction := {
            name :=
              Translation.actionNameFor
                targetMessage

            tag :=
              scheduledTag
          }

          let targetStateAfter :
              LF.StoreState := {
            currentTag :=
              targetTag

            stateStore :=
              sourceStore

            pendingActions :=
              pendingActions ++ [
                targetNew
              ]

            activeBody :=
              Translation.compileBody
                remaining
          }

          have hPostPending :
              DirectLFSelectionCompatible
                messageServers
                (pendingMessages ++ [
                  sourceNew
                ])
                (pendingActions ++ [
                  targetNew
                ]) := by

            simpa [
              sourceNew,
              targetNew,
              scheduledTag
            ] using
              hAppend.append_one

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
              scheduledTag.time =
                LogicalTime.after
                  currentTime
                  delay

            calc
              scheduledTag.time =
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

                rw [
                  hCurrentTime
                ]

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

            simpa [
              sourceNew,
              targetNew,
              targetStateAfter
            ] using
              hPostPending

end Correctness
end Relico
