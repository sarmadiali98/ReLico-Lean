import Relico.Correctness.DetailedBoundPayloadRuntimeInvariant
import Relico.Correctness.BoundPayloadStep
import Relico.Correctness.BoundPayloadDispatch

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
If the compiled target active body begins with a payload schedule and the
corresponding source body satisfies the internal positive-delay restriction,
then that target schedule has a strictly positive delay.

Bound-payload body compilation preserves the source self-send delay exactly.
-/
theorem compiledBoundPayloadScheduleHead_positive
    {sourceBody : DTR.BoundPayloadBody}
    {targetAction : ActionName}
    {targetExpression : LF.PayloadExpr}
    {delay : Delay}
    {targetRemaining : LF.BoundPayloadBody}
    (hCompiled :
      LF.BoundPayloadStmt.scheduleInt
            targetAction
            targetExpression
            delay ::
          targetRemaining =
        Translation.compileBoundPayloadBody
          sourceBody)
    (hTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceBody) :
    0 < delay.value := by

  let extractScheduleDelay :
      LF.BoundPayloadBody →
      Option Delay :=
    fun body =>
      match body with
      | LF.BoundPayloadStmt.scheduleInt
            _targetAction
            _payloadExpression
            extractedDelay ::
          _remaining =>
            some extractedDelay
      | _ =>
          none

  cases sourceBody with

  | nil =>
      have hImpossible :
          (some delay : Option Delay) =
            none := by

        simpa [
          extractScheduleDelay,
          Translation.compileBoundPayloadBody
        ] using
          congrArg
            extractScheduleDelay
            hCompiled

      cases hImpossible

  | cons sourceStatement sourceRemaining =>
      cases sourceStatement with

      | selfSendInt
          sourceTarget
          sourceExpression
          sourceDelay =>

          have hSome :
              (some delay : Option Delay) =
                some sourceDelay := by

            simpa [
              extractScheduleDelay,
              Translation.compileBoundPayloadBody,
              Translation.compileBoundPayloadStmt
            ] using
              congrArg
                extractScheduleDelay
                hCompiled

          have hDelay :
              delay =
                sourceDelay := by

            injection hSome

          have hHeadTiming :
              DTR.BoundPayloadStmt.PriorityTimingWellFormed
                (.selfSendInt
                  sourceTarget
                  sourceExpression
                  sourceDelay) :=

            ((DTR.BoundPayloadBody.priorityTimingWellFormed_cons
              (.selfSendInt
                sourceTarget
                sourceExpression
                sourceDelay)
              sourceRemaining).mp
              hTiming).1

          have hSourcePositive :
              0 < sourceDelay.value :=

            (DTR.BoundPayloadStmt.priorityTimingWellFormed_selfSendInt
              sourceTarget
              sourceExpression
              sourceDelay).mp
              hHeadTiming

          simpa [
            hDelay
          ] using
            hSourcePositive

/--
One source payload statement step preserves source-body timing
well-formedness.

The unique statement constructor consumes the current self-send and retains
the well-formed tail.
-/
theorem boundPayloadStep_preserves_priorityTimingWellFormed
    {declaredMessageServer : MsgName}
    {before after : DTR.BoundPayloadState}
    {label : DTR.BoundPayloadLabel}
    (hStep :
      DTR.BoundPayloadStep
        declaredMessageServer
        before
        label
        after)
    (hTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        before.activeBody) :
    DTR.BoundPayloadBody.PriorityTimingWellFormed
      after.activeBody := by

  cases hStep with

  | selfSendInt
      currentTime
      stateValue
      parameters
      pendingMessages
      targetMessage
      payloadExpression
      delay
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      exact
        DTR.BoundPayloadBody.priorityTimingWellFormed_tail
          hTiming

/--
A corresponding generated-LF payload statement step preserves the target
runtime invariant.

The source timing restriction and active-body correspondence prove that the
compiled schedule delay is positive. Therefore:

- the newly appended action has microstep zero;
- existing queued actions retain microstep zero;
- if the current tag already has microstep zero, it remains unchanged;
- otherwise the new positive-delay action, like every existing action, is
  strictly later in logical time.
-/
theorem targetBoundPayloadStep_preserves_runtimeInvariant
    {declaredMessageServer : MsgName}
    {sourceBefore : DTR.BoundPayloadState}
    {targetBefore targetAfter : LF.BoundPayloadState}
    {targetLabel : LF.BoundPayloadLabel}
    (hTargetStep :
      LF.BoundPayloadStep
        (Translation.actionNameFor
          declaredMessageServer)
        targetBefore
        targetLabel
        targetAfter)
    (hStates :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSourceTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceBefore.activeBody)
    (hTargetInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetBefore) :
    LF.BoundPayloadState.RuntimeInvariant
      targetAfter := by

  cases hTargetStep with

  | scheduleInt
      currentTag
      stateValue
      parameters
      pendingActions
      targetAction
      payloadExpression
      delay
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      have hPositive :
          0 < delay.value :=

        compiledBoundPayloadScheduleHead_positive
          hStates.activeBody
          hSourceTiming

      refine {
        pendingMicrostepsZero := ?_
        currentZeroOrPendingStrictlyFuture := ?_
      }

      · apply
          LF.ActionQueue.allMicrostepsZero_append_one
            hTargetInvariant.pendingMicrostepsZero

        simpa [
          LF.PendingAction.scheduleWithPayload
        ] using
          boundPayloadSchedule_positive_microstepZero
            currentTag
            delay
            hPositive

      · rcases
            hTargetInvariant.currentZeroOrPendingStrictlyFuture
          with
            hCurrentMicrostepZero |
            hPendingStrictlyFuture

        · exact
            Or.inl
              hCurrentMicrostepZero

        · apply
            Or.inr

          intro action hAction

          simp only [
            List.mem_append,
            List.mem_singleton
          ] at hAction

          rcases hAction with
            hExisting | hAdded

          · exact
              hPendingStrictlyFuture
                action
                hExisting

          · subst action

            calc
              currentTag.time <
                  LogicalTime.after
                    currentTag.time
                    delay := by

                change
                  currentTag.time <
                    currentTag.time + delay.value

                exact
                  Nat.lt_add_of_pos_right
                    (n := currentTag.time)
                    hPositive

              _ =
                  (LF.PendingAction.scheduleWithPayload
                    currentTag
                    targetAction
                    [
                      evaluatedValue
                    ]
                    delay).tag.time := by

                change
                  LogicalTime.after
                      currentTag.time
                      delay =
                    (LF.Tag.schedule
                      currentTag
                      delay).time

                exact
                  (LF.Tag.schedule_time
                    currentTag
                    delay).symm

/--
One generated-LF payload dispatch preserves the target runtime invariant.

Removal preserves zero microsteps in the residual queue. The selected action
belonged to the original queue and therefore has microstep zero. Since dispatch
sets the current tag to the selected action tag, the post-dispatch state
satisfies the current-microstep-zero disjunct directly.
-/
theorem targetBoundPayloadDispatch_preserves_runtimeInvariant
    {reaction : LF.PayloadReaction}
    {before after : LF.BoundPayloadState}
    {selectedAction : LF.PendingAction}
    (hDispatch :
      LF.BoundPayloadDispatchStep
        reaction
        before
        selectedAction
        after)
    (hBefore :
      LF.BoundPayloadState.RuntimeInvariant
        before) :
    LF.BoundPayloadState.RuntimeInvariant
      after := by

  cases hDispatch with

  | fire
      currentTag
      stateValue
      parameters
      pendingActions
      remainingActions
      selectedAction
      boundParameters
      hRemoved
      hEarliest
      hNotPast
      hTrigger
      hBind =>

      have hSelectedMember :
          selectedAction ∈
            pendingActions :=

        Occurrence.RemovesOne.selected_mem
          hRemoved

      have hSelectedMicrostepZero :
          selectedAction.tag.microstep =
            0 :=

        hBefore.pendingMicrostepsZero
          selectedAction
          hSelectedMember

      exact {
        pendingMicrostepsZero :=
          LF.ActionQueue.allMicrostepsZero_remove
            hBefore.pendingMicrostepsZero
            hRemoved

        currentZeroOrPendingStrictlyFuture :=
          Or.inl
            hSelectedMicrostepZero
      }

/--
Source payload dispatch establishes timing well-formedness for the activated
body when the declared payload server body is timing well formed.

Dispatch replaces the empty active body with `server.body`.
-/
theorem boundPayloadDispatch_establishes_priorityTimingWellFormed
    {server : DTR.PayloadMessageServer}
    {before after : DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    (hDispatch :
      DTR.BoundPayloadDispatchStep
        server
        before
        selectedMessage
        after)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body) :
    DTR.BoundPayloadBody.PriorityTimingWellFormed
      after.activeBody := by

  rw [
    DTR.BoundPayloadDispatchStep.activates_server_body
      hDispatch
  ]

  exact hServerTiming

/--
One matched source payload statement step preserves all recursive execution
data:

- a corresponding generated-LF statement step exists;
- labels and states correspond;
- source-body timing remains well formed;
- the target runtime invariant remains true.
-/
theorem boundPayloadStep_forward_preserves_runtimeInvariants
    {declaredMessageServer : MsgName}
    {sourceBefore sourceAfter : DTR.BoundPayloadState}
    {sourceLabel : DTR.BoundPayloadLabel}
    {targetBefore : LF.BoundPayloadState}
    (hSourceStep :
      DTR.BoundPayloadStep
        declaredMessageServer
        sourceBefore
        sourceLabel
        sourceAfter)
    (hStates :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hSourceTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceBefore.activeBody)
    (hTargetInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetBefore) :
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
          targetAfter ∧
        DTR.BoundPayloadBody.PriorityTimingWellFormed
          sourceAfter.activeBody ∧
        LF.BoundPayloadState.RuntimeInvariant
          targetAfter := by

  rcases
      boundPayloadStep_forward
        hStates
        hSourceStep
    with
      ⟨targetLabel,
       targetAfter,
       hTargetStep,
       hLabels,
       hAfterStates⟩

  have hSourceAfterTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceAfter.activeBody :=

    boundPayloadStep_preserves_priorityTimingWellFormed
      hSourceStep
      hSourceTiming

  have hTargetAfterInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetAfter :=

    targetBoundPayloadStep_preserves_runtimeInvariant
      hTargetStep
      hStates
      hSourceTiming
      hTargetInvariant

  exact
    ⟨targetLabel,
     targetAfter,
     hTargetStep,
     hLabels,
     hAfterStates,
     hSourceAfterTiming,
     hTargetAfterInvariant⟩

/--
One matched source payload dispatch preserves all recursive execution data.

The pre-state target invariant automatically supplies forward scheduler
compatibility. Conditional dispatch correctness then constructs the exact
generated dispatch. Source timing is re-established from the declared server
body, while target timing is preserved by queue removal and selected-action
microstep zero.
-/
theorem boundPayloadDispatch_forward_preserves_runtimeInvariants
    {server : DTR.PayloadMessageServer}
    {sourceBefore sourceAfter : DTR.BoundPayloadState}
    {selectedMessage : DTR.PendingMessage}
    {targetBefore : LF.BoundPayloadState}
    (hSourceDispatch :
      DTR.BoundPayloadDispatchStep
        server
        sourceBefore
        selectedMessage
        sourceAfter)
    (hStates :
      BoundPayloadStateCorresponds
        sourceBefore
        targetBefore)
    (hServerTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        server.body)
    (hTargetInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetBefore) :
    ∃ selectedAction targetAfter,
      LF.BoundPayloadDispatchStep
          (Translation.compilePayloadMessageServer
            server)
          targetBefore
          selectedAction
          targetAfter ∧
        PendingPayloadCorresponds
          selectedMessage
          selectedAction ∧
        BoundPayloadStateCorresponds
          sourceAfter
          targetAfter ∧
        DTR.BoundPayloadBody.PriorityTimingWellFormed
          sourceAfter.activeBody ∧
        LF.BoundPayloadState.RuntimeInvariant
          targetAfter := by

  have hCompatible :
      BoundPayloadForwardDispatchCompatible
        selectedMessage
        sourceAfter.pendingMessages
        targetBefore :=

    boundPayloadForwardDispatchCompatible_of_runtimeInvariant
      hSourceDispatch
      hStates
      hTargetInvariant

  rcases
      boundPayloadDispatch_forward_of_compatible
        hSourceDispatch
        hStates
        hCompatible
    with
      ⟨selectedAction,
       targetAfter,
       hTargetDispatch,
       hSelectedCorresponds,
       hAfterStates⟩

  have hSourceAfterTiming :
      DTR.BoundPayloadBody.PriorityTimingWellFormed
        sourceAfter.activeBody :=

    boundPayloadDispatch_establishes_priorityTimingWellFormed
      hSourceDispatch
      hServerTiming

  have hTargetAfterInvariant :
      LF.BoundPayloadState.RuntimeInvariant
        targetAfter :=

    targetBoundPayloadDispatch_preserves_runtimeInvariant
      hTargetDispatch
      hTargetInvariant

  exact
    ⟨selectedAction,
     targetAfter,
     hTargetDispatch,
     hSelectedCorresponds,
     hAfterStates,
     hSourceAfterTiming,
     hTargetAfterInvariant⟩

end Correctness
end Relico
