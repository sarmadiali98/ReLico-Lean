import Relico.Correctness.MultiStoreMachine
import Relico.DTR.PriorityTimingInvariant
import Relico.LF.PriorityTimingInvariant

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
If a generated active body begins with a schedule statement and is the
translation of a priority-timing-well-formed source body, that schedule
has a strictly positive delay.
-/
theorem compiledScheduleHead_positive
    {sourceBody : DTR.Body}
    {targetAction : ActionName}
    {delay : Delay}
    {targetRemaining : LF.Body}
    (hCompiled :
      LF.Stmt.schedule
            targetAction
            delay ::
          targetRemaining =
        Translation.compileBody
          sourceBody)
    (hTiming :
      DTR.Body.PriorityTimingWellFormed
        sourceBody) :
    0 < delay.value := by

  let extractScheduleDelay :
      LF.Body →
      Option Delay :=
    fun body =>
      match body with
      | LF.Stmt.schedule _ extractedDelay :: _ =>
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
          Translation.compileBody
        ] using
          congrArg
            extractScheduleDelay
            hCompiled

      cases hImpossible

  | cons sourceStatement sourceRemaining =>
      cases sourceStatement with

      | assign sourceTarget sourceExpression =>
          have hImpossible :
              (some delay : Option Delay) =
                none := by

            simpa [
              extractScheduleDelay,
              Translation.compileBody,
              Translation.compileStmt
            ] using
              congrArg
                extractScheduleDelay
                hCompiled

          cases hImpossible

      | selfSend sourceTarget sourceDelay =>
          have hSome :
              (some delay : Option Delay) =
                some sourceDelay := by

            simpa [
              extractScheduleDelay,
              Translation.compileBody,
              Translation.compileStmt
            ] using
              congrArg
                extractScheduleDelay
                hCompiled

          have hDelay :
              delay =
                sourceDelay := by

            injection hSome

          have hHeadTiming :
              DTR.Stmt.PriorityTimingWellFormed
                (DTR.Stmt.selfSend
                  sourceTarget
                  sourceDelay) :=

            ((DTR.Body.priorityTimingWellFormed_cons
              (DTR.Stmt.selfSend
                sourceTarget
                sourceDelay)
              sourceRemaining).mp
              hTiming).1

          have hSourcePositive :
              0 < sourceDelay.value := by

            simpa [
              DTR.Stmt.PriorityTimingWellFormed
            ] using
              hHeadTiming

          simpa [
            hDelay
          ] using
            hSourcePositive

/--
A generated multi-server machine step preserves the zero-microstep
queue invariant when its corresponding source active body satisfies
the positive-delay priority timing restriction.

Assignments leave the queue unchanged. Positive-delay schedules append
a zero-microstep action. Dispatch removes one action.
-/
theorem targetMultiStoreMachineStep_preserves_pendingMicrostepsZero
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {sourceState : DTR.StoreState}
    {targetState targetStateAfter : LF.StoreState}
    {targetLabel : LF.MultiStoreMachineLabel}
    (hTargetStep :
      LF.MultiStoreMachineStep
        declaredVariables
        (Translation.compileLogicalActions
          messageServers)
        (Translation.compileMessageReactions
          messageServers)
        targetState
        targetLabel
        targetStateAfter)
    (hStates :
      StoreStateCorresponds
        sourceState
        targetState)
    (hSourceTiming :
      DTR.Body.PriorityTimingWellFormed
        sourceState.activeBody)
    (hTargetTiming :
      LF.StoreState.PendingMicrostepsZero
        targetState) :
    LF.StoreState.PendingMicrostepsZero
      targetStateAfter := by

  cases hTargetStep with

  | statement hStatement =>
      cases hStatement with

      | assign
          currentTag
          stateStore
          pendingActions
          target
          expression
          evaluatedValue
          remaining
          hTarget
          hEvaluate =>

          exact
            hTargetTiming

      | schedule
          currentTag
          stateStore
          pendingActions
          targetAction
          delay
          remaining
          hTarget =>

          have hPositive :
              0 < delay.value :=

            compiledScheduleHead_positive
              hStates.activeBody
              hSourceTiming

          exact
            LF.MultiStoreStep.schedule_preserves_pendingMicrostepsZero
              currentTag
              pendingActions
              targetAction
              delay
              hTargetTiming
              hPositive

  | dispatch hDispatch =>
      exact
        LF.MultiStoreDispatchStep.preserves_pendingMicrostepsZero
          hDispatch
          hTargetTiming

end Correctness
end Relico
