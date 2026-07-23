import Relico.DTR.Semantics
import Relico.DTR.StoreEvaluation
import Relico.DTR.StoreState

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Small-step statement semantics over a finite state-variable store.

The declaration list may contain multiple state variables. Assignment
is enabled when:

- its target occurs in the declaration list; and
- its expression evaluates successfully in the current store.

The message-server parameter identifies the self-message supported by
the current semantic fragment.
-/
inductive StoreStep
    (declaredVariables : List VarName)
    (messageServer : MsgName) :
    DTR.StoreState →
    DTR.Label →
    DTR.StoreState →
    Prop where

  | assign
      (currentTime : LogicalTime)
      (stateStore : StateStore)
      (pendingMessages : MessageBag)
      (target : VarName)
      (expression : Expr)
      (evaluatedValue : Int)
      (remaining : Body)
      (hTarget :
        target ∈ declaredVariables)
      (hEvaluate :
        Expr.evaluateStore
            stateStore
            expression =
          some evaluatedValue) :

      StoreStep
        declaredVariables
        messageServer
        {
          currentTime :=
            currentTime

          stateStore :=
            stateStore

          pendingMessages :=
            pendingMessages

          activeBody :=
            DTR.Stmt.assign
              target
              expression ::
            remaining
        }
        DTR.Label.internal
        {
          currentTime :=
            currentTime

          stateStore :=
            StateStore.update
              stateStore
              target
              evaluatedValue

          pendingMessages :=
            pendingMessages

          activeBody :=
            remaining
        }

  | selfSend
      (currentTime : LogicalTime)
      (stateStore : StateStore)
      (pendingMessages : MessageBag)
      (targetMessage : MsgName)
      (delay : Delay)
      (remaining : Body)
      (hTarget :
        targetMessage =
          messageServer) :

      StoreStep
        declaredVariables
        messageServer
        {
          currentTime :=
            currentTime

          stateStore :=
            stateStore

          pendingMessages :=
            pendingMessages

          activeBody :=
            DTR.Stmt.selfSend
              targetMessage
              delay ::
            remaining
        }
        (DTR.Label.send
          targetMessage
          (LogicalTime.after
            currentTime
            delay))
        {
          currentTime :=
            currentTime

          stateStore :=
            stateStore

          pendingMessages :=
            pendingMessages ++ [
              {
                name :=
                  targetMessage

                arrivalTime :=
                  LogicalTime.after
                    currentTime
                    delay
              }
            ]

          activeBody :=
            remaining
        }

namespace StoreStep

/--
Every DTR store step preserves coverage of the declared variables.

Assignment preserves coverage through `StateStore.covers_update`.
Self-send leaves the state store unchanged.
-/
theorem preserves_coverage
    {declaredVariables : List VarName}
    {messageServer : MsgName}
    {before after : DTR.StoreState}
    {label : DTR.Label}
    (hStep :
      DTR.StoreStep
        declaredVariables
        messageServer
        before
        label
        after)
    (hCoverage :
      DTR.StoreState.Covers
        declaredVariables
        before) :
    DTR.StoreState.Covers
      declaredVariables
      after := by

  cases hStep with

  | assign
      currentTime
      stateStore
      pendingMessages
      target
      expression
      evaluatedValue
      remaining
      hTarget
      hEvaluate =>

      change
        StateStore.Covers
          declaredVariables
          (StateStore.update
            stateStore
            target
            evaluatedValue)

      exact
        StateStore.covers_update
          declaredVariables
          stateStore
          target
          evaluatedValue
          hCoverage

  | selfSend
      currentTime
      stateStore
      pendingMessages
      targetMessage
      delay
      remaining
      hTarget =>

      change
        StateStore.Covers
          declaredVariables
          stateStore

      exact hCoverage

end StoreStep
end DTR
end Relico
