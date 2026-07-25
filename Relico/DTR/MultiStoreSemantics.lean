import Relico.DTR.MultiStoreWellFormed
import Relico.DTR.StoreEvaluation
import Relico.DTR.StoreState
import Relico.DTR.Semantics

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Small-step statement semantics over a finite store with multiple
declared message servers.
-/
inductive MultiStoreStep
    (declaredVariables : List VarName)
    (declaredMessageServers : List MsgName) :
    DTR.StoreState →
    DTR.Label →
    DTR.StoreState →
    Prop where

  | assign
      (currentTime : LogicalTime)
      (stateStore : StateStore)
      (pendingMessages : DTR.MessageBag)
      (target : VarName)
      (expression : DTR.Expr)
      (evaluatedValue : Int)
      (remaining : DTR.Body)
      (hTarget :
        target ∈ declaredVariables)
      (hEvaluate :
        DTR.Expr.evaluateStore
            stateStore
            expression =
          some evaluatedValue) :

      MultiStoreStep
        declaredVariables
        declaredMessageServers
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
      (pendingMessages : DTR.MessageBag)
      (targetMessage : MsgName)
      (delay : Delay)
      (remaining : DTR.Body)
      (hTarget :
        targetMessage ∈
          declaredMessageServers) :

      MultiStoreStep
        declaredVariables
        declaredMessageServers
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

namespace MultiStoreStep

/--
Every multi-server statement step preserves state-store coverage.
-/
theorem preserves_coverage
    {declaredVariables : List VarName}
    {declaredMessageServers : List MsgName}
    {before after : DTR.StoreState}
    {label : DTR.Label}
    (hStep :
      DTR.MultiStoreStep
        declaredVariables
        declaredMessageServers
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

      exact hCoverage

/--
A statement step removes the active-body head and therefore preserves
well-formedness of the remaining body.
-/
theorem preserves_body_multiStoreWellFormed
    {declaredVariables : List VarName}
    {declaredMessageServers : List MsgName}
    {before after : DTR.StoreState}
    {label : DTR.Label}
    (hStep :
      DTR.MultiStoreStep
        declaredVariables
        declaredMessageServers
        before
        label
        after)
    (hBefore :
      DTR.Body.MultiStoreWellFormed
        declaredVariables
        declaredMessageServers
        before.activeBody) :
    DTR.Body.MultiStoreWellFormed
      declaredVariables
      declaredMessageServers
      after.activeBody := by

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

      exact
        ((DTR.Body.multiStoreWellFormed_cons
          declaredVariables
          declaredMessageServers
          (DTR.Stmt.assign
            target
            expression)
          remaining).mp
          hBefore).2

  | selfSend
      currentTime
      stateStore
      pendingMessages
      targetMessage
      delay
      remaining
      hTarget =>

      exact
        ((DTR.Body.multiStoreWellFormed_cons
          declaredVariables
          declaredMessageServers
          (DTR.Stmt.selfSend
            targetMessage
            delay)
          remaining).mp
          hBefore).2

/--
Statement execution preserves the invariant that every pending message
targets a declared message server.
-/
theorem preserves_pendingTargets
    {declaredVariables : List VarName}
    {declaredMessageServers : List MsgName}
    {before after : DTR.StoreState}
    {label : DTR.Label}
    (hStep :
      DTR.MultiStoreStep
        declaredVariables
        declaredMessageServers
        before
        label
        after)
    (hTargets :
      ∀ pendingMessage,
        pendingMessage ∈
          before.pendingMessages →
        pendingMessage.name ∈
          declaredMessageServers) :
    ∀ pendingMessage,
      pendingMessage ∈
        after.pendingMessages →
      pendingMessage.name ∈
        declaredMessageServers := by

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

      simpa using
        hTargets

  | selfSend
      currentTime
      stateStore
      pendingMessages
      targetMessage
      delay
      remaining
      hTarget =>

      intro pendingMessage hMember

      simp only [
        List.mem_append,
        List.mem_singleton
      ] at hMember

      rcases hMember with
        hExisting | hAdded

      · exact
          hTargets
            pendingMessage
            hExisting

      · subst pendingMessage
        exact hTarget

end MultiStoreStep
end DTR
end Relico
