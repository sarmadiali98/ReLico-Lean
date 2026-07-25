import Relico.DTR.MultiStoreMachineSemantics
import Relico.DTR.PriorityTimingWellFormed

set_option autoImplicit false

namespace Relico
namespace DTR

namespace MultiStoreStep

/--
Executing one source statement preserves priority timing
well-formedness of the remaining active body.
-/
theorem preserves_priorityTimingWellFormed
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
      DTR.Body.PriorityTimingWellFormed
        before.activeBody) :
    DTR.Body.PriorityTimingWellFormed
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
        ((DTR.Body.priorityTimingWellFormed_cons
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
        ((DTR.Body.priorityTimingWellFormed_cons
          (DTR.Stmt.selfSend
            targetMessage
            delay)
          remaining).mp
          hBefore).2

end MultiStoreStep

namespace MultiStoreMachineStep

/--
A combined source-machine step preserves active-body priority timing
when every declared message-server body satisfies the same restriction.

Statement execution removes the current body head. Dispatch loads the
selected declared message-server body.
-/
theorem preserves_priorityTimingWellFormed
    {declaredVariables : List VarName}
    {messageServers : List DTR.MessageServer}
    {before after : DTR.StoreState}
    {label : DTR.MultiStoreMachineLabel}
    (hStep :
      DTR.MultiStoreMachineStep
        declaredVariables
        messageServers
        before
        label
        after)
    (hMessageBodies :
      ∀ messageServer,
        messageServer ∈
            messageServers →
          DTR.Body.PriorityTimingWellFormed
            messageServer.body)
    (hBefore :
      DTR.Body.PriorityTimingWellFormed
        before.activeBody) :
    DTR.Body.PriorityTimingWellFormed
      after.activeBody := by

  cases hStep with

  | statement hStatement =>
      exact
        DTR.MultiStoreStep.preserves_priorityTimingWellFormed
          hStatement
          hBefore

  | dispatch hDispatch =>
      cases hDispatch with

      | fire
          currentTime
          stateStore
          pendingMessages
          remainingMessages
          selectedMessage
          selectedServer
          hServerDeclared
          hRemoved
          hPriorityEligible
          hNotPast
          hTarget =>

          exact
            hMessageBodies
              _
              hServerDeclared

end MultiStoreMachineStep
end DTR
end Relico
