import Relico.DTR.Scheduling
import Relico.DTR.StoreState

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Dispatch semantics for a pending DTR message over a finite state store.

Dispatch is enabled only when the active body is empty. One concrete
earliest message occurrence is removed, logical time advances to its
arrival time, and the declared message body becomes active.
-/
inductive StoreDispatchStep
    (messageServer : MsgName)
    (messageBody : DTR.Body) :
    DTR.StoreState →
    DTR.PendingMessage →
    DTR.StoreState →
    Prop where

  | fire
      (currentTime : LogicalTime)
      (stateStore : StateStore)
      (pendingMessages remainingMessages : MessageBag)
      (selectedMessage : PendingMessage)
      (hRemoved :
        Occurrence.RemovesOne
          selectedMessage
          pendingMessages
          remainingMessages)
      (hEarliest :
        DTR.IsEarliest
          selectedMessage
          pendingMessages)
      (hNotPast :
        currentTime ≤
          selectedMessage.arrivalTime)
      (hTarget :
        selectedMessage.name =
          messageServer) :

      StoreDispatchStep
        messageServer
        messageBody
        {
          currentTime :=
            currentTime

          stateStore :=
            stateStore

          pendingMessages :=
            pendingMessages

          activeBody :=
            []
        }
        selectedMessage
        {
          currentTime :=
            selectedMessage.arrivalTime

          stateStore :=
            stateStore

          pendingMessages :=
            remainingMessages

          activeBody :=
            messageBody
        }

namespace StoreDispatchStep

/--
Dispatch preserves coverage because it leaves the complete state store
unchanged.
-/
theorem preserves_coverage
    {messageServer : MsgName}
    {messageBody : DTR.Body}
    {declaredVariables : List VarName}
    {before after : DTR.StoreState}
    {selectedMessage : DTR.PendingMessage}
    (hDispatch :
      DTR.StoreDispatchStep
        messageServer
        messageBody
        before
        selectedMessage
        after)
    (hCoverage :
      DTR.StoreState.Covers
        declaredVariables
        before) :
    DTR.StoreState.Covers
      declaredVariables
      after := by

  cases hDispatch

  exact hCoverage

end StoreDispatchStep
end DTR
end Relico
