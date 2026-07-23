import Relico.DTR.Scheduling
import Relico.DTR.Syntax

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Dispatch transition for a pending DTR message.

Dispatch is enabled only when the currently active body is empty. The
rule removes one concrete earliest message occurrence, advances logical
time to its arrival time, and loads the model's message-server body.
-/
inductive DispatchStep
    (model : DTR.Model) :
    DTR.State →
    DTR.PendingMessage →
    DTR.State →
    Prop where

  | fire
      (currentTime : LogicalTime)
      (stateValue : Int)
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
          model.reactiveClass.messageServer.name) :
      DispatchStep
        model
        {
          currentTime := currentTime
          stateValue := stateValue
          pendingMessages := pendingMessages
          activeBody := []
        }
        selectedMessage
        {
          currentTime :=
            selectedMessage.arrivalTime
          stateValue := stateValue
          pendingMessages := remainingMessages
          activeBody :=
            model.reactiveClass.messageServer.body
        }

end DTR
end Relico
