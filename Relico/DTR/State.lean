import Relico.DTR.Syntax

set_option autoImplicit false

namespace Relico
namespace DTR

/--
One pending DTR message occurrence.

A list may contain multiple equal values. Each list element represents
one distinct pending occurrence.
-/
structure PendingMessage where
name : MsgName
arrivalTime : LogicalTime

/--
The evaluated argument values carried by this message occurrence.

The default preserves the existing parameter-free fragment exactly.
-/
payload : Payload := []

deriving Repr, DecidableEq, BEq, Inhabited

abbrev MessageBag := List PendingMessage

/--
Runtime state for vertical slice v0.

The active body contains the statements remaining in the constructor
or currently executing message server.
-/
structure State where
currentTime : LogicalTime
stateValue : Int
pendingMessages : MessageBag
activeBody : Body
deriving Repr, DecidableEq, BEq, Inhabited


namespace PendingMessage

/--
Create one pending source-message occurrence with an evaluated payload.
-/
def scheduleWithPayload
    (currentTime : LogicalTime)
    (messageName : MsgName)
    (payload : Payload)
    (delay : Delay) :
    DTR.PendingMessage where

  name :=
    messageName

  arrivalTime :=
    LogicalTime.after
      currentTime
      delay

  payload :=
    payload

@[simp]
theorem scheduleWithPayload_name
    (currentTime : LogicalTime)
    (messageName : MsgName)
    (payload : Payload)
    (delay : Delay) :
    (scheduleWithPayload
      currentTime
      messageName
      payload
      delay).name =
        messageName := by
  rfl

@[simp]
theorem scheduleWithPayload_arrivalTime
    (currentTime : LogicalTime)
    (messageName : MsgName)
    (payload : Payload)
    (delay : Delay) :
    (scheduleWithPayload
      currentTime
      messageName
      payload
      delay).arrivalTime =
        LogicalTime.after
          currentTime
          delay := by
  rfl

@[simp]
theorem scheduleWithPayload_payload
    (currentTime : LogicalTime)
    (messageName : MsgName)
    (payload : Payload)
    (delay : Delay) :
    (scheduleWithPayload
      currentTime
      messageName
      payload
      delay).payload =
        payload := by
  rfl

end PendingMessage

end DTR
end Relico
