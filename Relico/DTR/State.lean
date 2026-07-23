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

end DTR
end Relico
