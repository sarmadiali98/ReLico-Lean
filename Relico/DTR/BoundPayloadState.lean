import Relico.Common.ParameterStore
import Relico.DTR.BoundPayloadSyntax
import Relico.DTR.State

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Runtime state for parameter-aware source payload execution.

Persistent actor state and activation-local parameters remain separate.
The parameter environment is replaced when a new payload-bearing message
is dispatched.
-/
structure BoundPayloadState where

  currentTime :
    LogicalTime

  stateValue :
    Int

  parameters :
    ParameterStore

  pendingMessages :
    DTR.MessageBag

  activeBody :
    DTR.BoundPayloadBody

deriving Repr, DecidableEq, BEq, Inhabited

end DTR
end Relico
