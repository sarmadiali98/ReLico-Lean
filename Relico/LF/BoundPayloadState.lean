import Relico.Common.ParameterStore
import Relico.LF.BoundPayloadSyntax
import Relico.LF.State

set_option autoImplicit false

namespace Relico
namespace LF

/--
Runtime state for parameter-aware generated-LF payload execution.

The semantic parameter environment represents values read from the
triggering typed logical action.
-/
structure BoundPayloadState where

  currentTag :
    LF.Tag

  stateValue :
    Int

  parameters :
    ParameterStore

  pendingActions :
    LF.ActionQueue

  activeBody :
    LF.BoundPayloadBody

deriving Repr, DecidableEq, BEq, Inhabited

end LF
end Relico
