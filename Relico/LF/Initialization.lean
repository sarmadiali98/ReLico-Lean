import Relico.LF.State

set_option autoImplicit false

namespace Relico
namespace LF

/--
The initial LF tag used at startup-reaction entry.
-/
def initialTag : LF.Tag where
  time := 0
  microstep := 0

/--
The generated-LF runtime state at startup-reaction entry.

The initial integer value is shared with the corresponding DTR
constructor-entry state.
-/
def initialState
    (program : LF.Program)
    (initialValue : Int) :
    LF.State where
  currentTag := initialTag
  stateValue := initialValue
  pendingActions := []
  activeBody :=
    program.reactor.startupReaction.body

end LF
end Relico
