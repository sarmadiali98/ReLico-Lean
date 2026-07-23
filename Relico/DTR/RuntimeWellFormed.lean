import Relico.DTR.Semantics
import Relico.DTR.WellFormed

set_option autoImplicit false

namespace Relico
namespace DTR
namespace State

/--
Runtime well-formedness for a DTR state in vertical slice v0.

The active body may only refer to declarations provided by the model.
Every pending message must target the model's declared message server.
-/
structure WellFormed
    (model : DTR.Model)
    (state : DTR.State) :
    Prop where

  activeBodyWellFormed :
    state.activeBody.WellFormed
      model.reactiveClass.stateVar
      model.reactiveClass.messageServer.name

  pendingMessagesWellFormed :
    ∀ pendingMessage ∈ state.pendingMessages,
      pendingMessage.name =
        model.reactiveClass.messageServer.name

end State
end DTR
end Relico
