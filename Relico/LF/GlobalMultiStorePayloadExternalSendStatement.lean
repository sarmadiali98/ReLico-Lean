import Relico.LF.GlobalMultiStorePayloadExternalSend

set_option autoImplicit false

namespace Relico
namespace LF
namespace GlobalMultiStorePayloadExternalSendStatement

/--
Generated expression-bearing target adapter metadata.

This adapter is intentionally distinct from the local LF schedule statement.
A local schedule statement has no receiver identity and only updates the
executing actor's queue.
-/
structure Statement where
  sender :
    ActorName

  knownRebec :
    KnownRebecName

  actionName :
    ActionName

  payloadExpressions :
    List LF.MultiStorePayloadExpr

  delay :
    Delay

deriving Repr, DecidableEq, BEq, Inhabited

namespace Statement

/--
Evaluate generated payload expressions in the sender-local LF stores.
-/
def evaluatePayload?
    (statement : Statement)
    (senderState : LF.MultiStorePayloadState) :
    Option Payload :=
  LF.MultiStorePayloadExpr.evaluateAll
    senderState.stateStore
    senderState.parameters
    statement.payloadExpressions

end Statement

end GlobalMultiStorePayloadExternalSendStatement
end LF
end Relico
