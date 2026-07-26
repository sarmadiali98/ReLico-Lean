import Relico.DTR.PayloadExpression

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Parameter-aware source statements for the additive payload-dispatch
fragment.

Payload expressions may reference persistent actor state or the
activation-local parameter environment established by dispatch.
-/
inductive BoundPayloadStmt where

  | selfSendInt :
      MsgName →
      DTR.PayloadExpr →
      Delay →
      BoundPayloadStmt

deriving Repr, DecidableEq, BEq, Inhabited

abbrev BoundPayloadBody :=
  List DTR.BoundPayloadStmt

/--
A payload-aware message-server declaration.

Formal parameters are ordered. Dispatch binds an occurrence payload to
this list positionally.
-/
structure PayloadMessageServer where

  name :
    MsgName

  parameters :
    List VarName

  body :
    DTR.BoundPayloadBody

  priority :
    Option Nat :=
      none

deriving Repr, DecidableEq, BEq, Inhabited

end DTR
end Relico
