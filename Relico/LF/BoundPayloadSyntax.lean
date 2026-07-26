import Relico.LF.PayloadExpression

set_option autoImplicit false

namespace Relico
namespace LF

/--
Parameter-aware generated-LF statements for the additive payload
fragment.
-/
inductive BoundPayloadStmt where

  | scheduleInt :
      ActionName →
      LF.PayloadExpr →
      Delay →
      BoundPayloadStmt

deriving Repr, DecidableEq, BEq, Inhabited

abbrev BoundPayloadBody :=
  List LF.BoundPayloadStmt

/--
A generated payload-reaction declaration.

The semantic parameter list mirrors the source formal-parameter list.
At backend integration, these values are obtained from the triggering
typed logical action.
-/
structure PayloadReaction where

  logicalAction :
    ActionName

  parameters :
    List VarName

  body :
    LF.BoundPayloadBody

  priority :
    Option Nat :=
      none

deriving Repr, DecidableEq, BEq, Inhabited

end LF
end Relico
