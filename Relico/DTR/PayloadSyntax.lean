import Relico.DTR.Syntax

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Additive source-statement syntax for the first payload-bearing vertical
slice.

This type is separate from `DTR.Stmt`, so the existing parameterless
semantics and proofs remain unchanged.
-/
inductive PayloadStmt where

  /--
  Schedule a self-message carrying one integer-valued expression.
  -/
  | selfSendInt :
      MsgName →
      DTR.Expr →
      Delay →
      PayloadStmt

deriving Repr, DecidableEq, BEq, Inhabited

abbrev PayloadBody :=
  List DTR.PayloadStmt

end DTR
end Relico
