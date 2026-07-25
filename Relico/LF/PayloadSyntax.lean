import Relico.LF.Syntax

set_option autoImplicit false

namespace Relico
namespace LF

/--
Additive generated-LF statement syntax for one integer action payload.

This type is separate from `LF.Stmt`, preserving the complete existing
void-action fragment.
-/
inductive PayloadStmt where

  /--
  Schedule a typed logical action using reactor-cpp argument order:
  payload first, delay second.
  -/
  | scheduleInt :
      ActionName →
      LF.Expr →
      Delay →
      PayloadStmt

deriving Repr, DecidableEq, BEq, Inhabited

abbrev PayloadBody :=
  List LF.PayloadStmt

end LF
end Relico
