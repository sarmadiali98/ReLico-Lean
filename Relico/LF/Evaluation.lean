import Relico.LF.State

set_option autoImplicit false

namespace Relico
namespace LF
namespace Expr

/--
Evaluate an expression in the generated LF subset.

The generated fragment contains one integer reactor state variable.
-/
@[simp]
def evaluate
    (stateValue : Int) :
    LF.Expr → Int
  | LF.Expr.intLiteral value =>
      value
  | LF.Expr.stateVar _ =>
      stateValue

end Expr
end LF
end Relico
