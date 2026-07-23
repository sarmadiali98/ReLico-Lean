import Relico.DTR.State

set_option autoImplicit false

namespace Relico
namespace DTR
namespace Expr

/--
Evaluate a vertical-slice DTR expression.

The fragment contains one integer state variable, so evaluation receives
its current value directly. Source well-formedness guarantees that a
variable reference names the declared variable.
-/
@[simp]
def evaluate
    (stateValue : Int) :
    DTR.Expr → Int
  | DTR.Expr.intLiteral value =>
      value
  | DTR.Expr.stateVar _ =>
      stateValue

end Expr
end DTR
end Relico
