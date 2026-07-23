import Relico.DTR.Evaluation
import Relico.LF.Evaluation
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compiling an expression preserves its integer evaluation.

This theorem refers directly to the executable `compileExpr` function.
-/
theorem compileExpr_preserves_evaluation
    (sourceExpression : DTR.Expr)
    (stateValue : Int) :
    LF.Expr.evaluate
        stateValue
        (Translation.compileExpr sourceExpression) =
      DTR.Expr.evaluate
        stateValue
        sourceExpression := by
  cases sourceExpression <;> rfl

end Correctness
end Relico
