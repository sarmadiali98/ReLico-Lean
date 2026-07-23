import Relico.Correctness.Expression
import Relico.Tests.DTRWellFormed

set_option autoImplicit false

namespace Relico
namespace Tests

example :
    LF.Expr.evaluate
        12
        (Translation.compileExpr
          (.intLiteral 7)) =
      DTR.Expr.evaluate
        12
        (.intLiteral 7) := by
  exact
    Correctness.compileExpr_preserves_evaluation
      (.intLiteral 7)
      12

example :
    LF.Expr.evaluate
        12
        (Translation.compileExpr
          (.stateVar stateVariableName)) =
      DTR.Expr.evaluate
        12
        (.stateVar stateVariableName) := by
  exact
    Correctness.compileExpr_preserves_evaluation
      (.stateVar stateVariableName)
      12

end Tests
end Relico
