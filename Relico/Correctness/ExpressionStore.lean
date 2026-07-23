import Relico.DTR.StoreEvaluation
import Relico.LF.StoreEvaluation
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Compiling an expression preserves partial evaluation in every finite
state-variable store.

Unlike the original single-value theorem, this result already supports
references to different variable names.
-/
theorem compileExpr_preserves_store_evaluation
    (sourceExpression : DTR.Expr)
    (store : StateStore) :
    LF.Expr.evaluateStore
        store
        (Translation.compileExpr
          sourceExpression) =
      DTR.Expr.evaluateStore
        store
        sourceExpression := by

  cases sourceExpression <;> rfl

end Correctness
end Relico
