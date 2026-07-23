import Relico.Common.StateStore
import Relico.LF.Evaluation
import Relico.LF.WellFormed

set_option autoImplicit false

namespace Relico
namespace LF
namespace Expr

/--
Evaluate a generated LF expression in a finite state-variable store.

Evaluation is partial because an arbitrary store may omit a referenced
state variable.
-/
@[simp]
def evaluateStore
    (store : StateStore) :
    LF.Expr →
    Option Int

  | .intLiteral value =>
      some value

  | .stateVar variableName =>
      StateStore.lookup
        store
        variableName

/--
The store evaluator agrees with the original v0 evaluator on a
well-formed expression and a singleton store containing the declared
reactor state variable.
-/
theorem evaluateStore_singleton_of_wellFormed
    (declaredStateVar : VarName)
    (stateValue : Int)
    (expression : LF.Expr)
    (hWellFormed :
      expression.WellFormed
        declaredStateVar) :
    evaluateStore
        (StateStore.singleton
          declaredStateVar
          stateValue)
        expression =
      some
        (evaluate
          stateValue
          expression) := by

  cases expression with

  | intLiteral value =>
      rfl

  | stateVar referencedStateVar =>
      change
        referencedStateVar =
          declaredStateVar
        at hWellFormed

      subst referencedStateVar

      simp [
        evaluateStore,
        evaluate
      ]

end Expr
end LF
end Relico
