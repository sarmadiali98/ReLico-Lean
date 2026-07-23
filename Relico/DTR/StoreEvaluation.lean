import Relico.Common.StateStore
import Relico.DTR.Evaluation
import Relico.DTR.WellFormed

set_option autoImplicit false

namespace Relico
namespace DTR
namespace Expr

/--
Evaluate a DTR expression in a finite state-variable store.

Evaluation is partial because a variable reference may be absent from
an arbitrary runtime store.
-/
@[simp]
def evaluateStore
    (store : StateStore) :
    DTR.Expr →
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
state variable.
-/
theorem evaluateStore_singleton_of_wellFormed
    (declaredStateVar : VarName)
    (stateValue : Int)
    (expression : DTR.Expr)
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
end DTR
end Relico
