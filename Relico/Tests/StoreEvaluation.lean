import Relico.Correctness.ExpressionStore
import Relico.Tests.DTRWellFormed
import Std.Tactic

set_option autoImplicit false

namespace Relico
namespace Tests

def secondStateVariableName :
    VarName :=
  ⟨"y"⟩

def twoVariableStore :
    StateStore := [
  (stateVariableName, 12),
  (secondStateVariableName, 34)
]

example :
    StateStore.lookup
        twoVariableStore
        stateVariableName =
      some 12 := by
  native_decide

example :
    StateStore.lookup
        twoVariableStore
        secondStateVariableName =
      some 34 := by
  native_decide

example :
    DTR.Expr.evaluateStore
        twoVariableStore
        (.stateVar
          secondStateVariableName) =
      some 34 := by
  native_decide

example :
    LF.Expr.evaluateStore
        twoVariableStore
        (Translation.compileExpr
          (.stateVar
            secondStateVariableName)) =
      DTR.Expr.evaluateStore
        twoVariableStore
        (.stateVar
          secondStateVariableName) := by
  exact
    Correctness.compileExpr_preserves_store_evaluation
      (.stateVar
        secondStateVariableName)
      twoVariableStore

example :
    DTR.Expr.evaluateStore
        StateStore.empty
        (.stateVar
          stateVariableName) =
      none := by
  rfl

example :
    DTR.Expr.evaluateStore
        (StateStore.singleton
          stateVariableName
          12)
        (.stateVar
          stateVariableName) =
      some
        (DTR.Expr.evaluate
          12
          (.stateVar
            stateVariableName)) := by

  exact
    DTR.Expr.evaluateStore_singleton_of_wellFormed
      stateVariableName
      12
      (.stateVar
        stateVariableName)
      rfl

example :
    LF.Expr.evaluateStore
        (StateStore.singleton
          stateVariableName
          12)
        (.stateVar
          stateVariableName) =
      some
        (LF.Expr.evaluate
          12
          (.stateVar
            stateVariableName)) := by

  exact
    LF.Expr.evaluateStore_singleton_of_wellFormed
      stateVariableName
      12
      (.stateVar
        stateVariableName)
      rfl

end Tests
end Relico
