import Relico.Common.ParameterStore
import Relico.LF.Evaluation

set_option autoImplicit false

namespace Relico
namespace LF

/--
Expressions available in the generated payload-aware LF fragment.

The semantic parameter environment mirrors the value read from the
triggering typed logical action.
-/
inductive PayloadExpr where

  | intLiteral :
      Int →
      PayloadExpr

  | stateVar :
      VarName →
      PayloadExpr

  | parameterVar :
      VarName →
      PayloadExpr

deriving Repr, DecidableEq, BEq, Inhabited

namespace PayloadExpr

def evaluate
    (stateValue : Int)
    (parameters : ParameterStore) :
    LF.PayloadExpr →
    Option Int

  | .intLiteral value =>
      some value

  | .stateVar _ =>
      some stateValue

  | .parameterVar parameterName =>
      ParameterStore.lookup
        parameters
        parameterName

def ofExpr :
    LF.Expr →
    LF.PayloadExpr

  | .intLiteral value =>
      .intLiteral value

  | .stateVar variableName =>
      .stateVar variableName

@[simp]
theorem evaluate_intLiteral
    (stateValue : Int)
    (parameters : ParameterStore)
    (value : Int) :
    evaluate
        stateValue
        parameters
        (.intLiteral value) =
      some value := by
  rfl

@[simp]
theorem evaluate_stateVar
    (stateValue : Int)
    (parameters : ParameterStore)
    (variableName : VarName) :
    evaluate
        stateValue
        parameters
        (.stateVar variableName) =
      some stateValue := by
  rfl

@[simp]
theorem evaluate_parameterVar
    (stateValue : Int)
    (parameters : ParameterStore)
    (parameterName : VarName) :
    evaluate
        stateValue
        parameters
        (.parameterVar parameterName) =
      ParameterStore.lookup
        parameters
        parameterName := by
  rfl

@[simp]
theorem evaluate_ofExpr
    (stateValue : Int)
    (parameters : ParameterStore)
    (expression : LF.Expr) :
    evaluate
        stateValue
        parameters
        (ofExpr expression) =
      some
        (LF.Expr.evaluate
          stateValue
          expression) := by

  cases expression <;>
    rfl

end PayloadExpr
end LF
end Relico
