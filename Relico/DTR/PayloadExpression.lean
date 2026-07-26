import Relico.Common.ParameterStore
import Relico.DTR.Evaluation

set_option autoImplicit false

namespace Relico
namespace DTR

/--
Expressions available in the payload-aware source fragment.

State-variable references observe persistent actor state. Parameter
references observe the activation-local environment established by
message dispatch.
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
    DTR.PayloadExpr →
    Option Int

  | .intLiteral value =>
      some value

  | .stateVar _ =>
      some stateValue

  | .parameterVar parameterName =>
      ParameterStore.lookup
        parameters
        parameterName

/--
Embed an established parameterless DTR expression into the
payload-aware expression language.
-/
def ofExpr :
    DTR.Expr →
    DTR.PayloadExpr

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
    (expression : DTR.Expr) :
    evaluate
        stateValue
        parameters
        (ofExpr expression) =
      some
        (DTR.Expr.evaluate
          stateValue
          expression) := by

  cases expression <;>
    rfl

end PayloadExpr
end DTR
end Relico
