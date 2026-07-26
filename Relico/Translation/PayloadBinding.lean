import Relico.DTR.PayloadExpression
import Relico.LF.PayloadExpression
import Relico.Translation.Basic

set_option autoImplicit false

namespace Relico
namespace Translation

/--
Compile a source payload-aware expression into the corresponding
generated-LF payload-aware expression.
-/
def compilePayloadExpr :
    DTR.PayloadExpr →
    LF.PayloadExpr

  | .intLiteral value =>
      .intLiteral value

  | .stateVar variableName =>
      .stateVar variableName

  | .parameterVar parameterName =>
      .parameterVar parameterName

@[simp]
theorem compilePayloadExpr_intLiteral
    (value : Int) :
    compilePayloadExpr
        (.intLiteral value) =
      LF.PayloadExpr.intLiteral
        value := by
  rfl

@[simp]
theorem compilePayloadExpr_stateVar
    (variableName : VarName) :
    compilePayloadExpr
        (.stateVar variableName) =
      LF.PayloadExpr.stateVar
        variableName := by
  rfl

@[simp]
theorem compilePayloadExpr_parameterVar
    (parameterName : VarName) :
    compilePayloadExpr
        (.parameterVar parameterName) =
      LF.PayloadExpr.parameterVar
        parameterName := by
  rfl

/--
Payload-expression translation preserves evaluation in corresponding
persistent state and activation-local parameter environments.
-/
theorem compilePayloadExpr_preserves_evaluation
    (expression : DTR.PayloadExpr)
    (stateValue : Int)
    (parameters : ParameterStore) :
    LF.PayloadExpr.evaluate
        stateValue
        parameters
        (compilePayloadExpr
          expression) =
      DTR.PayloadExpr.evaluate
        stateValue
        parameters
        expression := by

  cases expression <;>
    rfl

/--
Embedding an existing parameterless expression commutes with
translation.
-/
theorem compilePayloadExpr_ofExpr
    (expression : DTR.Expr) :
    compilePayloadExpr
        (DTR.PayloadExpr.ofExpr
          expression) =
      LF.PayloadExpr.ofExpr
        (compileExpr
          expression) := by

  cases expression <;>
    rfl

end Translation
end Relico
