import Relico.Common.Store
import Relico.LF.GeneralSyntax

/-!
# Evaluation for the general LF fragment

The mirror of `Relico.DTR.GeneralEvaluation`. That module carries the reasoning — why an evaluator is
needed at all, why one store serves state variables and parameters, the three causes of partiality, and
why the operator semantics is C++'s. This note records only what is different on this side, so the two
do not drift into two half-accurate accounts of the same decision.

## `Relico.Common.Store` is imported explicitly, and that is not redundant

`Relico.LF.GeneralSyntax` imports only `Relico.LF.StoreSyntax`, which is the earlier integer-only
family's declaration layer and has no reason to reach `Store`. `VarName` arrives transitively — it must,
since `LF.GeneralExpr.stateVar` carries one — but `Store` does not, so the import above is load-bearing
rather than decorative. The DTR side needs no such line because `DTR.GeneralSyntax` already imports
`Relico.Common.Store` directly.

## This is the side where the operator semantics is a claim about a real program

`DTR.GeneralBinaryOp.apply` and the `apply` below are the same function up to the constructor names, and
the module note on the DTR side explains why they use `Int.tdiv` and `Int.tmod`. The asymmetry worth
recording is that on the DTR side those choices are a *model of the source language*, whereas here they
are a model of text that `LF.GeneralCppPrinter` actually emits into a `{= … =}` block and that a C++
compiler actually compiles. So a divergence between this function and C++ integer arithmetic would not
be a modelling infelicity; it would make the correctness result false of the artefact the tool produces.

That is also why the two `apply` functions are written out separately instead of one being defined as
the image of the other. Defining this one through `Translation.compileGeneralValue` would make
`Correctness.compileGeneralExpr_preserves_evaluation` true by construction and would prove nothing about
the target: the theorem is worth having precisely because both sides are stated independently and then
shown to agree.

## Nothing here mentions the translation

This module imports no `Translation` module and names nothing from one, which keeps the dependency
direction the repository already uses: `Relico/Correctness/ExpressionStore.lean` is the module that
imports both sides *and* `Translation.Basic`, because `Translation` sits downstream of both languages.
The general family's counterpart is `Relico/Correctness/GeneralEvaluation.lean`.
-/

set_option autoImplicit false

namespace Relico
namespace LF

/--
A valuation for one reactor: the state variables and the action or port parameters in scope.

The LF counterpart of `DTR.GeneralValuation`, with the same single-store arrangement. Note that this
side has no well-formedness clause of its own forbidding a parameter that shadows a state variable — the
guarantee is inherited, because every general LF program this development reasons about is the image of
a well-formed DTR program under `Translation.compileGeneralProgram`, and stage E's
`.parameterShadowsStateVariable` clause rejects the collision on the source. A hand-written LF term
that shadowed could still be evaluated here; nothing claims otherwise, and no theorem depends on it.
-/
abbrev GeneralValuation :=
  Store VarName LF.GeneralValue

namespace GeneralBinaryOp

/--
Apply a binary operator to two values, matching `DTR.GeneralBinaryOp.apply` arm for arm.

Thirteen operators; mixed-type operands and a zero divisor yield `none` through the closing wildcard and
the two guards. See the module note above and the one on the DTR side for why the arithmetic is C++'s.
-/
def apply :
    LF.GeneralBinaryOp →
    LF.GeneralValue →
    LF.GeneralValue →
    Option LF.GeneralValue

  | .add, .int left, .int right =>
      some (.int (left + right))

  | .sub, .int left, .int right =>
      some (.int (left - right))

  | .mul, .int left, .int right =>
      some (.int (left * right))

  | .div, .int left, .int right =>
      if right = 0 then
        none
      else
        some (.int (Int.tdiv left right))

  | .mod, .int left, .int right =>
      if right = 0 then
        none
      else
        some (.int (Int.tmod left right))

  | .eq, .int left, .int right =>
      some (.bool (left == right))

  | .eq, .bool left, .bool right =>
      some (.bool (left == right))

  | .ne, .int left, .int right =>
      some (.bool (left != right))

  | .ne, .bool left, .bool right =>
      some (.bool (left != right))

  | .lt, .int left, .int right =>
      some (.bool (decide (left < right)))

  | .le, .int left, .int right =>
      some (.bool (decide (left ≤ right)))

  | .gt, .int left, .int right =>
      some (.bool (decide (left > right)))

  | .ge, .int left, .int right =>
      some (.bool (decide (left ≥ right)))

  | .logicalAnd, .bool left, .bool right =>
      some (.bool (left && right))

  | .logicalOr, .bool left, .bool right =>
      some (.bool (left || right))

  | _, _, _ =>
      none

/--
Division by a zero divisor has no result on the target side either.

Stated separately from `DTR.GeneralBinaryOp.apply_div_zero` rather than derived from it, because the
undefined behaviour being modelled is undefined behaviour of *this* side's emitted C++. The DTR-side
theorem is a statement about the source model; this one is the statement that carries the fragment
restriction.
-/
theorem apply_div_zero
    (left : Int) :
    apply
        .div
        (.int left)
        (.int 0) =
      none := by
  simp [apply]

/--
Modulo by a zero divisor has no result, for the same reason as `apply_div_zero`.
-/
theorem apply_mod_zero
    (left : Int) :
    apply
        .mod
        (.int left)
        (.int 0) =
      none := by
  simp [apply]

end GeneralBinaryOp

namespace GeneralUnaryOp

/--
Apply a unary operator to a value, matching `DTR.GeneralUnaryOp.apply`.
-/
def apply :
    LF.GeneralUnaryOp →
    LF.GeneralValue →
    Option LF.GeneralValue

  | .negate, .int value =>
      some (.int (-value))

  | .logicalNot, .bool value =>
      some (.bool (!value))

  | _, _ =>
      none

end GeneralUnaryOp

namespace GeneralExpr

/--
Evaluate a general LF expression in a valuation.

Six arms for the six constructors, mirroring `DTR.GeneralExpr.evaluate`. `.stateVar` and
`.parameterVar` resolve in the same store; see `GeneralValuation` above for why that is inherited from
the source side rather than guaranteed here.
-/
def evaluate
    (valuation : LF.GeneralValuation) :
    LF.GeneralExpr →
    Option LF.GeneralValue

  | .intLiteral value =>
      some (.int value)

  | .boolLiteral value =>
      some (.bool value)

  | .stateVar name =>
      Store.lookup valuation name

  | .parameterVar name =>
      Store.lookup valuation name

  | .binary operator left right =>
      match
        evaluate valuation left,
        evaluate valuation right
      with
      | some leftValue, some rightValue =>
          LF.GeneralBinaryOp.apply
            operator
            leftValue
            rightValue

      | _, _ =>
          none

  | .unary operator operand =>
      match evaluate valuation operand with
      | some operandValue =>
          LF.GeneralUnaryOp.apply
            operator
            operandValue

      | none =>
          none

@[simp]
theorem evaluate_intLiteral
    (valuation : LF.GeneralValuation)
    (value : Int) :
    evaluate
        valuation
        (.intLiteral value) =
      some (.int value) := by
  rfl

@[simp]
theorem evaluate_boolLiteral
    (valuation : LF.GeneralValuation)
    (value : Bool) :
    evaluate
        valuation
        (.boolLiteral value) =
      some (.bool value) := by
  rfl

@[simp]
theorem evaluate_stateVar
    (valuation : LF.GeneralValuation)
    (name : VarName) :
    evaluate
        valuation
        (.stateVar name) =
      Store.lookup valuation name := by
  rfl

@[simp]
theorem evaluate_parameterVar
    (valuation : LF.GeneralValuation)
    (name : VarName) :
    evaluate
        valuation
        (.parameterVar name) =
      Store.lookup valuation name := by
  rfl

/--
Evaluate an argument list left to right, failing if any argument fails.

Used for the arguments of a `schedule` or a `setPort`. Both LF statements that carry expressions carry
a `List GeneralExpr`, so one function serves both — unlike the DTR side, where the only expression-list
position is a send's actual arguments.
-/
def evaluateArguments
    (valuation : LF.GeneralValuation) :
    List LF.GeneralExpr →
    Option (List LF.GeneralValue)

  | [] =>
      some []

  | argument :: rest =>
      match
        evaluate valuation argument,
        evaluateArguments valuation rest
      with
      | some value, some values =>
          some (value :: values)

      | _, _ =>
          none

@[simp]
theorem evaluateArguments_nil
    (valuation : LF.GeneralValuation) :
    evaluateArguments
        valuation
        [] =
      some [] := by
  rfl

end GeneralExpr
end LF
end Relico
