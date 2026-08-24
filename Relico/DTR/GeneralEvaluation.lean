import Relico.DTR.GeneralSyntax

/-!
# Evaluation for the general DTR fragment

The general family reached stage G with **no evaluator at all**. Five general modules existed on this
side — `GeneralSyntax`, `GeneralWellFormed`, `GeneralPriority`, `GeneralState`, `GeneralActorSelection`
— and not one of them says what an expression denotes. That gap is not optional for stage G, and the
reason is the shape of the result being proved rather than a preference for completeness.

`docs/STAGE_G_DESIGN.md` §7 commits stage G to the paper's Theorem 1, whose correspondence relation is

```
R = {(s,s') | ∀x ∈ AID. ∃r ∈ RID · r = map_A(x) ∧ s(x) = (e_x,b_x,π_x) ∧ s'(r) = (η_r,q_r,µ_r)
              ∧ e_x ≡ η_r ∧ b_x ≡ q_r ∧ π_x ≡ µ_r}
```

The first conjunct relates the two **valuations**. Without an evaluator nothing ever changes a
valuation, so `e_x ≡ η_r` would be preserved by every step for the empty reason that both sides are
constant — the paper's relation reproduced with a decorative conjunct. That is the defect recorded as
`docs/STAGE_G_FINDINGS.md` F66 part 5, and this module is the first half of its repair.

## One store serves state variables and message parameters

`GeneralValuation` is a single `Store VarName DTR.GeneralValue`, and `GeneralExpr.evaluate` resolves
both `.stateVar` and `.parameterVar` in it. That is the paper's own arrangement: its TAKE rule binds a
message's arguments by `e_x ∪ v⃗`, one environment holding both.

It is sound **only because of a clause proved in stage E**. `DTR.GeneralWellFormed`'s
`.parameterShadowsStateVariable` failure makes a message server whose formal parameter has the same
name as a state variable ill-formed, so for any program that passed the predicate the union cannot
collide. Remove that clause and this module becomes wrong rather than merely imprecise, which is why
the dependency is named here and not left to be rediscovered. `evaluate_stateVar_eq_parameterVar`
below pins the decision as a theorem, so a later stage that splits the two stores gets a build error
here instead of a silent change of meaning.

## Evaluation is partial, and there are exactly three causes

The signature is `Option DTR.GeneralValue`, following `DTR.Expr.evaluateStore`, whose docstring gives
the first cause. All three are worth separating, because they have different standing:

1. **An absent binding.** `Store.lookup` is partial and an arbitrary runtime store need not bind every
   name. Well-formedness resolves the names an expression *mentions*, so for a well-formed program
   reached by a real execution this cause does not arise; it is nonetheless representable, so it is
   modelled rather than assumed away.
2. **An operand-type mismatch**, such as adding a boolean to an integer. `DTR.GeneralExpr`'s own
   docstring records that "expression type-correctness is not enforced anywhere in this family" and
   that adding a typing judgement is a scoped later addition. So `.binary .add (.boolLiteral true)
   (.intLiteral 1)` is a writable term, and this module reports it as `none` rather than inventing the
   typing judgement that docstring declines to add.
3. **A zero divisor**, which is the one that is a statement about the *target*. See below.

## The operator semantics is C++'s, and that is a measurement

`LF.renderGeneralBinaryOp` emits `"/"` and `"%"` verbatim, and its docstring records why the spellings
needed no probe: every one appears "inside a `{= … =}` block where the text is verbatim C++, so the
spellings are guaranteed by the C++ standard". That same standard fixes the arithmetic. Integer
division truncates toward zero and the remainder takes the sign of the dividend, which in Lean are
`Int.tdiv` and `Int.tmod` — **not** Euclidean or flooring division. A model built on `Int.ediv` would
agree with this one on non-negative operands and disagree on `(-7) / 2`, and would then be a false
claim about what the generated program computes.

This repository contained no integer division anywhere before this module, so there was no convention
to inherit and the choice had to be made from the target rather than from precedent. Recorded as
`docs/STAGE_G_FINDINGS.md` F67.

## Division by zero: `none` means "no claim", not "computes nothing"

Division by zero is **undefined behaviour** in C++, so there is no value for a faithful model to
return and no behaviour for a faithful model to exhibit. `apply` therefore returns `none`, and the
consequence is deliberate: a step rule premised on a successful evaluation simply has no instance, so
a source configuration whose next statement divides by zero is *stuck*, and — by
`Correctness.compileGeneralExpr_preserves_evaluation` — its target counterpart is stuck in exactly the
same place. Nothing asymmetric is claimed, which is what keeps Theorem 1 true rather than vacuous.

What this does **not** do is model the real generated program, which has undefined behaviour rather
than a stuck state. The correctness result therefore transfers to real target behaviour only on
executions in which no division or modulo by zero occurs, and nothing in `DTR.GeneralWellFormed`
excludes such a program: it places no restriction on expressions at all, so `x / 0` is well-formed,
translated and printed. That is a **fragment restriction**, it is stated here at the point where it
becomes true, and stage G's obligation G6 owes its declaration alongside conditional-freedom.
`apply_div_zero` and `apply_mod_zero` pin the refusal so it cannot be relaxed silently.
-/

set_option autoImplicit false

namespace Relico
namespace DTR

/--
A valuation for one actor: the state variables and the parameters currently in scope.

This is an `abbrev` rather than a `def` on purpose. `DTR.GeneralActorState.valuation`
(`Relico/DTR/GeneralState.lean`) already has exactly this type spelled out inline, and a transparent
abbreviation names it without putting a coercion between the state layer and this one. The same
pattern is `Relico/Common/StateStore.lean`'s `abbrev StateStore := Store VarName Int`.
-/
abbrev GeneralValuation :=
  Store VarName DTR.GeneralValue

namespace GeneralBinaryOp

/--
Apply a binary operator to two values.

Thirteen operators, written out one combination at a time, with a single closing wildcard for every
operand shape that has no meaning. The wildcard is what makes the type mismatch of cause 2 above a
`none` rather than an unhandled case.

`.eq` and `.ne` accept two integers or two booleans; the ordering comparisons accept only integers;
`.logicalAnd` and `.logicalOr` accept only booleans. Mixed operands are refused rather than coerced,
because a coercion here would be this development inventing a conversion the source language does not
have.

`.div` and `.mod` use `Int.tdiv` and `Int.tmod` — truncation toward zero, remainder signed like the
dividend — because that is what the C++ the printer emits computes. A zero divisor is refused: see the
module note.
-/
def apply :
    DTR.GeneralBinaryOp →
    DTR.GeneralValue →
    DTR.GeneralValue →
    Option DTR.GeneralValue

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
Division by a zero divisor has no result.

Pinned as a theorem rather than left to the definition, because the reason for it is a property of the
target rather than of this development: C++ integer division by zero is undefined behaviour, so a
model that returned a value here would be claiming something false. A later change that made this
total would have to delete this theorem, which is the point.
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
Apply a unary operator to a value.

`.negate` is integer negation and `.logicalNot` is boolean negation; the crossed combinations are
refused by the wildcard rather than coerced.
-/
def apply :
    DTR.GeneralUnaryOp →
    DTR.GeneralValue →
    Option DTR.GeneralValue

  | .negate, .int value =>
      some (.int (-value))

  | .logicalNot, .bool value =>
      some (.bool (!value))

  | _, _ =>
      none

end GeneralUnaryOp

namespace GeneralExpr

/--
Evaluate a general DTR expression in a valuation.

Six arms matching the six constructors, two of them recursive, with totality of the *recursion* by
structural descent and no termination argument owed. Partiality of the *result* is the separate matter
described in the module note.

`.stateVar` and `.parameterVar` resolve in the same store. That is the paper's `e_x ∪ v⃗` and it is
sound because stage E's `.parameterShadowsStateVariable` clause makes a name collision between the two
ill-formed.
-/
def evaluate
    (valuation : DTR.GeneralValuation) :
    DTR.GeneralExpr →
    Option DTR.GeneralValue

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
          DTR.GeneralBinaryOp.apply
            operator
            leftValue
            rightValue

      | _, _ =>
          none

  | .unary operator operand =>
      match evaluate valuation operand with
      | some operandValue =>
          DTR.GeneralUnaryOp.apply
            operator
            operandValue

      | none =>
          none

@[simp]
theorem evaluate_intLiteral
    (valuation : DTR.GeneralValuation)
    (value : Int) :
    evaluate
        valuation
        (.intLiteral value) =
      some (.int value) := by
  rfl

@[simp]
theorem evaluate_boolLiteral
    (valuation : DTR.GeneralValuation)
    (value : Bool) :
    evaluate
        valuation
        (.boolLiteral value) =
      some (.bool value) := by
  rfl

@[simp]
theorem evaluate_stateVar
    (valuation : DTR.GeneralValuation)
    (name : VarName) :
    evaluate
        valuation
        (.stateVar name) =
      Store.lookup valuation name := by
  rfl

@[simp]
theorem evaluate_parameterVar
    (valuation : DTR.GeneralValuation)
    (name : VarName) :
    evaluate
        valuation
        (.parameterVar name) =
      Store.lookup valuation name := by
  rfl

/--
A state-variable reference and a parameter reference of the same name denote the same value.

This is the single-store decision stated as a theorem. It is true by definition today, and that is
exactly why it is worth writing down: the stage that gives message parameters their own store must
either keep this true or delete this theorem, and deleting a theorem is a visible act. Without it the
change would be a silent alteration of what every expression means.

Note what it does *not* say. It is not a claim that the two constructors are redundant — the
distinction is what lets `DTR.GeneralWellFormed` resolve a name against the right declaration list,
and `.parameterShadowsStateVariable` is what makes the two lookups agree here without ambiguity.
-/
theorem evaluate_stateVar_eq_parameterVar
    (valuation : DTR.GeneralValuation)
    (name : VarName) :
    evaluate
        valuation
        (.stateVar name) =
      evaluate
        valuation
        (.parameterVar name) := by
  rfl

/--
Evaluate an argument list left to right, failing if any argument fails.

Used for a send's actual arguments, which become the payload the receiving message server binds. The
recursion fails as a whole when any element fails, so a payload is either fully determined or absent;
there is no partially evaluated payload, which is what lets a step rule take the payload as a single
premise.

Nothing here relates the list's length to the declared parameter list of the message server being
sent. `DTR.GeneralWellFormed` does that, and the length agreement this induces is owed as a theorem by
the stage that writes the step relation, where it is first used.
-/
def evaluateArguments
    (valuation : DTR.GeneralValuation) :
    List DTR.GeneralExpr →
    Option DTR.GeneralPayload

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
    (valuation : DTR.GeneralValuation) :
    evaluateArguments
        valuation
        [] =
      some [] := by
  rfl

end GeneralExpr
end DTR
end Relico
