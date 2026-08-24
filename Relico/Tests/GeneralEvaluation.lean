import Relico.Correctness.GeneralEvaluation

set_option autoImplicit false

/-!
# Value-level pins for general expression evaluation

`docs/STAGE_G_DESIGN.md` §7, obligation G2a-i. `Relico/DTR/GeneralEvaluation.lean`,
`Relico/LF/GeneralEvaluation.lean` and `Relico/Correctness/GeneralEvaluation.lean` prove that the two
evaluators agree under the translation, that they fail in exactly the same cases, and that the agreement
hypothesis is satisfiable. This module pins the things those theorems are structurally unable to see.

## The theorems cannot see whether the arithmetic is right

This is the important one, and it is not a small gap. `compileGeneralExpr_preserves_evaluation` is a
*relative* statement: it says the two sides compute the same thing. Replace `Int.tdiv` with `Int.fdiv`
and `Int.tmod` with `Int.fmod` in **both** `apply` functions and every theorem in this commit still
holds, because the two sides would still agree — they would simply agree on the wrong answer. Nothing in
the three modules above would fail, and the development would then contain a false claim about what the
generated C++ computes.

The only instrument that sees the difference is a value pin at a **negative dividend**, because that is
the sole input class on which truncating and flooring division disagree. `-7 / 2` is `-3` under
truncation and `-4` under flooring; `-7 % 2` is `-1` under truncation and `1` under flooring. The four
pins below fix the truncating answers on both sides, so `docs/STAGE_G_FINDINGS.md` F67's claim — that the
operator semantics is C++'s, taken from what `LF.GeneralCppPrinter` actually emits — is checkable rather
than merely asserted in a docstring.

Note that these pins state the expected values as literals. Writing them as `Int.tdiv (-7) 2` would make
them tautologies that hold under any definition of the operator, which is exactly the failure mode
`docs/STAGE_F_FINDINGS.md` F60 records for an assertion that was invariant under the sort it was
credited with pinning.

## The theorems cannot see the refusals

`Relico/DTR/GeneralEvaluation.lean`'s module note separates three causes of a `none` result — an absent
binding, an operand-type mismatch, and a zero divisor — but only the third has theorems
(`apply_div_zero`, `apply_mod_zero`) and those are about the operator rather than about an expression.
The first two have no theorem anywhere, so a change that made a mixed-type operand coerce instead of
fail, or made an absent variable read as zero, would build green. Three pins below close that.

## The theorems cannot see argument order, and cannot see non-vacuity in use

`evaluateArguments` has no theorem relating its output to its input beyond the empty case, so nothing
fixes that arguments are evaluated left to right and returned in order, and nothing fixes that one
failing argument fails the whole list. Two pins.

Finally, `compileGeneralExpr_preserves_evaluation` takes a hypothesis, and a hypothesis no caller can
discharge would make it useless without making it false. `generalValuationAgrees_image` proves it can be
discharged in general; the last pin discharges it at a concrete store and reads a concrete value out of
the *target* side, so the theorem is exercised end to end rather than only stated.
-/

namespace Relico
namespace Tests

/-- A state variable holding a negative value, so that division rounding is observable. -/
def evaluationCounter : VarName :=
  ⟨"counter"⟩

/-- A boolean state variable, used for the mixed-operand refusal and the nested expression. -/
def evaluationFlag : VarName :=
  ⟨"flag"⟩

/-- A name deliberately absent from every store below. -/
def evaluationAbsent : VarName :=
  ⟨"absent"⟩

/--
The source valuation used by every pin in this module.

`counter` is negative on purpose: it is the only reason the division pins can distinguish truncation
from flooring.
-/
def evaluationStore : DTR.GeneralValuation :=
  [
    (evaluationCounter, DTR.GeneralValue.int (-7)),
    (evaluationFlag, DTR.GeneralValue.bool true)
  ]

/-- `counter / 2`, with `counter = -7`. -/
def evaluationTruncatingQuotient : DTR.GeneralExpr :=
  .binary
    .div
    (.stateVar evaluationCounter)
    (.intLiteral 2)

/-- `counter / 0`. Well-formed, translatable, printable, and undefined in the target. -/
def evaluationZeroDivisor : DTR.GeneralExpr :=
  .binary
    .div
    (.stateVar evaluationCounter)
    (.intLiteral 0)

/-- `flag + 1`: an operand-type mismatch the source language does not forbid. -/
def evaluationMixedOperands : DTR.GeneralExpr :=
  .binary
    .add
    (.stateVar evaluationFlag)
    (.intLiteral 1)

/--
`flag && !(counter < 0)`, where `counter` is read as a **parameter**.

Exercises nesting, a comparison, a unary operator, and the single-store arrangement in one term: the
`.parameterVar` reference resolves against a binding introduced as a state variable, which is sound
because stage E's `.parameterShadowsStateVariable` clause makes a real collision ill-formed.
-/
def evaluationNested : DTR.GeneralExpr :=
  .binary
    .logicalAnd
    (.stateVar evaluationFlag)
    (.unary
      .logicalNot
      (.binary
        .lt
        (.parameterVar evaluationCounter)
        (.intLiteral 0)))

/--
**Source-side integer division truncates toward zero.**

Fails under a flooring or Euclidean model, which would give `-4`. See the module note: this is the pin
that makes the operator semantics an absolute claim rather than a relative one.
-/
theorem evaluation_source_division_truncates_toward_zero :
    DTR.GeneralBinaryOp.apply
        .div
        (.int (-7))
        (.int 2) =
      some (.int (-3)) := by
  rfl

/--
**Source-side modulo takes the sign of the dividend.**

Fails under a flooring or Euclidean model, which would give `1`.
-/
theorem evaluation_source_modulo_takes_dividend_sign :
    DTR.GeneralBinaryOp.apply
        .mod
        (.int (-7))
        (.int 2) =
      some (.int (-1)) := by
  rfl

/--
**Target-side integer division truncates toward zero.**

The same claim on the side that matters most: this is the function modelling text that
`LF.GeneralCppPrinter` emits into a `{= … =}` block and that a C++ compiler compiles.
-/
theorem evaluation_target_division_truncates_toward_zero :
    LF.GeneralBinaryOp.apply
        .div
        (.int (-7))
        (.int 2) =
      some (.int (-3)) := by
  rfl

/--
**Target-side modulo takes the sign of the dividend.**
-/
theorem evaluation_target_modulo_takes_dividend_sign :
    LF.GeneralBinaryOp.apply
        .mod
        (.int (-7))
        (.int 2) =
      some (.int (-1)) := by
  rfl

/--
A zero divisor inside an expression makes the whole expression valueless.

`apply_div_zero` states this of the operator; this states it of an expression, which is the level at
which a step rule will premise evaluation and therefore the level at which the configuration becomes
stuck.
-/
theorem evaluation_zero_divisor_expression_has_no_value :
    DTR.GeneralExpr.evaluate
        evaluationStore
        evaluationZeroDivisor =
      none := by
  rfl

/--
A mixed-type operand is refused rather than coerced.

Cause 2 of partiality, which has no theorem in any of the three modules. A change that made `.add`
coerce a boolean to an integer would build green without this pin.
-/
theorem evaluation_mixed_operands_have_no_value :
    DTR.GeneralExpr.evaluate
        evaluationStore
        evaluationMixedOperands =
      none := by
  rfl

/--
An absent binding is refused rather than defaulted.

Cause 1 of partiality, likewise unstated by any theorem. A change that made an unbound variable read as
`0` — a plausible convenience — would build green without this pin.
-/
theorem evaluation_absent_variable_has_no_value :
    DTR.GeneralExpr.evaluate
        evaluationStore
        (.stateVar evaluationAbsent) =
      none := by
  rfl

/--
A nested expression evaluates through both operator layers and both variable constructors.

`flag && !(counter < 0)` is `true && !(-7 < 0)` is `true && !true` is `false`. Nothing in the three
modules pins that the recursion in `evaluate` descends correctly, nor that a `.parameterVar` reference
reaches a binding introduced as a state variable.
-/
theorem evaluation_nested_expression_reduces :
    DTR.GeneralExpr.evaluate
        evaluationStore
        evaluationNested =
      some (.bool false) := by
  rfl

/--
Arguments are evaluated left to right and returned in order.

`evaluateArguments` has no theorem beyond the empty case, so a reversal would build green.
-/
theorem evaluation_arguments_preserve_order :
    DTR.GeneralExpr.evaluateArguments
        evaluationStore
        [
          .intLiteral 1,
          .stateVar evaluationCounter
        ] =
      some [
        .int 1,
        .int (-7)
      ] := by
  rfl

/--
One valueless argument makes the whole list valueless.

What lets a step rule take an evaluated payload as a single premise: there is no partially evaluated
payload for a rule to have to describe.
-/
theorem evaluation_arguments_fail_as_a_whole :
    DTR.GeneralExpr.evaluateArguments
        evaluationStore
        [
          .intLiteral 1,
          .stateVar evaluationAbsent
        ] =
      none := by
  rfl

/--
**The correspondence theorem, discharged and read out on the target side.**

Takes `generalValuationAgrees_image` to satisfy the hypothesis at a concrete store, rewrites with
`compileGeneralExpr_preserves_evaluation`, and computes. So the theorem is exercised rather than only
stated, and the value it delivers on the target side is the truncating `-3` rather than a flooring `-4`.

This is the pin that would fail if the agreement hypothesis were unsatisfiable in practice: a theorem
whose premise no caller can discharge is useless without being false, and nothing that only *states* the
theorem can detect that.
-/
theorem evaluation_correspondence_delivers_the_target_value :
    LF.GeneralExpr.evaluate
        (Correctness.compileGeneralValuationImage evaluationStore)
        (Translation.compileGeneralExpr evaluationTruncatingQuotient) =
      some (.int (-3)) := by
  rw [
    Correctness.compileGeneralExpr_preserves_evaluation
      (Correctness.generalValuationAgrees_image evaluationStore)
  ]
  rfl

/--
Failure corresponds: the compiled zero-divisor expression has no value either.

The value-level face of `compileGeneralExpr_evaluation_none_iff`, and the concrete instance of the
argument that partiality does not weaken Theorem 1 — both sides are stuck at the same statement.
-/
theorem evaluation_correspondence_transports_failure :
    LF.GeneralExpr.evaluate
        (Correctness.compileGeneralValuationImage evaluationStore)
        (Translation.compileGeneralExpr evaluationZeroDivisor) =
      none := by
  rw [
    Correctness.compileGeneralExpr_preserves_evaluation
      (Correctness.generalValuationAgrees_image evaluationStore)
  ]
  rfl

end Tests
end Relico
