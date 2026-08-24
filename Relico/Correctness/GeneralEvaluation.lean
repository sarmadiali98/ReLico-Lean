import Relico.DTR.GeneralEvaluation
import Relico.LF.GeneralEvaluation
import Relico.Translation.GeneralBasic

/-!
# Expression evaluation is preserved by the general translation

This is the cross-language half of stage G's obligation G2a-i, and it is the first theorem anywhere in
this repository about `Translation.compileGeneralExpr`. That function has been committed since stage C
and has carried **no** stated property until now: the general family's expression compiler was exercised
by printer fixtures and by well-formedness, never by a semantic claim. So this module is new work rather
than a restatement, which is the whole reason G2a-i is a commit of its own.

The module lives under `Correctness/` and not under `DTR/` or `LF/` because it is the first point at
which a `Translation` module may be mentioned. `Translation.compileGeneralExpr` is defined in
`Relico/Translation/GeneralBasic.lean`, which imports both languages; a lemma about it therefore cannot
live in either language's own module without inverting the dependency. The precedent is exact:
`Relico/Correctness/ExpressionStore.lean` imports `DTR.StoreEvaluation`, `LF.StoreEvaluation` and
`Translation.Basic` for the integer-only family and proves the same shape of result there.

## Why the hypothesis is agreement rather than an image

The obvious statement would fix the target valuation to be the literal image of the source one, as
`ExpressionStore.lean` does — it quantifies over a single `StateStore` shared by both sides, which it can
because that family has one value type. Here the two valuations have different types, so the choice is
real, and this module takes an *agreement hypothesis* instead:

```
GeneralValuationAgrees source target :=
  ∀ name, Store.lookup target name = (Store.lookup source name).map Translation.compileGeneralValue
```

Three reasons, in order of weight. First, it is strictly more general: any target valuation built as the
pointwise image of the source satisfies it, and so does any target valuation that merely *agrees* on
lookups while differing in shadowed entries or in the order of bindings — and `Store` is an association
list, so two stores that agree on every lookup genuinely need not be equal. Second, it is the form the
next obligation needs: G2b's `R` relates whole configurations by the paper's `e_x ≡ η_r`, which is an
agreement between two independently evolving valuations rather than an assertion that one was computed
from the other. Third, it avoids adding a `compileGeneralValuation` function to
`Relico/Translation/GeneralBasic.lean`, a module stage C already committed — the weaker hypothesis buys
the same theorem without touching landed translation code.

## What the `none` cases mean, and why that is the point

`compileGeneralExpr_preserves_evaluation` is an equation between two `Option`s, so it says as much about
failure as about success: it forces the two sides to fail *together*, and
`compileGeneralExpr_evaluation_none_iff` states that consequence directly.

That corollary is what makes the partiality of both evaluators harmless to Theorem 1. The step relations
of obligation G2a-iii will premise a successful evaluation, so where evaluation is `none` no transition
exists and the configuration is stuck. Because failure corresponds exactly, a stuck source
configuration has a stuck target counterpart and neither side can move — so there is no execution on one
side to be matched by a missing execution on the other, and the rules acquire no propagation case for
failure. `docs/STAGE_G_DESIGN.md` §14 item 8 raised the worry that partiality would weaken the theorem;
this corollary is the answer, and it is an answer by proof rather than by assumption.

What the corollary does **not** do is make a divide-by-zero program correct with respect to the real
generated code. Both sides being stuck models both sides having no defined result, whereas the emitted
C++ has undefined behaviour rather than a stuck state. That gap is the fragment restriction recorded in
`Relico/DTR/GeneralEvaluation.lean`'s module note and in `docs/STAGE_G_FINDINGS.md` F67, and obligation
G6 owes its declaration.
-/

set_option autoImplicit false

namespace Relico
namespace Correctness

/--
Two valuations agree when every name resolves on the target side to the compiled image of what it
resolves to on the source side — including resolving to nothing in exactly the same cases.

Stated as a `∀` over names rather than as an equation between stores on purpose: `Store` is an ordered
association list, so distinct stores can agree on every lookup, and it is the lookups that expression
evaluation observes. See the module note for why this is preferred to requiring an image.
-/
def GeneralValuationAgrees
    (source : DTR.GeneralValuation)
    (target : LF.GeneralValuation) :
    Prop :=
  ∀ name : VarName,
    Store.lookup target name =
      (Store.lookup source name).map
        Translation.compileGeneralValue

/--
The pointwise image of a source valuation: every binding's value compiled, every name kept.

Defined here rather than in `Relico/Translation/GeneralBasic.lean` because it is an artefact of this
proof rather than a part of the translation. The translation never builds a valuation — valuations are
runtime objects — so putting this in `Translation` would suggest the compiler emits something it does
not.
-/
def compileGeneralValuationImage
    (source : DTR.GeneralValuation) :
    LF.GeneralValuation :=
  source.map
    (fun binding =>
      (binding.1, Translation.compileGeneralValue binding.2))

/--
The empty valuations agree.

Trivial, and worth stating anyway: together with `generalValuationAgrees_image` it establishes that
`GeneralValuationAgrees` is **satisfiable**, so the theorems taking it as a hypothesis are not vacuous.
That is not a hypothetical concern in this development. `docs/STAGE_G_FINDINGS.md` F66 part 5 is a
finding about a conjunct of the paper's own correspondence relation being trivially true, so a stage-G
module that took an unsatisfiable hypothesis and proved everything about it would be repeating the
defect it was written to repair, and would build green while doing so.
-/
theorem generalValuationAgrees_empty :
    GeneralValuationAgrees [] [] := by
  intro name
  rfl

/--
Every source valuation agrees with its pointwise image.

The witness that makes the hypothesis of the theorems below inhabited for an arbitrary store, not just
for the empty one. It is also the form a caller will actually have: a target valuation constructed from
a source valuation by compiling the values in place.

It is stated as an existence-style witness rather than folded into the theorems as a definition,
because the theorems deliberately take the weaker agreement hypothesis — see the module note. A caller
that happens to hold a literal image uses this lemma; a caller relating two independently evolving
valuations, as obligation G2b's `R` will, uses agreement directly.
-/
theorem generalValuationAgrees_image
    (source : DTR.GeneralValuation) :
    GeneralValuationAgrees
      source
      (compileGeneralValuationImage source) := by
  intro name
  induction source with

  | nil =>
      rfl

  | cons binding rest inductionHypothesis =>
      obtain ⟨candidate, value⟩ := binding
      by_cases hName : candidate = name

      · subst hName
        simp [
          compileGeneralValuationImage,
          Store.lookup
        ]

      · simp only [
          compileGeneralValuationImage,
          List.map_cons,
          Store.lookup,
          if_neg hName
        ]
        exact inductionHypothesis

/--
Applying a compiled binary operator to compiled operands agrees with compiling the result.

Proved by explicit case analysis rather than by a single `cases … <;> rfl`, because `.div` and `.mod`
guard on a zero divisor and the two sides of the equation put the guard in different positions: the
source side computes an `Option` and then maps, the target side maps first and then computes. Pushing
`Option.map` through an `if` is what `apply_ite` would do, and this repository has no Mathlib — the
`lakefile.toml` declares one library and the manifest lists no dependencies — so the divisor case is
split by hand with `by_cases` instead. The other eleven operators need no such treatment because neither
side branches.
-/
theorem compileGeneralBinaryOp_apply
    (operator : DTR.GeneralBinaryOp)
    (leftValue rightValue : DTR.GeneralValue) :
    LF.GeneralBinaryOp.apply
        (Translation.compileGeneralBinaryOp operator)
        (Translation.compileGeneralValue leftValue)
        (Translation.compileGeneralValue rightValue) =
      (DTR.GeneralBinaryOp.apply
          operator
          leftValue
          rightValue).map
        Translation.compileGeneralValue := by

  cases operator with

  | add =>
      cases leftValue <;> cases rightValue <;> rfl

  | sub =>
      cases leftValue <;> cases rightValue <;> rfl

  | mul =>
      cases leftValue <;> cases rightValue <;> rfl

  | div =>
      cases leftValue with
      | int left =>
          cases rightValue with
          | int right =>
              by_cases hZero : right = 0
              · simp [
                  DTR.GeneralBinaryOp.apply,
                  LF.GeneralBinaryOp.apply,
                  Translation.compileGeneralBinaryOp,
                  Translation.compileGeneralValue,
                  hZero
                ]
              · simp [
                  DTR.GeneralBinaryOp.apply,
                  LF.GeneralBinaryOp.apply,
                  Translation.compileGeneralBinaryOp,
                  Translation.compileGeneralValue,
                  hZero
                ]
          | bool _right =>
              rfl
      | bool _left =>
          cases rightValue <;> rfl

  | mod =>
      cases leftValue with
      | int left =>
          cases rightValue with
          | int right =>
              by_cases hZero : right = 0
              · simp [
                  DTR.GeneralBinaryOp.apply,
                  LF.GeneralBinaryOp.apply,
                  Translation.compileGeneralBinaryOp,
                  Translation.compileGeneralValue,
                  hZero
                ]
              · simp [
                  DTR.GeneralBinaryOp.apply,
                  LF.GeneralBinaryOp.apply,
                  Translation.compileGeneralBinaryOp,
                  Translation.compileGeneralValue,
                  hZero
                ]
          | bool _right =>
              rfl
      | bool _left =>
          cases rightValue <;> rfl

  | eq =>
      cases leftValue <;> cases rightValue <;> rfl

  | ne =>
      cases leftValue <;> cases rightValue <;> rfl

  | lt =>
      cases leftValue <;> cases rightValue <;> rfl

  | le =>
      cases leftValue <;> cases rightValue <;> rfl

  | gt =>
      cases leftValue <;> cases rightValue <;> rfl

  | ge =>
      cases leftValue <;> cases rightValue <;> rfl

  | logicalAnd =>
      cases leftValue <;> cases rightValue <;> rfl

  | logicalOr =>
      cases leftValue <;> cases rightValue <;> rfl

/--
Applying a compiled unary operator to a compiled operand agrees with compiling the result.

Four combinations, none of them guarded, so the whole thing reduces.
-/
theorem compileGeneralUnaryOp_apply
    (operator : DTR.GeneralUnaryOp)
    (operandValue : DTR.GeneralValue) :
    LF.GeneralUnaryOp.apply
        (Translation.compileGeneralUnaryOp operator)
        (Translation.compileGeneralValue operandValue) =
      (DTR.GeneralUnaryOp.apply
          operator
          operandValue).map
        Translation.compileGeneralValue := by
  cases operator <;> cases operandValue <;> rfl

/--
**Compiling an expression preserves its evaluation, in agreeing valuations.**

The payoff of obligation G2a-i. Structural induction on the source expression: the two literal arms
reduce, the two variable arms are exactly the agreement hypothesis instantiated at the referenced name,
and the two compound arms rewrite by the inductive hypotheses and then finish with the operator lemmas
above.

Note that the two variable arms are discharged by the *same* term, `hAgrees name`. That is the
single-store decision showing up in the proof: `.stateVar` and `.parameterVar` resolve in one store on
each side, so one agreement hypothesis covers both. `DTR.GeneralExpr.evaluate_stateVar_eq_parameterVar`
pins the same fact on the source side alone.
-/
theorem compileGeneralExpr_preserves_evaluation
    {sourceValuation : DTR.GeneralValuation}
    {targetValuation : LF.GeneralValuation}
    (hAgrees :
      GeneralValuationAgrees
        sourceValuation
        targetValuation)
    (expression : DTR.GeneralExpr) :
    LF.GeneralExpr.evaluate
        targetValuation
        (Translation.compileGeneralExpr expression) =
      (DTR.GeneralExpr.evaluate
          sourceValuation
          expression).map
        Translation.compileGeneralValue := by

  induction expression with

  | intLiteral _value =>
      rfl

  | boolLiteral _value =>
      rfl

  | stateVar name =>
      simp only [
        Translation.compileGeneralExpr,
        DTR.GeneralExpr.evaluate,
        LF.GeneralExpr.evaluate
      ]
      exact hAgrees name

  | parameterVar name =>
      simp only [
        Translation.compileGeneralExpr,
        DTR.GeneralExpr.evaluate,
        LF.GeneralExpr.evaluate
      ]
      exact hAgrees name

  | binary operator left right leftHypothesis rightHypothesis =>
      simp only [
        Translation.compileGeneralExpr,
        DTR.GeneralExpr.evaluate,
        LF.GeneralExpr.evaluate,
        leftHypothesis,
        rightHypothesis
      ]
      cases DTR.GeneralExpr.evaluate sourceValuation left with
      | none =>
          rfl
      | some leftValue =>
          cases DTR.GeneralExpr.evaluate sourceValuation right with
          | none =>
              rfl
          | some rightValue =>
              exact
                compileGeneralBinaryOp_apply
                  operator
                  leftValue
                  rightValue

  | unary operator operand operandHypothesis =>
      simp only [
        Translation.compileGeneralExpr,
        DTR.GeneralExpr.evaluate,
        LF.GeneralExpr.evaluate,
        operandHypothesis
      ]
      cases DTR.GeneralExpr.evaluate sourceValuation operand with
      | none =>
          rfl
      | some operandValue =>
          exact
            compileGeneralUnaryOp_apply
              operator
              operandValue

/--
The two evaluators fail in exactly the same cases.

A corollary of the theorem above, but the one that carries the argument of `docs/STAGE_G_DESIGN.md` §14
item 8: partiality does not weaken Theorem 1, because a source expression that has no value is compiled
to a target expression that has no value, so the step rules premised on successful evaluation have no
instance on either side and the two configurations are stuck together. See the module note.
-/
theorem compileGeneralExpr_evaluation_none_iff
    {sourceValuation : DTR.GeneralValuation}
    {targetValuation : LF.GeneralValuation}
    (hAgrees :
      GeneralValuationAgrees
        sourceValuation
        targetValuation)
    (expression : DTR.GeneralExpr) :
    LF.GeneralExpr.evaluate
        targetValuation
        (Translation.compileGeneralExpr expression) = none ↔
      DTR.GeneralExpr.evaluate
          sourceValuation
          expression = none := by
  rw [compileGeneralExpr_preserves_evaluation hAgrees expression]
  cases DTR.GeneralExpr.evaluate sourceValuation expression with
  | none =>
      simp
  | some _value =>
      simp

/--
Compiling an argument list preserves its evaluation, elementwise.

Needed by the send and schedule rules of obligation G2a-iii, and proved here rather than there because
it is the same induction as its sibling above and belongs beside it. The source side produces a
`DTR.GeneralPayload`, which is `List DTR.GeneralValue`; the target side produces a plain
`List LF.GeneralValue`, there being no LF payload alias in this family.

The list is evaluated as a whole or not at all, so this equation also transports the failure case: an
argument list one of whose elements has no value compiles to an argument list with no value.
-/
theorem compileGeneralExpr_preserves_evaluateArguments
    {sourceValuation : DTR.GeneralValuation}
    {targetValuation : LF.GeneralValuation}
    (hAgrees :
      GeneralValuationAgrees
        sourceValuation
        targetValuation)
    (arguments : List DTR.GeneralExpr) :
    LF.GeneralExpr.evaluateArguments
        targetValuation
        (arguments.map Translation.compileGeneralExpr) =
      (DTR.GeneralExpr.evaluateArguments
          sourceValuation
          arguments).map
        (List.map Translation.compileGeneralValue) := by

  induction arguments with

  | nil =>
      rfl

  | cons argument rest inductionHypothesis =>
      simp only [
        List.map_cons,
        DTR.GeneralExpr.evaluateArguments,
        LF.GeneralExpr.evaluateArguments,
        compileGeneralExpr_preserves_evaluation hAgrees,
        inductionHypothesis
      ]
      cases DTR.GeneralExpr.evaluate sourceValuation argument with
      | none =>
          rfl
      | some _value =>
          cases
            DTR.GeneralExpr.evaluateArguments
              sourceValuation
              rest
          with
          | none =>
              rfl
          | some _values =>
              rfl

end Correctness
end Relico
